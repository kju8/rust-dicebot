extern crate rand;
use rand::Rng;
use std::convert::TryInto;
use std::fmt::{Debug, Error, Formatter};

pub const NULL_NODE: Node = Node::Null;

pub const MAX_DICE_NUM: i32 = 256;
pub const MAX_DICE_FACE: i32 = 10000;

pub const MINIMUM_MODE: OmissionMode = OmissionMode::Min;
pub const MAXIMUM_MODE: OmissionMode = OmissionMode::Max;

fn repeat(l: &Box<Node>, r: DiceList, mode: OmissionMode) -> DiceList {
  if r.calc() <= 0 {
    return DiceList {
      diceList: Some(vec![]),
      calcMode: CalcMode::Sum,
    };
  }
  let mut count = 0;
  let mut new_dice: Vec<i32> = vec![];
  while count < r.calc() {
    count = count + 1;
    new_dice.append(&mut l._calc(mode).diceList.unwrap());
  }
  DiceList {
    diceList: Some(new_dice),
    calcMode: CalcMode::Sum,
  }
}

fn repeat_once(l: &Box<Node>, r: &Box<Node>, mode: OmissionMode) -> Node {
  if r.depth() > 2 {
    return Node::Repeat(Box::new(l._clone()), Box::new(r._calc_once(mode)));
  }
  match l.depth() {
    0 | 1 => Node::List(Box::new(repeat(l, r._calc(mode), mode))),
    _ => {
      let k = r._calc(mode).calc();
      let mut as_roll: Vec<Node> = Vec::new();
      for _i in 0..(k + 1) {
        as_roll.push(l._calc_once(mode));
      }
      Node::Merge(as_roll)
    }
  }
}

#[derive(Copy, Clone)]
pub enum OmissionMode {
  Min,
  Max,
}

pub enum Node {
  Null,
  List(Box<DiceList>),
  Number(u16),

  Op(Box<Node>, OpCode, Box<Node>),
  Unary(UnaryCode, Box<Node>),

  Eqr(Box<Node>, EqrCode, Box<Node>),
  Eqr3(Box<Node>, EqrCode, Box<Node>, Eqr3Code, Box<Node>),

  Dice(Box<Node>, DiceCode, Box<Node>),
  Dice3(Box<Node>, DiceCode, Box<Node>, Dice3Code, Box<Node>),

  Sum(Box<Node>),
  Count(Box<Node>),
  Repeat(Box<Node>, Box<Node>),
  Merge(Vec<Node>),
}
impl Debug for Node {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match self {
      Node::Null => write!(fmt, "()"),
      Node::List(t) => write!(fmt, "{:?}", t),
      Node::Number(n) => write!(fmt, "{:?}", n),

      Node::Op(ref l, op, ref r) => write!(fmt, "({:?} {:?} {:?})", l, op, r),
      Node::Unary(op, ref r) => write!(fmt, "({:?} {:?})", op, r),

      Node::Eqr(ref l, op, ref r) => write!(fmt, "({:?} {:?} {:?})", l, op, r),
      Node::Eqr3(ref l, op, ref c, op2, ref r) => {
        write!(fmt, "({:?} {:?} {:?} {:?} {:?})", l, op, c, op2, r)
      }

      Node::Dice(ref l, op, ref r) => write!(fmt, "({:?} {:?} {:?})", l, op, r),
      Node::Dice3(ref l, op, ref c, op2, ref r) => {
        write!(fmt, "({:?} {:?} {:?} {:?} {:?})", l, op, c, op2, r)
      }

      Node::Sum(ref t) => write!(fmt, "Sum [{:?}]", t),
      Node::Count(ref t) => write!(fmt, "Count [{:?}]", t),
      Node::Repeat(ref t, ref n) => write!(fmt, "Repeat [{:?}, {:?}]", t, n),
      Node::Merge(v) => write!(fmt, "Merge [{:?}]", v),
    }
  }
}
impl Node {
  fn _clone(&self) -> Node {
    match self {
      Node::Null => Node::Null,
      Node::List(t) => Node::List(Box::new(DiceList {
        diceList: Some(t.diceList.as_ref().unwrap().to_vec()),
        calcMode: t.calcMode,
      })),
      Node::Number(t) => Node::Number(*t),

      Node::Op(l, op, r) => {
        Node::Op(Box::new(l._clone()), *op, Box::new(r._clone()))
      }
      Node::Unary(op, r) => Node::Unary(*op, Box::new(r._clone())),

      Node::Eqr(l, op, r) => {
        Node::Eqr(Box::new(l._clone()), *op, Box::new(r._clone()))
      }
      Node::Eqr3(l, op, c, op2, r) => Node::Eqr3(
        Box::new(l._clone()),
        *op,
        Box::new(c._clone()),
        *op2,
        Box::new(r._clone()),
      ),

      Node::Dice(l, op, r) => {
        Node::Dice(Box::new(l._clone()), *op, Box::new(r._clone()))
      }
      Node::Dice3(l, op, c, op2, r) => Node::Dice3(
        Box::new(l._clone()),
        *op,
        Box::new(c._clone()),
        *op2,
        Box::new(r._clone()),
      ),

      Node::Sum(arg) => Node::Sum(Box::new(arg._clone())),
      Node::Count(arg) => Node::Count(Box::new(arg._clone())),
      Node::Repeat(arg1, arg2) => {
        Node::Repeat(Box::new(arg1._clone()), Box::new(arg2._clone()))
      }
      Node::Merge(arg) => {
        let mut as_roll: Vec<Node> = Vec::new();
        for v in arg {
          as_roll.push(v._clone());
        }
        Node::Merge(as_roll)
      }
    }
  }

  pub fn depth(&self) -> i32 {
    match self {
      Node::Null => 0,
      Node::List(_) => 0,
      Node::Number(_) => 0,

      Node::Op(l, _op, r) => std::cmp::max(l.depth(), r.depth()) + 1,
      Node::Unary(_op, r) => r.depth() + 1,

      Node::Eqr(l, _op, r) => std::cmp::max(l.depth(), r.depth()) + 1,
      Node::Eqr3(l, _op, c, _op2, r) => {
        std::cmp::max(l.depth(), std::cmp::max(c.depth(), r.depth())) + 1
      }

      Node::Dice(l, _op, r) => std::cmp::max(l.depth(), r.depth()) + 1,
      Node::Dice3(l, _op, c, _op2, r) => {
        std::cmp::max(l.depth(), std::cmp::max(c.depth(), r.depth())) + 1
      }

      Node::Sum(arg) => arg.depth() + 1,
      Node::Count(arg) => arg.depth() + 1,
      Node::Repeat(arg1, arg2) => std::cmp::max(arg1.depth(), arg2.depth()) + 1,
      Node::Merge(arg) => arg.iter().map(|v| v.depth()).max().unwrap() + 1,
    }
  }
  fn _calc(&self, mode: OmissionMode) -> DiceList {
    match self {
      Node::Null => DiceList {
        diceList: None,
        calcMode: CalcMode::Sum,
      },
      Node::List(l) => DiceList {
        diceList: Some((*l).diceList.as_ref().unwrap().to_vec()),
        calcMode: l.calcMode,
      },
      Node::Number(n) => DiceList {
        diceList: Some(vec![*n as i32]),
        calcMode: CalcMode::Sum,
      },

      Node::Op(l, op, r) => op.calc(l._calc(mode), r._calc(mode)),
      Node::Unary(op, r) => op.calc(r._calc(mode)),

      Node::Eqr(l, op, r) => op.checkDice(l._calc(mode), r._calc(mode)),
      Node::Eqr3(l, op, c, op2, r) => {
        op2.filter(l._calc(MAXIMUM_MODE), c._calc(mode), r._calc(mode), *op)
      }

      Node::Dice(l, op, r) => op.roll(l._calc(mode), r._calc(mode), mode),
      Node::Dice3(l, op, c, op2, r) => {
        op2.roll(l._calc(mode), c._calc(mode), r._calc(mode), *op, mode)
      }

      Node::Sum(arg) => arg._calc(mode).sum(),
      Node::Count(arg) => arg._calc(mode).count(),
      Node::Repeat(arg1, arg2) => repeat(arg1, arg2._calc(mode), mode),
      Node::Merge(arg) => {
        let mut as_roll: Vec<i32> = Vec::new();
        for v in arg {
          if let Some(t) = v._calc(mode).diceList {
            for v2 in t {
              as_roll.push(v2);
            }
          }
        }
        DiceList {
          diceList: Some(as_roll),
          calcMode: CalcMode::Sum,
        }
      }
    }
  }
  fn _calc_once(&self, mode: OmissionMode) -> Node {
    match self.depth() {
      0 => self._clone(),
      1 => Node::List(Box::new(self._calc(mode))),
      _ => match self {
        Node::Op(l, op, r) => Node::Op(
          Box::new(l._calc_once(mode)),
          *op,
          Box::new(r._calc_once(mode)),
        ),
        Node::Unary(op, r) => Node::Unary(*op, Box::new(r._calc_once(mode))),

        Node::Eqr(l, op, r) => Node::Eqr(
          Box::new(l._calc_once(mode)),
          *op,
          Box::new(r._calc_once(mode)),
        ),
        Node::Eqr3(l, op, c, op2, r) => op2.filter_once(l, c, r, *op, mode),

        Node::Dice(l, op, r) => Node::Dice(
          Box::new(l._calc_once(mode)),
          *op,
          Box::new(r._calc_once(mode)),
        ),
        Node::Dice3(l, op, c, op2, r) => Node::Dice3(
          Box::new(l._calc_once(mode)),
          *op,
          Box::new(c._calc_once(mode)),
          *op2,
          Box::new(r._calc_once(mode)),
        ),

        Node::Sum(arg) => Node::Sum(Box::new(arg._calc_once(mode))),
        Node::Count(arg) => Node::Count(Box::new(arg._calc_once(mode))),
        Node::Repeat(arg1, arg2) => repeat_once(arg1, arg2, mode),
        Node::Merge(arg) => {
          let mut as_roll: Vec<Node> = Vec::new();
          for v in arg {
            as_roll.push(v._calc_once(mode));
          }
          Node::Merge(as_roll)
        }

        _ => Node::Null,
      },
    }
  }
  pub fn calc(&self) -> i32 {
    self._calc(MINIMUM_MODE).calc()
  }
  pub fn calc_once(&self) -> Node {
    self._calc_once(MINIMUM_MODE)
  }
}

#[derive(Copy, Clone)]
pub enum OpCode {
  // 2項演算子
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  Pow,
}
impl Debug for OpCode {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match *self {
      OpCode::Add => write!(fmt, "+"),
      OpCode::Sub => write!(fmt, "-"),
      OpCode::Mul => write!(fmt, "*"),
      OpCode::Div => write!(fmt, "/"),
      OpCode::Mod => write!(fmt, "%"),
      OpCode::Pow => write!(fmt, "^"),
    }
  }
}
impl OpCode {
  fn calc(&self, l: DiceList, r: DiceList) -> DiceList {
    match self {
      OpCode::Add => DiceList {
        diceList: Some(vec![l.calc() + r.calc()]),
        calcMode: CalcMode::Sum,
      },
      OpCode::Sub => DiceList {
        diceList: Some(vec![l.calc() - r.calc()]),
        calcMode: CalcMode::Sum,
      },
      OpCode::Mul => DiceList {
        diceList: Some(vec![l.calc() * r.calc()]),
        calcMode: CalcMode::Sum,
      },
      OpCode::Div => DiceList {
        diceList: Some(vec![l.calc() / r.calc()]),
        calcMode: CalcMode::Sum,
      },
      OpCode::Mod => DiceList {
        diceList: Some(vec![l.calc() % r.calc()]),
        calcMode: CalcMode::Sum,
      },
      OpCode::Pow => DiceList {
        diceList: Some(vec![l.calc().pow(r.calc().try_into().unwrap())]),
        calcMode: CalcMode::Sum,
      },
    }
  }
}

#[derive(Copy, Clone)]
pub enum UnaryCode {
  // 単項演算子
  Minus,
}
impl Debug for UnaryCode {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match *self {
      UnaryCode::Minus => write!(fmt, "-"),
    }
  }
}
impl UnaryCode {
  fn calc(&self, r: DiceList) -> DiceList {
    match self {
      UnaryCode::Minus => DiceList {
        diceList: Some(vec![-r.calc()]),
        calcMode: CalcMode::Sum,
      },
    }
  }
}

#[derive(Copy, Clone)]
pub enum EqrCode {
  // 比較演算子
  Eqr,
  Grt,
  Sml,
  NEq,
  GEq,
  SEq,
}
impl Debug for EqrCode {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match *self {
      EqrCode::Eqr => write!(fmt, "="),
      EqrCode::Grt => write!(fmt, ">"),
      EqrCode::Sml => write!(fmt, "<"),
      EqrCode::NEq => write!(fmt, "!="),
      EqrCode::GEq => write!(fmt, ">="),
      EqrCode::SEq => write!(fmt, "<="),
    }
  }
}
impl EqrCode {
  fn reverse(&self) -> EqrCode {
    match self {
      EqrCode::Grt => EqrCode::Sml,
      EqrCode::Sml => EqrCode::Eqr,
      EqrCode::GEq => EqrCode::GEq,
      EqrCode::SEq => EqrCode::SEq,
      _ => *self,
    }
  }

  pub fn check(&self, l: i32, r: i32) -> bool {
    match self {
      EqrCode::Eqr => l == r,
      EqrCode::Grt => l > r,
      EqrCode::Sml => l < r,
      EqrCode::NEq => l != r,
      EqrCode::GEq => l >= r,
      EqrCode::SEq => l <= r,
    }
  }

  fn checkNum(&self, l: &DiceList, r: i32) -> DiceList {
    DiceList {
      diceList: Some(
        l.diceList
          .as_ref()
          .unwrap()
          .iter()
          .cloned()
          .filter(|&x| self.check(x, r))
          .collect(),
      ),
      calcMode: CalcMode::Count,
    }
  }

  pub fn checkDice(&self, l: DiceList, r: DiceList) -> DiceList {
    if let None = l.diceList {
      return r;
    }
    if let None = r.diceList {
      return l;
    }

    let rc = r.calc();

    match r.diceList.as_ref().unwrap().len() {
      0 => l,
      1 => self.checkNum(&l, rc),
      _ => match &l.diceList.as_ref().unwrap().len() {
        0 => DiceList {
          diceList: Some(r.diceList.unwrap()),
          calcMode: r.calcMode,
        },
        1 => self.reverse().checkDice(r, l),
        _ => self.checkNum(&l, rc),
      },
    }
  }
}

#[derive(Copy, Clone)]
pub enum Eqr3Code {
  // 三項比較演算子
  Suc,
  Fail,
}
impl Debug for Eqr3Code {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match *self {
      Eqr3Code::Suc => write!(fmt, "Success"),
      Eqr3Code::Fail => write!(fmt, "Failed"),
    }
  }
}
impl Eqr3Code {
  fn countMode(&self, b: bool) -> bool {
    match self {
      Eqr3Code::Suc => b,
      Eqr3Code::Fail => !b,
    }
  }

  pub fn filter(
    &self,
    l: DiceList,
    c: DiceList,
    r: DiceList,
    op: EqrCode,
  ) -> DiceList {
    if let None = l.diceList {
      return l;
    }

    let mut new_dice: Vec<i32> = vec![];
    let mut count: i32 = 0;
    for v in l.diceList.unwrap() {
      if count < r.calc() {
        if self.countMode(op.check(v, c.calc())) {
          count = count + 1;
        }
        new_dice.push(v);
      }
    }

    DiceList {
      diceList: Some(new_dice),
      calcMode: CalcMode::Sum,
    }
  }
  pub fn filter_once(
    &self,
    l: &Box<Node>,
    c: &Box<Node>,
    r: &Box<Node>,
    op: EqrCode,
    mode: OmissionMode,
  ) -> Node {
    if c.depth() > 1 || r.depth() > 1 {
      return Node::Eqr3(
        Box::new(l._clone()),
        op,
        Box::new(c._calc_once(mode)),
        *self,
        Box::new(r._calc_once(mode)),
      );
    }
    match l.depth() {
      0 | 1 => Node::List(Box::new(self.filter(
        l._calc(MAXIMUM_MODE),
        c._calc(mode),
        r._calc(mode),
        op,
      ))),
      _ => Node::Eqr3(
        Box::new(l._calc_once(mode)),
        op,
        Box::new(c._calc_once(mode)),
        *self,
        Box::new(r._calc_once(mode)),
      ),
    }
  }
}

#[derive(Copy, Clone)]
pub enum DiceCode {
  // ダイス演算子
  Dice,
}
impl Debug for DiceCode {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match *self {
      DiceCode::Dice => write!(fmt, "D"),
    }
  }
}
impl DiceCode {
  pub fn roll(
    &self,
    l_old: DiceList,
    r: DiceList,
    mode: OmissionMode,
  ) -> DiceList {
    if r.calc() <= 0 {
      return DiceList {
        diceList: Some(vec![]),
        calcMode: CalcMode::Sum,
      };
    }
    let l: DiceList = if l_old.calc() <= 0 {
      match mode {
        OmissionMode::Max => DiceList {
          diceList: Some(vec![MAX_DICE_NUM]),
          calcMode: CalcMode::Sum,
        },
        OmissionMode::Min => DiceList {
          diceList: Some(vec![1]),
          calcMode: CalcMode::Sum,
        },
      }
    } else if l_old.calc() > MAX_DICE_NUM {
      DiceList {
        diceList: Some(vec![MAX_DICE_NUM]),
        calcMode: CalcMode::Sum,
      }
    } else {
      l_old
    };

    let face = if r.calc() > MAX_DICE_FACE {
      MAX_DICE_FACE
    } else {
      r.calc()
    } + 1;
    let mut new_dice: Vec<i32> = vec![];
    let mut rd = rand::thread_rng();

    for _ in 0..(l.calc()) {
      new_dice.push(rd.gen_range(1..face));
    }

    DiceList {
      diceList: Some(new_dice),
      calcMode: CalcMode::Sum,
    }
  }
}

#[derive(Copy, Clone)]
pub enum Dice3Code {
  // ダイス演算子
  Adv,
}
impl Debug for Dice3Code {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match *self {
      Dice3Code::Adv => write!(fmt, "K"),
    }
  }
}
impl Dice3Code {
  pub fn roll(
    &self,
    l_old: DiceList,
    c: DiceList,
    r: DiceList,
    op: DiceCode,
    mode: OmissionMode,
  ) -> DiceList {
    if c.calc() <= 0 || r.calc() == 0 {
      return DiceList {
        diceList: Some(vec![]),
        calcMode: CalcMode::Sum,
      };
    }
    let l: DiceList = if l_old.calc() <= 0 {
      match mode {
        OmissionMode::Max => DiceList {
          diceList: Some(vec![MAX_DICE_NUM]),
          calcMode: CalcMode::Sum,
        },
        OmissionMode::Min => DiceList {
          diceList: Some(vec![1]),
          calcMode: CalcMode::Sum,
        },
      }
    } else if l_old.calc() > MAX_DICE_NUM {
      DiceList {
        diceList: Some(vec![MAX_DICE_NUM]),
        calcMode: CalcMode::Sum,
      }
    } else {
      l_old
    };
    let mut new_dice: Vec<i32> = vec![];
    let mut rd = rand::thread_rng();

    for _ in 0..(l.calc()) {
      new_dice.push(rd.gen_range(1..(c.calc() + 1)));
    }
    new_dice.sort_unstable();
    if r.calc() > 0 {
      new_dice.reverse();
    }

    DiceList {
      diceList: Some(
        new_dice[0..(r.calc().abs().try_into().unwrap())]
          .iter()
          .cloned()
          .collect(),
      ),
      calcMode: CalcMode::Sum,
    }
  }
}

peg::parser! {
  grammar dice_parser() for str {
    pub rule arithmetic() -> Node = precedence!{
      x:(@) op:eqrOp() t:eqrCenter()? y:@ {
        match t {
          None => Node::Eqr(Box::new(x), op, Box::new(y)),
          Some(t) => Node::Eqr3(Box::new(x), op, Box::new(t.0), t.1, Box::new(y))
        }
      }
      --
      x:(@) "+" y:@ { Node::Op(Box::new(x), OpCode::Add, Box::new(y)) }
      x:(@) "-" y:@ { Node::Op(Box::new(x), OpCode::Sub, Box::new(y)) }
      --
      x:(@) "*" y:@ { Node::Op(Box::new(x), OpCode::Mul, Box::new(y)) }
      x:(@) "/" y:@ { Node::Op(Box::new(x), OpCode::Div, Box::new(y)) }
      x:(@) "%" y:@ { Node::Op(Box::new(x), OpCode::Mod, Box::new(y)) }
      --
      x:@ ("^" / "**") y:(@) { Node::Op(Box::new(x), OpCode::Pow, Box::new(y)) }
      --
      x:(@) ['d' | 'D'] t:dice3center()? y:@ {
        match t {
          None => Node::Dice(Box::new(x), DiceCode::Dice, Box::new(y)),
          Some(t) => Node::Dice3(Box::new(x), DiceCode::Dice, Box::new(t.0), t.1, Box::new(y))
        }
      }
      ['d' | 'D'] t:dice3center()? y:@ {
        match t {
          None => Node::Dice(Box::new(NULL_NODE), DiceCode::Dice, Box::new(y)),
          Some(t) => Node::Dice3(Box::new(NULL_NODE), DiceCode::Dice, Box::new(t.0), t.1, Box::new(y))
        }
      }
      --
      "-" y:(@) { Node::Unary(UnaryCode::Minus, Box::new(y)) }
      --
      n:pred() { n }
    }

    rule eqrOp() -> EqrCode
      = "!=" { EqrCode::NEq }
      / ">=" { EqrCode::GEq }
      / "<=" { EqrCode::SEq }
      / "=" { EqrCode::Eqr }
      / ">" { EqrCode::Grt }
      / "<" { EqrCode::Sml }

    rule eqrCenter() -> (Node, Eqr3Code)
      = t:pred() ['f' | 'F'] { (t, Eqr3Code::Fail) }
      / t:pred() ['s' | 'S'] { (t, Eqr3Code::Suc) }

    rule dice3center() -> (Node, Dice3Code) = t:pred() ['k' | 'K'] { (t, Dice3Code::Adv) }

    rule whitespace() = quiet!{[' ' | '\n' | '\t']+}

    rule ws<T>(s: rule<T>) -> T = whitespace()* t:s() whitespace()* { t }

    rule brackets<S,T1,T2>(s: rule<S>, t1:rule<T1>, t2:rule<T2>) -> S
      = ws(<t1()>) t:s() ws(<t2()>) { t }
      / t:s()

    rule pred() -> Node
      = ws(<("SUM" / "Sum" / "sum")>) e:brackets(<arithmetic()>, <"[">, <"]">) { Node::Sum(Box::new(e)) }
      / ws(<("COUNT" / "Count" / "count")>) e:brackets(<arithmetic()>, <"[">, <"]">) { Node::Count(Box::new(e)) }
      / ws(<("Repeat" / "Repeat" / "repeat")>) ws(<"[">) e1:arithmetic() ws(<",">) e2:arithmetic() ws(<"]">) { Node::Repeat(Box::new(e1), Box::new(e2)) }
      / n:ws(<number()>) { Node::Number(n) }
      / e:brackets(<arithmetic()>, <"(">, <")">) { e }

    rule number() -> u16 = n:$(['0'..='9']+) {? n.parse().or(Err("u32")) }
  }
}

#[derive(Copy, Clone)]
enum CalcMode {
  Sum,
  Count,
}

pub struct DiceList {
  diceList: Option<Vec<i32>>,
  calcMode: CalcMode,
}
impl Debug for DiceList {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    let mut as_str: Vec<String> = Vec::new();
    if let Some(l) = &self.diceList {
      for v in l {
        as_str.push(v.to_string());
      }
    };

    let modeStr: &str = match self.calcMode {
      CalcMode::Count => "Count",
      CalcMode::Sum => "Sum",
    };

    write!(
      fmt,
      "[{}](Length: {:?}, Mode: {})",
      as_str.join(", ").to_string(),
      as_str.len(),
      modeStr.to_string()
    )
  }
}
impl DiceList {
  pub fn calc(&self) -> i32 {
    match self.calcMode {
      CalcMode::Count => match &self.diceList {
        Some(s) => s.len().try_into().unwrap(),
        None => 0,
      },
      CalcMode::Sum => match &self.diceList {
        Some(s) => s.iter().fold(0, |sum, a| sum + a),
        None => 0,
      },
    }
  }

  pub fn sum(&self) -> DiceList {
    DiceList {
      diceList: Some(self.diceList.as_ref().unwrap().to_vec()),
      calcMode: CalcMode::Sum,
    }
  }

  pub fn count(&self) -> DiceList {
    DiceList {
      diceList: Some(self.diceList.as_ref().unwrap().to_vec()),
      calcMode: CalcMode::Count,
    }
  }
}

pub fn parse(s: &String) -> Node {
  dice_parser::arithmetic(&s).unwrap()
}

pub fn roll_detail<'a>(n: Node, to_out: &'a mut dyn std::io::Write) -> i32{
  writeln!(to_out, "{:?}", n).unwrap();
  let mut n_mut: Node = n._clone();
  while n_mut.depth() > 0 {
    n_mut = n_mut.calc_once();
    writeln!(to_out, "=> {:?}", n_mut).unwrap();
  }
  writeln!(to_out, "=> {:?}", n_mut.calc()).unwrap();
  n_mut.calc()
}