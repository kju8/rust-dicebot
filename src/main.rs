use std::{collections::HashSet, fs::File, io::BufReader, usize};

use serenity::async_trait;
use serenity::framework::standard::{
  help_commands,
  macros::{command, group, help},
  Args, CommandGroup, CommandResult, HelpOptions,
};
use serenity::framework::StandardFramework;
use serenity::model::{channel::Message, gateway::Ready, id::UserId};
use serenity::prelude::{Client, Context, EventHandler, Mentionable};

use serde::{Deserialize, Serialize};
use serde_json::Result;

use std::io::{stdout, Write};

mod roll;

#[derive(Serialize, Deserialize)]
struct Token {
  token: String,
}

//{"token": "This_is_Token"} の形のトークンを取り出す関数
fn get_token(file_name: &str) -> Result<String> {
  let file = File::open(file_name).unwrap();
  let reader = BufReader::new(file);
  let t: Token = serde_json::from_reader(reader).unwrap();
  Ok(t.token)
}

struct Handler;

#[async_trait]
impl EventHandler for Handler {
  // Botが起動したときに走る処理
  async fn ready(&self, _: Context, ready: Ready) {
    // デフォルトでC言語のprintfのようなことができる
    println!("{} is connected!", ready.user.name);
  }
}

#[group]
#[description("汎用コマンド")]
#[summary("一般")]
#[commands(roll)]
struct General;

#[command]
#[description = "ダイスロールします"]
async fn roll(ctx: &Context, msg: &Message, args: Args) -> CommandResult {
  let mut args_vec = args.raw().collect::<Vec<&str>>();
  let detail_mode = args_vec[0] == "-d";
  let roll_str = match detail_mode {
    true => args_vec.split_off(1).join(""),
    false => args_vec.join("")
  };
  if detail_mode {
    println!("Detail Mode");
  }
  println!("{:?}", roll_str);

  let n = roll::parse(&roll_str);

  let mut out_str = Vec::new();
  let fin = roll::roll_detail(n, &mut out_str);
  let detail_str = String::from_utf8(out_str).unwrap();
  print!("{}", detail_str);

  if !detail_mode {
    msg.channel_id
        .say(&ctx.http, format!("{} {} = {}", msg.author.mention(), roll_str, fin))
        .await?;
  } else {
    msg.channel_id
        .say(&ctx.http, format!("{}\n{}", msg.author.mention(), detail_str))
        .await?;
  }
  // msg.channel_id.say で、channel_id の channel にメッセージを投稿
  // msg
  //   .channel_id
  //   .say(&ctx.http, format!("{} にゃーん", msg.author.mention()))
  //   .await?;
  // CommandResultはResultを継承している
  // `Result?` は正常な値の場合、Resultの中身を返し、エラーの場合は即座にreturnする演算子
  Ok(())
}

#[help] // Helpコマンド
#[individual_command_tip = "これはヘルプコマンド"] // Helpコマンドの説明
#[strikethrough_commands_tip_in_guild = ""] // 使用できないコマンドについての説明を削除
async fn my_help(
  ctx: &Context,
  msg: &Message,
  args: Args,
  help_options: &'static HelpOptions,
  groups: &[&'static CommandGroup],
  owners: HashSet<UserId>,
) -> CommandResult {
  // _ は使用しない返り値を捨てることを明示している
  let _ =
    help_commands::with_embeds(ctx, msg, args, help_options, groups, owners)
      .await;
  // 空のタプルをreturn（仕様）
  // Rustでは`;`なしの行は値としてreturnすることを表す
  // return Ok(()); と同義
  Ok(())
}

#[tokio::main]
async fn main() {
  // Discord Bot Token を設定
  let token = get_token("config.json").expect("Err トークンが見つかりません");
  // コマンド系の設定
  let framework = StandardFramework::new()
    // |c| c はラムダ式
    .configure(|c| c.prefix("!")) // コマンドプレフィックス
    .help(&MY_HELP) // ヘルプコマンドを追加
    .group(&GENERAL_GROUP); // general を追加するには,GENERAL_GROUP とグループ名をすべて大文字にする

  // Botのクライアントを作成
  let mut client = Client::builder(&token)
    .event_handler(Handler) // 取得するイベント
    .framework(framework) // コマンドを登録
    .await
    .expect("Err creating client"); // エラーハンドリング

  // メインループ。Botを起動
  if let Err(why) = client.start().await {
    println!("Client error: {:?}", why);
  }
}
