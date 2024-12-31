-- 第一話「証明支援系&環境構築」

-- ワシ「Lean4の勉強をはじめるぞ.」
-- 学「はーい.」
-- ワシ「学の言う通り, Leanは, プログラミング言語でもあり, 証明支援系でもある. 」
-- 学「そもそも, Leanなの? Lean4なの?」
-- ワシ「Leanの最新バージョンが, Lean4. ここでは同じ意味で扱う.
--      また, 学は数学が好きだから証明支援系を中心に進める.」

-- 学「証明支援系って?」
-- ワシ「文字通り, 証明を支援してくれる. 数学の証明は大変だろ?」
-- 学「うん. 時間掛かったり, 合っているか不安になったりする.」
-- ワシ「合っているか, つまり証明が正しいことをコンピュータが保証してくれる.」
-- 学「コンピュータ使わなくても, 友達に聞けばいいじゃん.」
-- ワシ「友達も人だから, ミスはあるし, 曖昧な表現になることもある.
--      それに, 数学の証明は膨大なステップを踏むことがある.
--      そのときに, 人の手を使わず, 機械的に保証してくれるのはすごくありがたいことだ.」
-- 学「でも, どうやってLeanが証明を正しいと保証してくれるの?」
-- ワシ「それは, 明日以降で動かすとわかる.」

-- 学「なるほど. 証明支援系は, Leanだけなの?」
-- ワシ「他にも色々ある. Isabelle, Agda, Coqとか. Leanは比較的新しい部類だな.」
-- 学「なんで, その中でもLeanなの?」
-- ワシ「(お前が勧めてきたからだ.) 他の証明支援系にもいい点は多分あるが, 使ったことがないから,
--      ここでは, Lean4のいい点を述べる.」
-- ワシ「1つ目が, Mathlibだ. これは, 数学ライブラリで, 数学のたくさんの定理が入っている.
--       もし証明するときに, 『あの定理が使いたい』と思ったら, Mathlibに基本あるから,
--       それを使えばよい.」
-- ワシ「2つ目がユーザーフレンドリーな設計だ.
--      VS Codeを使うことで, インタラクティブな証明環境になって,
--      証明の進行状況をリアルタイムで確認できる.」
-- 学「(こんな横文字使うおじいちゃん初めて見た.) よくわからなかったけど, 実際に使ったらわかる?」
-- ワシ「もちろん.」

-- 学「ところで, 何で『Lean』というの?」
-- ワシ「さすが, ワシの可愛い孫! 着眼点がすばらしい.
--       (wikiによると)Leanは, 英語で「痩せている」とか「贅肉がない」という意味がある.
--      Leanの基礎としては標準的な依存型理論を最小限の理論に圧縮したものが
--      採用されていることが由来.」
-- 学「...依存型理論? それも, Lean動かしたらわかる?」
-- ワシ「...多分」

-- ワシ「さて, せっかくPCがあるし, Leanを動かそう.」
-- 学「やった! OSはWindowsでいい?」
-- ワシ「なんでもいいぞ. ちなみにインストールしない方法もある.」
-- 学「どういう意味?」
-- ワシ「すまん. Lean4 playgroundというものがあって, それを使うと, ブラウザで再現できる.」
-- https://live.lean-lang.org/
-- ワシ「ただ, 今回は長く使うことになるから, インストールする方法で話を進める.」

-- ワシ「インストールできた?」
-- 学「できた!」
-- ワシ「以下のコマンドをファイル内で打ったらどうなる?」

-- `#eval`: 式を評価する.
#eval 18 + 19

-- 学「右側のLean Infoviewという画面に, `37` と出た.」
-- ワシ「無事インストールできたことが確認できた. 明日はどんな感じで証明するか, 詳しくみよう.」

-- ワシ「今日はもう早い. 帰って寝なさい.」
-- 学「(まだ, 17時半だけど. 年寄りだから寝るの早いな.) わかった.」
-- ワシ「(今日は徹夜だ.)」

-- おじいちゃんのひとりごと
-- 時期によって, やり方は変わるから, 公式を見るのが一番確実です.
-- とはいえ, 日本語でわかりやすいサイトがあったので紹介します.
-- https://aconite-ac.github.io/how_to_install_lean/title_page.html
-- ↑の「1. Leanのインストール方法」と, 「3.2 Leanプロジェクトの作り方」をとくにみるといいです.
-- 「1. Leanのインストール方法」でも, Lean4は使えますが, Mathlibを使う際には,
-- 「3.2 Leanプロジェクトの作り方」が必要です.

-- 「さすが, ワシの可愛い孫! 着眼点がすばらしい.」は, 以後「さす孫」と略します.

-- 今回の `#eval` のように, Lean4には, 独自のコマンドがたくさんあります.
-- そのコマンドの説明は, 以下が丁寧です.
-- https://lean-ja.github.io/lean-by-example/index.html
-- ここでも, 新しいコマンドが出る際に, 一言説明を加えますが, ↑のサイトから拝借しています.