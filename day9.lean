import Mathlib

-- 第九話「不等式の証明」

-- ワシ「今まで証明に主に `rw` (書き換え)を使ったけど, それが使えない証明もある.
--       今日はそれをみる.」

-- ワシ「Mathlibには, 以下の定理がある.」

variable(a b c d : ℝ)

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

-- ワシ「`le_trans` は証明でどう使うと思う?」
-- 学「`apply le_trans a b c` とか?」
-- ワシ「残念. それはできない. `le_trans` は `a`, `b`, `c` を暗黙の引数として使っている.」
-- 学「`add_left_cancel` のときみたいに, 仮定を使うとか?」
-- ワシ「正解!」

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

-- 学「`.` は何?」
-- ワシ「これはgoalを二つに分けている. まず, `→` は右結合になっている.
--       つまり, `A → B → C` は, `A → (B → C)` と同じ意味だ.
--       このとき, `C` が正しいことを示すには, まず `A` が正しいこと,
--       次に `B` が正しいことを示す必要がある.
--       そのため, goalを `A` と `B` に分ける.」
-- 学「確かに.」
-- ワシ「今回は, `x ≤ z` を示す際に, まず `x ≤ ?` を示す. 」
-- 学「? `x ≤ y` じゃないの? あ, 単に `le_trans` だと間の数が `y` か特定できないのか.」
-- ワシ「その通り. このとき, `apply h₀` で, `x ≤ y` が適用でき, goalを閉じる.」
-- ワシ「次は, `y ≤ z` を示す.
--      先ほどの `apply h₀` で既に `y` と特定されているため, `? ≤ z` ではない.
--      `apply h₁` を使って, goalを閉じる.」
-- 学「なるほど. `.` ごとにgoalがあるんだね.
--     あれ? 仮定をそのまま使うなら, `exact h₀` はダメなの?」
-- ワシ「さす孫! 実はそれでもいい. `apply` は `exact` の代わりに使うことができる.
--       また, 詳しくは割愛するが, `apply` の方が上手く使えることが多い.
--       ただ, `exact` を使うことで読みやすいというメリットはある.」
-- 学「確かに `apply` は, 使い方が多いから, たまに `exact` があった方がわかりやすいかもね.」

-- (注) 実は以下のような書き方もあります. もちろんどちらでもいいです.
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

-- ワシ「ちなみに, `ring` のときみたいに, これに関しても自動的に行う便利なtacticがある.」

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  -- `linarith`: 線形(不)等式を示す
  linarith

-- ワシ「実数上の不等式を示すために用意されたMathlibの定理を見る.」

-- `open`: 名前空間を開く.
open Real
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left

-- 学「名前空間は, 何に使うの?」
-- ワシ「`exp` を使うときに必要. これは, Mathlib側で用意した名前空間 `Real` に入っていて,
--       なので, 名前空間を使わずにかくと, `Real.exp` になる.
--       少し長くて面倒だから, `open Real` とした.」

-- ワシ「↑の `exp_le_exp` と `linarith` で以下ができる.」

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

-- 学「`linarith` に使ってほしい補題を渡せるということ?」
-- ワシ「その通り. なお, `h: A ↔ B` に対して,
--      `h.mp` が `A → B`, `h.mpr` が `B → A` となる. `mp` は `modus ponens` の略.
--      `mpr` は `modus ponens reverse` の略.」
-- 学「`modus ponens` って何?」
-- ワシ「わからん. ググってくれないか.」
-- 学「...わかった. (おじいちゃん, ググるという言葉知ってるんだ.)」
