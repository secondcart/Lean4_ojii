import Mathlib

-- 第八話「環の公理(続き)&have&apply&rfl」

-- ワシ「さっそくだが, 環の公理の復習として以下を解いてみよう.」

namespace day8

variable {R : Type*} [Ring R]
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  -- `apply`: 含意 `→` を示す.
  apply neg_eq_of_add_eq_zero -- a + b = 0 → -a = b
  -- goalが `-0 = 0` から `0 + 0 = 0` になる
  rw [add_zero]

-- 学「疲れたけど, できた. `(-0 : R)` は何?」
-- ワシ「Leanでは, `0` はデフォルトでは自然数を指す.
--      ただ, 今回は環 `R` の元として使いたいから, 上のような注釈をつける.」

-- 学「`apply` は何?」
-- ワシ「`apply` は含意 `→` をgoalに適用するtactic.」
-- 学「?」
-- ワシ「`neg_eq_of_add_eq_zero` は, `a + b = 0` ならば `-a = b` という定理.
--      この定理から, `-a = b` を示すには, `a + b = 0` を示せばよいことになる.」
-- 学「確かに. `a + b = 0` が真ならば,
--    `neg_eq_of_add_eq_zero` を使って, `-a = b` も真になる.」
-- ワシ「その通り. そういうときに便利なのが, `apply`.」
-- 学「つまり, goalが `Q` で, `P → Q` となる仮定や定理があれば, `apply` を使って,
--     goalが `P` になるということ?(LBE)」
-- ワシ「さす孫!」

-- ワシ「ここまで環の足し算ばかりみたが, 引き算は, 加法の逆元との足し算と等しい.」

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

-- ワシ「実数は, そのように定義されている.」

example (a b : ℝ) : a - b = a + -b := by
  -- `rfl`: 関係の反射性を利用する
  rfl

-- ワシ「`rfl` は, reflexivity(反射性)からきている.
--      左辺=右辺のときに, goalを閉じることができる.
--      今回は, 実数において, 左辺と右辺が等しいから閉じることができた.」
-- 学「`rw` のときも左辺=右辺だったけど, 使わなかったよ.」
-- ワシ「`rw` は書き換えた後に, 自動的に `rfl` を実行する.」

-- 学「そういえば, 環があるのはわかったけど, 群もあるの?」
-- ワシ「ある.」

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

-- 学「これは, 可換群は `CommGroup`?」
-- ワシ「その通り!」
-- 学「うーん.」
-- ワシ「どうした?」
-- 学「tacticの `ring` は可換群なのに, 構造の `Ring` は可換ではないのが少しもやっとする.」
-- (注) `ring` は可換環ではなく, 厳密には可換半環です.
-- ワシ「なるほど, 歴史的な理由もあるけど,
--      可換環はよく扱うから, tacticには, 短い名前を付けた方が便利という理由がある.」
-- 学「なるほど.」

-- ワシ「今日はここまで.」

end day8
