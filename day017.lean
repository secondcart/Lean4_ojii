import Mathlib

-- 第十七話「数列と収束」

-- ワシ「今まで十分色々なtacticを学んだから, 今日から本格的な数学に入る.
--      もちろん, 初見のtacticはきちんと紹介する.」
-- ワシ「今日は数列と収束だ.」

-- ワシ「Leanでは, 収束は次のように定義する.」

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- ワシ「さっそく, 新しいtacticを紹介する.」

-- 一部改変
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  -- `ext`: 外延性を使う.
  ext x y
  ring

-- ワシ「(LBE)外延性というのは, 『同じものから作られているものは同じである』という主張.
--      たとえば, 集合 `A, B ⊆ α` について `A = B ⇔ (x ∈ A ↔ x ∈ B)`
--      だし, 2つの写像 `f g : A → B` に対して, `f = g ⇔ ∀ a ∈ A (f a = g a)` となる.」
-- 学「なるほど, 今回は, 任意の `x y` で, 外延性を使いたいから, `ext x y` になるわけだね.」

-- ワシ「次は, `congr` だ. これは, 合同(congruence)からきている.」

example (a b : ℝ) : |a| = |a - b + b| := by
  -- `congr`: ゴールの関数適用を外す
  congr
  ring

-- ワシ「(LBE) `f₁ = f₂` かつ `a₁ = a₂` ならば `f₁ a₁ = f₂ a₂` という事実がある.」
-- 学「等しい関数で, 等しい元だから正しいね. `congr` は, これを使って分解しているの?」
-- ワシ「さす孫! この場合, 関数は絶対値だな.」

-- ワシ「次は `convert` だ.」

-- 一部改変
example {a : ℝ} (h : 1 < a) : a < a * a := by
  -- `convert`: 惜しい補題を使う
  --  `mul_lt_mul_right`(a0 : 0 < a) : b * a < c * a ↔ b < c
  convert (mul_lt_mul_right _).mpr h
  · rw [one_mul]
  apply lt_trans zero_lt_one h

-- 学「惜しい補題って, 何?」
-- ワシ「現時点の仮定と補題で, ギリギリできないという感じだな.
--      `convert` では, 一旦 `apply` して進めて, できない部分の差を新たなgoalとして埋める.」
-- 学「`mul_lt_mul_right.mpr` で, 仮定 `h : 1 < a` だから,
--     `0 < a` かつ, `1 < a` ならば, `1 * a < a * a` になるよね. あれ, できてる?
--     あ, 違うか, `1 * a = a` を別に証明しないといけないか.」
-- ワシ「その通り. `1 * a = a` は別のgoalとして, `. rw[one_mul]` でおこなっている.」
-- 学「`convert` が完了した後, goalが `0 < a` なのは,
--    `mul_lt_mul_right.mpr` の仮定で必要なのに使ってないから?」
-- ワシ「さす孫! これは, `convert (mul_lt_mul_right _).mpr h` の `_` が鍵を握っている.
--       `convert` ではなく `apply` の話だが, `_` を含む式を `apply` すると,
--       Lean側で自動的に埋めようとして, 埋められない場合はそれが新しいgoalになる.」

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  dsimp
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

-- 学「↑は, 定数列が収束するということ?」
-- ワシ「その通り.」

-- ワシ「今日はここまで!」

-- おじいちゃんのひとりごと
-- 数列の収束に関しては, 参考サイトにもっと色々あります.
-- たとえば, `a` に収束する `s n`, `b` に収束する `t n` において,
-- 積 `s n * t n` は, `a * b` に収束するとかです.
-- ただ, 触れませんでした. 老い先短いから許してね.
