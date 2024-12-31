import Mathlib

-- 第十六話「論理積」

-- ワシ「今回は, 論理積 `∧` を進める.」

-- 一部改変
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  -- `constructor`: 論理積や同値性を示す
  constructor
  · -- `assumption`: 仮定を自動でexact
    assumption
  . intro h
    apply h₁
    rw [h]

-- (注) `.` は無くても問題ないです. 見やすさのために付けました.

-- ワシ「goalが `P ∧ Q` のとき, `constructor` で, goalを分割できる.」
-- 学「分割したgoalそれぞれを証明すればいいんだね. `assumption` は, `exact h₀` と同じ?」
-- ワシ「その通り.」

-- ワシ「仮定に, `P ∧ Q` があるときは, `∃` 同様に, `rcases` が使える.」

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

-- ワシ「以下のように, `h.left`, `h.right` とかくことで,
--      `h: A ∧ B` の2つの構成要素を取り出すことができる.」

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  apply le_antisymm
  . apply h.left
  . apply h'

-- ワシ「各goalに同じtacticを使用したいとき, `<;>` が使える.」

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  -- `<;>`: 生成された全ゴールに適用
  constructor <;> norm_num

-- ワシ「次は, 論理和 `∨` を進める.」

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  -- `left`: 論理和 `∨` を示す
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  -- `right`: 論理和 `∨` を示す
  right
  linarith [pow_two_nonneg x]

-- ワシ「次は仮定に, `∨` がある場合だ. このときは, `rcases` を使う.」
-- 学「(また, `rcases` か..)」

example : x < |y| → x < y ∨ x < -y := by
  -- `le_or_gt`: a ≤ b ∨ a > b
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

-- 学「仮定に, `P ∨ Q` の形ないと思ったけど,
--     考えるときに, `0 ≤ y` か `0 > y` の場合分けが必要だから付け足したってこと?」
-- ワシ「さす孫! ちなみに, 行数を減らしたいから, 複数のtacticを `;` で1行にまとめている.」

-- ワシ「場合分け関連のtacticだと `by_cases` もある.」

example (P : Prop) : ¬¬P → P := by
  intro h
  -- `by_cases`: 排中律
  by_cases h' : P
  · assumption
  . contradiction

-- 学「排中律は, 『`P` もしくは, `¬ P`』という命題は真という原理だよね?」
-- ワシ「その通り. `by_cases h' : P` とすることで, `h' : P`, `h' : ¬ P` にわけている.」

-- ワシ「今日はここまで.」
