import Mathlib

-- 第十三話「存在量化子」

-- ワシ「前回, 全称量化子をやったから, 今回は存在量化子を扱う.
--      ところで, 以下は正しいか? `∃ x : ℝ, 2 < x ∧ x < 3`.」
-- 学「うん, 正しいよ. `2.5` がそうだよ.」
-- ワシ「このとき, 使えるtacticが `use`.」

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

-- 学「(しょぼいtacticだな.)」
-- ワシ「`use` は値だけでなく, 証明を渡すこともできる.」

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2

-- ワシ「さらに, 利用可能な補題があると, 自動的に使うこともできる.」

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  -- Leanが文脈から推測できない場合, `5 / 2` を `(5 : ℝ) / 2` とかくこともある.
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2

-- 学「見直した.」
-- ワシ「何が?」

-- ワシ「前回, 上界の定義をしたけど, 今回は存在量化子を使って似たものを定義する.」

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

-- 上界をもつ写像の定義
def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

variable(a b : ℝ)
variable {f g : ℝ → ℝ}

-- 再掲
theorem fnUb_add (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  -- `rcases`: パターン分解
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add
  apply ubfa
  apply ubgb

-- 学「...難しいね.」
-- ワシ「たとえば, 性質 `P` が成り立つ実数が存在するならば, `Q` という命題は,
--      実数 `x` があって, その実数 `x` に対して `P` が成り立つならば, `Q` と同値だよね?」
-- 学「(なんとなく)確かに.」
-- ワシ「`rcases` は, それを分解している. たとえば, 仮定 `ubf` から,
--       `FnHasUb f` を満たす `a : ℝ` が存在する.
--       これを, `a : ℝ` と, `ubfa : FnUb f a` にわけている.」
-- 学「なるほど, でも難しいね.」
-- ワシ「`rcases` は結構ややこしい.」

-- 一部改変
-- 写像 `f` が上界をもち, 写像 `g` が上界をもつならば, 写像 `f + g` も上界をもつ.
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  use a + b
  apply fnUb_add
  exact ubfa
  exact ubgb

-- 学「また, ややこしそうなtacticが出た.」
-- ワシ「`rintro` は, `intro` と `rcases` を組み合わせたもので,
--      省略せずにかくと以下になる.」

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  intro ubf
  intro ubg
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add
  exact ubfa
  exact ubgb

-- 学「これだとわかりやすいけど, 行も増えるし, 新たな文字(`ubf`, `ubg`) も増えるね,
--     そう考えると, `rintro` が必要な理由もわかる.」
-- ワシ「(物分かりがいい孫だ.)」
