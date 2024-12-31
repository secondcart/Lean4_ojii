import Mathlib

-- 第十四話「単射, 全射」

-- ワシ「一昨日, `∀` は定義に隠れていることがあるといったけど, `∃` も同様だ.
--      今日は, 重要な例として, 単射, 全射をみる. まず単射.」

open Function

#check Injective

-- 一部改変
-- 写像 `f: x ↦ x + c` は単射
example (c : ℝ) : Injective fun x ↦ x + c := by
  intro a b
  dsimp
  apply (add_left_inj c).mp

-- ワシ「単射は, Mathlinでは, `Function.Injective f` で定義している.
--      そのため, 名前空間として, `Function` を開く.」
-- ワシ「そもそも単射の定義は知っているか?」
-- 学「えーと,写像 `f` が単射は `∀ x₁, x₂(f(x₁) = f(x₂) ⇒ x₁ = x₂)`　だっけ?」
-- ワシ「その通り, `x₁`, `x₂` は暗黙の引数なので, 使うときは, `Injective f` でよい.」
-- 学「証明は, 最初の `intro a b` で全称記号が消えて, `dsimp` した後に,
--     `a + c = b + c → a = b` になって, `add_left_inj` を `apply` か, なるほど.」

-- ワシ「次は全射だ.」

-- 一部改変
-- 写像 `f: x ↦ x + c` は全射. ただし, `f: ℝ → ℝ`.
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  dsimp
  use x - c
  dsimp
  ring

-- 学「全射の定義は, 写像 `f : α → β` に対して, `∀ y ∈ β ∃ x ∈ α (f(x) = y)` だっけ?」
-- ワシ「その通り, 全射の定義は, `∀`, `∃` どちらもあるので, `intro` も `use` も使う.」
-- 学「これもわかった. Lean4初めて面白いと思った.」
-- ワシ「(遅.)」

-- ワシ「もう一度, 全射の `example` を見よう.」

-- `f : ℝ → ℝ` が全射ならば, `f(x)^2 = 4` となる `x` が存在する.
example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

-- 学「1行目がよくわからない.」
-- ワシ「`Surjective f` だから, `∀ y ∈ ℝ  ∃ x ∈ ℝ (f(x) = y)` になる.
--      当然, `y = 2` の場合は, `∃ x ∈ ℝ (f(x) = 2)` となる.
--      これを新たな仮定 `h₂` とする.
--      仮定 `h` の特殊な例が, `h₂` なので, 仮定 `h` が, 仮定 `h`, `h₂` になっても
--      仮定は緩くもきつくもなっていない. (`h` を満たす ↔ `h` を満たす　かつ `h₂` を満たす)
--      この `h₂` に関して `rcases` を使う, つまり以下と同じだ.」

example {f : ℝ → ℝ} (h : Surjective f) (h₂ : ∃ x : ℝ , f x = 2): ∃ x, f x ^ 2 = 4 := by
  rcases h₂ with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

-- 学「↑はわかった. 最初の `rcases h 2 with ⟨x, hx⟩` は, `rcases` が仮定だけでなくて,
--     値にも適用できるということ?」
-- ワシ「さす孫!」
