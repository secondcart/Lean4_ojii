import Mathlib

-- 第十一話「束&trans」

-- 学「おじいちゃん, 疑問があるんだけど?」
-- ワシ「(学から, 始まるの珍しいな.) なんだ?」
-- 学「昨日の `example` だけどさ,」

variable(a b c d e : ℝ)

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

-- 学「最初のgoal が `min a b = min b a` じゃなくて, `a ⊓ b = b ⊓ a` だけど, これは何?」
-- ワシ「これは, 束(lattice)という構造から来ている.
--      以前の `Ring` のように, Leanでは具体的な構造ではなく, 抽象的な構造を使う.」

variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

-- ワシ「(wikiによると)『任意の二元集合が一意的な上限および下限をもつ半順序集合』が束になる.
--      『自然数全体の成す集合(ただし, 0を含む) ℕ に対し,
--       通常の大小関係を考えたものは `min` および `max` を演算として束を成す.』」
-- 学「なるほど. じゃあ, `min`, `max` を一般的にして書いた演算が, `⊓`, `⊔`?」
-- ワシ「さす孫! ちなみに, `⊓`(`\inf`), `⊔`(`\sup`) と打てる.」
-- ワシ「せっかくだし, 上に関連する `example` を出す.」

example (h : x ≤ z) : x ⊓ y ≤ z :=by
  -- `trans`: 推移律を利用する
  trans x
  . apply inf_le_left
  . exact h

-- 学「推移律は, `a ≤ b → b ≤ c → a ≤ c` だよね?
--     今回だと `x ⊓ y ≤ x → x ≤ z → x ⊓ y ≤ z` ということ?」
-- ワシ「その通り. `trans` と推移律を使うことで, 自分が好きなようにgoalが分解できる.」

-- ワシ「少し早いけど, 今日はここで終わり.」

-- おじいちゃんのひとりごと
-- 戦術, タクティクよりtacticの方がいいよね.
-- 最近, 年の割に新しいことをどんどん受け入れてて, 夢見てる気がする.
