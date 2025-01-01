import Mathlib

-- 第十五話「否定」

-- ワシ「今回は否定をテーマに, いろいろなtacticをみる.」

variable(a b : ℝ)

-- 一部改変
-- `a < b` ならば, `¬ (b < a)`
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a :=by apply lt_trans h h'
  show False
  apply lt_irrefl a
  exact this

-- 学「`intro h'` をすると, goalが `False` になってる!」
-- ワシ「否定の `¬ A` は, Leanでは, `A → False` で定義される.
--      そのため, `¬ b < a` は `b < a` が仮定にいき, goalが `False` になる.」
-- 学「`have` で, 補題に名前がないけどいいの?」
-- ワシ「問題ない. その場合は, `this` という名前がつく.」
-- 学「`lt_irrefl` は, `¬ a < a` つまり, `a < a → False` になるから,
--     `apply` して, goalが `a < a` つまり, `exact this` で閉じることができる.」
-- ワシ「大分理解できているな. すごいぞ!」
-- 学「(さす孫じゃないのか.)」

-- ワシ「次は背理法を学ぶ.」

-- LBE
variable (P Q : Prop)

example (h: ¬Q → ¬P) : P → Q := by
  intro hP
  -- `by_contra`: 背理法
  by_contra hnQ
  show False
  have := h hnQ
  -- `contradiction`: 矛盾を指摘
  contradiction

-- 学「`by_contra` というのが, 背理法の部分?」
-- ワシ「その通り, 背理法は, `P` を証明するときに, `P` が偽ならば成り立たない,
--      つまり, `¬ P → False` を示す方法だけど, これがLeanだと `by_contra` でできる.」
-- 学「確かに, goalが `Q` だったのに,  `¬Q` が仮定にいって, goalが `False` になっているね.」
-- ワシ「`contradiction` は名前の通り,
--       `h : P`, `h : ¬ P` のような仮定が矛盾しているときに適用できるものだ.」

-- 学「でも, `¬` が外側にあると, 少しややこしいね. Leanだと括弧もないし.」
-- ワシ「そのときに便利なtacticもある.」

example (h : P → Q) : ¬ (P ∧ ¬ Q) := by
  -- `push_neg`: ドモルガン
  push_neg
  show P → Q
  exact h

-- 学「ドモルガンは `¬ ∀ x, Px` を `∃ x, ¬ P x` に変えるや,
--     `¬ (P ∧ Q)` を `P → ¬ Q` に変形するだよね? 確かに, `¬` が消えて便利だね.」

-- ワシ「次は, `contrapose` だ. これは対偶で, `A → B` というgoalを `¬ B → ¬ A` に変える.
--      または, 仮定 `h : A` で, goalが `B` のとき,
--      仮定 `h : ¬ B`, goalを `¬ A` に変える.」

variable(f: ℝ → ℝ)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  contrapose! h'
  apply h
  exact h'

-- 学「あれ, `contrapose!` になってるよ!」
-- ワシ「`contrapose!` は, 対偶をとった後に簡略化してくれる. `contrapose` を使うとこう.」

example (h : Monotone f) (h' : f a < f b) : a < b := by
  contrapose h'
  apply le_of_not_lt  at h'
  apply not_lt_of_ge
  apply h
  exact h'

-- ワシ「最後に仮定が矛盾しているときにgoalを閉じる方法を教える.」
-- 学「仮定が矛盾していたら, goalの真偽関係なく, 真だよね.」
-- ワシ「その通り. そのように, 『矛盾からはどんな命題でも示せる』という命題(LBE)を,
--       爆発律という.」
-- 学「(すごい名前だな.)」

-- 一部改変あり
example (h : 0 < 0) : a > 37 := by
  -- `exfalso`: 矛盾を示すことに帰着
  exfalso
  apply lt_irrefl 0 h

-- 学「`exfalso` が爆発律?」
-- ワシ「その通り, ラテン語でそういうらしい.」
-- ワシ「ちなみに, 今回の例だと, 単に `linarith` でもよい.」
