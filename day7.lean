import Mathlib

-- 第七話「環の公理(続き)&have」

-- ワシ「前回の続きだが, 昨日の宿題は解けたか?」
-- 学「何とか解けた. `rw` 3つで済んでよかった. でも, 少し気になる点があるんだけど.」
-- ワシ「何だ?」

-- MIL(再掲)
namespace day6

variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

end day6

-- 学「`variable` や `add_left_cancel` で, `{}` になっているけど, なんで?
--     いつも `()` だよね?」
-- ワシ「さす孫! `{}` は暗黙の引数だ.」
-- 学「暗黙の引数?」
-- ワシ「以下に, `{}` と `()` の例を示す.」

namespace day7

variable {R : Type*} [Ring R]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_left_cancel2 (a b c : R) (h : a + b = a + c) : b = c := by
  sorry

variable (d e f : R)

example (h : d + e = d + f) : e = f := by
  rw[add_left_cancel h]

example (h : d + e = d + f) : e = f := by
  rw[add_left_cancel2 d e f h]

-- ワシ「`add_left_cancel`, `add_left_cancel2` は `{}`, `()` が違うだけで,
--      証明したいことは同じだ. けど, 使う際に, 引数が違う.」
-- 学「確かに, `add_left_cancel` は `h` だけで,
--    `add_left_cancel2` は `d`, `e`, `f`, `h` と4つもあるね.」
-- ワシ「実際は, こんなにいらない. なぜなら仮定 `h` で, 対象が判断できるからだ.」
-- 学「確かに, `d + e` とかいているから, 環だとわかりそうだね.」
-- ワシ「その通り. 数文字多いだけとはいえ, 何回もかくと結構面倒になる.
--      そのため, `{}` を使うことで, 暗黙の引数として, 使うときは省略することができる.」
-- 学「なるほど.」

-- ワシ「次は以下を環の公理のみを使って解いてみよう. 一旦Leanは忘れていいぞ.」
-- 学「わかった. 普通に考えてみる. `add_left_cancel` は使っていい?」
-- ワシ「いいぞ.」

-- 環 `R` の元 `a` に対して, `a * 0 = 0`.

-- 学「できた!」
-- 学くんのメモ
-- `a * 0 + 0 = a * 0 = a * (0 + 0) = a * 0 + a * 0 ⇒ a * 0 = 0`

-- ワシ「これをLeanでかけそう?」
-- 学「えーと, `rw` で, `a * 0` を `a * (0 + 0)` にして, そして `a * 0 + a * 0` だから,
--     でも, 右辺が `a * 0 + 0` でなくて, `0` だから, えーと...」
-- ワシ「もし, goalが `a * 0 + 0 = a * 0 + a * 0` ならできそうか?」
-- 学「それは, `rw` でできそう.」
-- ワシ「`a * 0 + 0 = a * 0 + a * 0` から, `a * 0 = 0` はできそう.」
-- 学「それも `add_left_cancel` でできそう.」
-- ワシ「そんなときに, 便利なtacticが `have`.」

theorem mul_zero (a : R) : a * 0 = 0 := by
  -- `have`: 補題を用意する.
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

-- 学「証明できる補題を用意して, それが解けたら仮定になるってこと?」
-- ワシ「その通り. `have` の証明は, インデントを付けて証明する必要がある.
--       `rw [← mul_add, add_zero, add_zero]` の左にカーソルを当てるとわかるが,
--       goalが `a * 0 + a * 0 = a * 0 + 0` と, `h` の証明になっている.
--       `h` の証明を終えて, インデントを戻すと, `h` が仮定として追加される.」

-- ワシ「今日はここまで.」
end day7
