import Mathlib

-- 第十話「不等式の証明(続き)&min」

-- ワシ「昨日の復習で以下を解いてみよう.」

open Real

variable(a b c d e : ℝ)

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  apply log_le_log h₀
  sorry

-- 僕「(疲れた. これおじいちゃん解いてるのかな.) できた. `norm_num` って何?」
-- ワシ「(その顔は, 疑っているな. 解いてないぞ.)
--       `norm_num` は, 具体的な数値についてのgoalを閉じるtactic.」
-- 僕「不等式だから, `linarith` はダメなの?」
-- ワシ「さす孫! それでもできるけど, 実行に時間がかかる.」

-- LBE
-- `#time`: 実行時間計測
#time example : 1 < 2 :=by linarith
#time example : 1 < 2 :=by norm_num

-- 学「これって, Mathlibにある定理についてある程度知ってないときついね.」
-- ワシ「そんなことないぞ. Mathlibのwebpageを見てもいいし, 命名規則から名前を推測とか,
--       ある程度定理名を推測して, Ctrl+Space(Mac: Cmd+Space)で定理名を補完できる.
--       他にもVSCode上で, 定理を右クリックして `Go to Definition` を選ぶと,
--       定義されているファイルに飛ぶから, そこで類似の定理を探すことができる.
--       それと, `apply?` でライブラリ中の関連する定理を探すこともできる.」

example : 0 ≤ a ^ 2 := by
  -- `apply?`: applyできるか検索
  apply?

-- 学「Lean Infoviewには, `exact sq_nonneg a` と出てるけど, これを使えばいい?」
-- ワシ「その通り.」

example : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

-- ワシ「話は変わるが, 今度は関数 `min` をみる.」

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)


-- ワシ「注意として, 関数 `min` は `ℝ → ℝ → ℝ` 型の関数.
--      昨日言ったように, 矢印は右結合だから `ℝ → (ℝ → ℝ)` と同じ意味になる.
--      だから, `min a` は `ℝ → ℝ` 型になり, `min a b` は `ℝ` 型になる.」
-- ワシ「次を見よう.」

#check le_antisymm -- a ≤ b → b ≤ a → a = b

example : min a b = min b a := by
  apply le_antisymm
  · -- `show`: 示すべきことを宣言
    show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    . apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    . apply min_le_left

-- 学「goalが複数あるから, `.` で区切ると見やすいね. `show` は必要なの?」
-- ワシ「無くてもいい. ただ, 証明が読みやすいし, 現在のgoalを確認できる.」
-- 学「本当だ! `show min a b ≥ min b a` にするとエラーになる. ただのコメントとは違うね.」

-- (注) 見やすさのため, `.` を使っていますが, 実は以下でも問題なくできます.
example : min a b = min b a := by
  apply le_antisymm
  show min a b ≤ min b a
  apply le_min
  apply min_le_right
  apply min_le_left
  show min b a ≤ min a b
  apply le_min
  apply min_le_right
  apply min_le_left

-- ワシ「今回のは, 同じことの繰り返しで少し長く感じたかもしれない.
--      そのときは, `repeat` が便利だ. これは指定したtacticを失敗するまで繰り返す(LBE).」

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left
