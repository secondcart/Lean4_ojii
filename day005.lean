import Mathlib

-- 第五話「calc, sorry, ring」

-- ワシ「次を見てみよう.」

variable (a b c d e f : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- 学「えーと, ... わかった! カーソルを置くとわかるね.」
-- ワシ「確かにその通りだけど, `calc` を使うことで, 普段行う計算のようにみることができる.」

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  -- `calc`: 計算モードに入る.
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      -- `sorry`: 証明したことにする
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

-- 学「確かに, 各行で何をやるか, カーソルを当てなくてもわかるね. `sorry` は何?」
-- ワシ「これは, かくことで証明したことにしてくれるtactic.」
-- 学「え, それありなの!」
-- ワシ「もちろん, 最終的には, 消さないといけない. Leanもエラーはでないけど, 警告は出る.
--       上のように, 一旦証明の細部を飛ばして証明の概要を組み立てるときに便利.」
-- 学「さっきまでの例と比べると, `sorry` は, 対応する `rw` を埋めればいい?」
-- ワシ「さす孫! 正解.」

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

-- ワシ「`calc` で始まる式は, (tacticを使う証明ではなく)証明項になる.
--      そのため, `by` で始まらないことに注意.
--      また, 少し制約が多くて, インデントや `_` にも気を付けないといけない.」

-- ワシ「便利なtacticがある.
--      ここまで, `rw` とかを使ってかいたけど, 毎回かくのは大変だ.」
-- 学「確かに. もっと証明が長い定理とかだと疲れそう.」
-- ワシ「そういうときのために, Leanでは, ある程度自動的にやってくれるtacticがある.
--       今回は, `ring` がそれだ.」

example : c * b * a = b * (a * c) := by
  -- `ring`: 可換環の等式を示す
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

-- 学「すごい! `ℝ` が可換環だから, 可換環の性質は使えるってこと?」
-- ワシ「その通り. 注意してほしいのは, あくまで可換環の等式が使えるだけで,
--      仮定を読むこととかはできない.
--      なので, 最後の例では, `rw[hyp, hyp']` を入れる必要がある.」

-- ワシ「今日はここまで!」
