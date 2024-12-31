import Mathlib

-- 第六話「環の公理」

-- ワシ「前回, `ring` のときに, 環の話をしたけど, 今回は, その環をベースに話す.」
-- ワシ「(ずっとtacticの話をするのも飽きた.)」
-- ワシ「環の公理は, Leanで以下のようにかける.」

-- MIL
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

-- 学「`variable (R : Type*) [Ring R]` って何?」
-- ワシ「今はまだ気にしなくてよい. この書き方で,
--       型 `R` に対して, 環の構造が与えられているとわかればよい.」
-- 学「`ℝ` とか `ℤ` みたいに具体的な構造ではなく, 抽象的な構造でかけるのはいいね.
--     あれ, `mul_comm` はないの?」
-- ワシ「さす孫! これは可換環ではない. だから, `mul_comm` はない.
--      可換環を宣言する場合は `CommRing` を使う.」

variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

-- 学「可換環は, 環とは別にあるんだ. あれ? 見たことある気が.」
-- ワシ「これは昨日の終わりに, みせたものと同じだ. `ℝ` が可換環だから, 上と同じことができた.」
-- 学「なるほど, `by ring` みたいに `by` と同じ行に書いてもいいの?」
-- ワシ「見やすさの問題だな. 証明が短ければ, 同じ行にかくとよい.」

-- ワシ「環の公理に戻るが, `a + 0 = a` や `a + -a = 0` は上にかかれてない. なんでだと思う?」
-- 学「環の公理で証明できるから?」
-- ワシ「その通り!」

-- `namespace`: 名前空間を宣言する(`end` で終了)
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

#check add_zero

-- 学「確かに環の公理から証明できたね. 名前空間って何?」
-- ワシ「実は, 上で証明した `add_zero`, `add_right_neg` は既にMathlibで用意されている.
--       それを名前空間なしでかくと, 名前の衝突によるエラーが起きる.」
-- 学「同じ名前の定理で, 中身が微妙に違うものが作られるから?」
-- ワシ「その通り. まぁ, 中身が全く同じでもLeanではエラーになる.」
-- 学「定理の名前を変えるはダメなの?」
-- ワシ「それもいい解決策だ. ただ, Mathlibにどんな定理があるかを教えたいから, 今回はあえて
--       同じ名前を付けている.」
-- 学「`#check MyRing.add_zero` を見ると,
--     名前空間 `MyRing` 内に置かれた定理 `add_zero` は `MyRing.add_zero` になるの?」
-- ワシ「その通り! ただ, 名前空間内なら, 単純に `add_zero` でも同じ意味になる.
--       名前空間の外に, `#check add_zero` とあるが, これは Mathlibが用意した定理を指し,
--       名前空間内の `#check add_zero` とは違う.」

-- ワシ「今日はここまで. 最後に宿題だ.」
-- 学「えー, 急に!」
-- ワシ「諸事情だ. 参考サイトで, 問題にしているものを勝手に答えを公開するのはよくないので,
--      宿題という形にした.」
-- 学「(何言ってんだろ.) とりあえず, 下の `sorry` を変えればいいのね.」

namespace day6

variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

end day6
