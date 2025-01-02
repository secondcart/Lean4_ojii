import Mathlib

-- 最終話「`√2` が無理数(前編)」

-- ワシ「今日は今まで学んだことを生かして, 証明を解こう! 証明は `√2` が無理数の証明だ.」
-- 学「わかりました!」

-- ワシ「まず, 証明を思い出そう. 説明できるか?」
-- 学「確か...」
-- 1. `√2` が有理数と仮定する.
-- 2. このとき, 互いに素な自然数 `p`, `q` から `√2 = q / p` とかける.
-- 3. 両辺二乗して, 分母を払うと, `2 p^2 = q^2`.
-- 4. 左辺は `2` の倍数だから, `q^2` は `2` の倍数, つまり, `q` も `2` の倍数.
-- 5. `q^2` は `4` の倍数だから, `p^2` が `2` の倍数,つまり, `p` も `2` の倍数.
-- 6. `p`, `q` が互いに素に矛盾.
-- ワシ「そうだったな.　段階を踏んでいこう.」

-- 0. `√2` が無理数
-- ワシ「まず, 何を証明するかをかかないといけない.」
-- 学「それは, そうだ. 『`√2` が無理数』とかければいいけど,
--    Leanの言葉でかかないといけないよね?」
-- ワシ「もちろん.」
-- 学「無理数は, Leanでは何というの?」
-- ワシ「英語で考えればよい. 無理数は irrationalで, 既にLeanで定義されている.」

example : Irrational √2 :=by
  sorry

-- 学「この `sorry` を埋めていく形だね!」

-- 1. `√2` が有理数と仮定する.
-- 学「これはわかった! 背理法だから, `by_contra` だ!」

example : Irrational √2 :=by
  by_contra h
  show False
  sorry

-- 学「これで, `√2` が有理数ならば, 偽になったね. これで `√2` を分数にして矛盾を導けば...」
-- ワシ「まだ, できてないぞ.」
-- 学「え?」
-- ワシ「あくまで `√2` が無理数でないというだけだ. 有理数とは一言も言ってない.」
-- 学「何だよそれ. `¬Irrational x ↔ x ∈ ℚ` ってこと?」
-- ワシ「それもできない. 型の関係上エラーになる.」
-- 学「そっか, もう終わりか.」
-- ワシ「待て, 諦めるのは早い! 少し書き方を変えればよい.
--      実数 `x` が無理数でない(`¬Irrational x`) と, `x = r` となる
--      `r : ℚ` が存在することが同値なら, `x` は分数に分解できる.」

theorem step1 (x : ℝ) : ¬Irrational x ↔ ∃ r : ℚ, x = r :=by
  rw[irrational_iff_ne_rational]
  push_neg
  constructor
  . rintro ⟨a, b, xab⟩
    use a / b
    rw[xab, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
  . rintro ⟨r, xr⟩
    use r.num, r.den
    rw[xr]
    apply Field.ratCast_def r

example : Irrational √2 :=by
  by_contra h
  rw[step1] at h
  sorry

-- 2. このとき, 互いに素な自然数 `p`, `q` から `√2 = q / p` とかける.
-- 学「分数に分解できたは, いいけど, 互いに素が必要だよね.」
-- ワシ「そうだ, それと, 分母が `0` じゃないという情報も今後必要だ.」

-- 有理数は, 互いに素な整数 `a,b (b ≠ 0)` で, `a / b` とかける.
theorem step2 (s : ℝ): (∃ r : ℚ, s = r) ↔
(∃ a : ℤ, ∃ b : ℤ, b ≠ 0 ∧ (Int.natAbs a).Coprime (Int.natAbs b) ∧ s = a / b) :=by
  constructor
  . rintro ⟨r, sr⟩
    use r.num, r.den
    rw[sr]
    have h2 : r = r.num / r.den :=by exact Eq.symm (Rat.num_div_den r)
    nth_rw 3[h2]
    constructor
    . apply Int.ofNat_ne_zero.mpr
      exact r.den_nz
    . constructor
      . rw[← h2]
        exact r.reduced
      . exact Field.ratCast_def r
  . rintro ⟨a, b, bn0, acopb, sab⟩
    use a / b
    rw[sab, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]

example : Irrational √2 :=by
  by_contra h
  rw[step1] at h
  rw[step2] at h
  sorry

-- ワシ「以下に, Mathlibにかかれているものをみつけられるか,
--      また上手く `apply?` を使えるかが鍵になる. 今日はここまで!」
