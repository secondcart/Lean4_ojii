import Mathlib

-- 最終話「`√2` が無理数(後編その1)」

-- ワシ「まず, 現時点でどこまで証明が進んだか, おさらいだ.」
-- 1. `√2` が有理数と仮定する. (Clear)
-- 2. このとき, 互いに素な自然数 `p`, `q` から `√2 = q / p` とかける. (Clear)
-- 3. 両辺二乗して, 分母を払うと, `2 p^2 = q^2`. (Clear)
-- 4. 左辺は `2` の倍数だから, `q^2` は `2` の倍数, つまり, `q` も `2` の倍数. (Clear)
-- 5. `q^2` は `4` の倍数だから, `p^2` が `2` の倍数,つまり, `p` も `2` の倍数.
-- 6. `p`, `q` が互いに素に矛盾.

theorem step1 (x : ℝ) : ¬Irrational x ↔ ∃ r : ℚ, x = r :=by sorry

theorem step2 (s : ℝ): (∃ r : ℚ, s = r) ↔
(∃ a : ℤ, ∃ b : ℤ, b ≠ 0 ∧ (Int.natAbs a).Coprime (Int.natAbs b) ∧ s = a / b) :=by sorry

theorem step42 (z : ℤ): Even (z^2) → Even z :=by
  sorry

example (a b : ℝ) : Irrational √2 :=by
  by_contra h
  rw[step1, step2] at h
  rcases h with ⟨q,p,pn0,qcop, pq2⟩
  have step3 : (2 : ℝ) * p^2 = q^2 :=by
    rw[show 2 = √2 * √2 from by norm_num]
    rw[pq2]
    field_simp
    rw[← pow_two, ← pow_two]
  have step4 : Even q :=by
    apply step42
    dsimp [Even]
    use p^2
    rify
    rw[← step3]
    ring
  sorry

-- 5. `q^2` は `4` の倍数だから, `p^2` が `2` の倍数,つまり, `p` も `2` の倍数.

example (a b : ℝ) : Irrational √2 :=by
  by_contra h
  rw[step1, step2] at h
  rcases h with ⟨q,p,pn0,qcop, pq2⟩
  have step3 : (2 : ℝ) * p^2 = q^2 :=by
    rw[show 2 = √2 * √2 from by norm_num]
    rw[pq2]
    field_simp
    rw[← pow_two, ← pow_two]
  have step4 : Even q :=by
    apply step42
    dsimp [Even]
    use p^2
    rify
    rw[← step3]
    ring
  have step5 : Even p :=by
    have step52 : Even (p^2) :=by
      dsimp [Even]
      have step51 : ∃ z : ℤ, q^2 = 4 * z :=by
        dsimp [Even] at step4
        rcases step4 with ⟨r, qrr⟩
        use r^2
        rw[qrr]
        ring
      rcases step51 with ⟨r,q24r⟩
      rify at q24r
      rw[q24r, show (4 : ℝ) = 2 * 2 from by norm_num] at step3
      use r
      rify
      rw[← mul_two, ← mul_right_inj_of_invertible 2]
      nth_rw 3[mul_comm]
      rw[← mul_assoc]
      exact step3
    apply step42
    exact step52
  sorry

-- ワシ「もう少し上手い書き方があるかもだが, とりあえずできた.」
-- 学「いよいよ最後だね.」

-- 6. `p`, `q` が互いに素に矛盾.

-- ワシ「これは明日.」
-- 学「明日最終回!」


theorem ekiden (p : ℤ) : Even (p^2) → Even p :=by
  contrapose
  rw[Int.not_even_iff_odd]
  rw[Int.not_even_iff_odd]
  dsimp [Odd]
  intro h
  rcases h with ⟨ℓ, bbb⟩
  use 2 * ℓ^2 + 2 * ℓ
  rw[bbb]
  ring

theorem hatsuhinode (p : ℤ) : Even p → ∃ z : ℕ, p ^ 2 = 4 * z :=by
  intro a
  dsimp [Even] at a
  rcases a with ⟨r, bbb⟩
  use (Int.natAbs r)^2
  rw[bbb]
  rw[← two_mul]
  rw[pow_two]
  rw[← mul_assoc]
  rw[mul_assoc 2 r 2]
  rw[mul_comm r 2]
  rw[← mul_assoc]
  simp
  rw[mul_assoc]
  rw[← pow_two]

theorem nengajo (a b :ℤ) : 2 * a = 2 * b → a = b :=by simp only [mul_eq_mul_left_iff,
  OfNat.ofNat_ne_zero, or_false, imp_self]

theorem kakizome (p q : ℕ) (hp : Even p)(hq : Even q): ¬Nat.Coprime p q :=by
  rw[Nat.Prime.not_coprime_iff_dvd]
  use 2
  constructor
  . exact Nat.prime_two
  . constructor
    . exact even_iff_two_dvd.mp hp
    . exact even_iff_two_dvd.mp hq

example : Irrational √2 :=by
  by_contra ht
  rw[step1] at ht
  rw[step2] at ht
  rcases ht with ⟨p,q,ccc,ddd, eee⟩
  have h1 : √2 > 0 :=by norm_num
  have h2 : √2 * √2 = 2 :=by exact (Real.sqrt_eq_iff_mul_self_eq_of_pos h1).mp rfl
  have h3 : (2 : ℤ) * q^2 = p^2 :=by
    rify
    rw[← h2]
    rw[eee]
    field_simp
    rw[← pow_two]
    rw[← pow_two]
  have h4 : Even (p^2) :=by
    rw[← h3]
    dsimp [Even]
    use q^2
    ring
  have h5 :Even p :=by
    apply ekiden
    exact h4
  have h6 : ∃ z : ℕ, p ^ 2 = 4 * z := by
    apply hatsuhinode
    exact h5
  rcases h6 with ⟨s,ggg⟩
  have h7 : Even (q^2) :=by
    have h71 : q^2 = 2 * s :=by
      rw[ggg] at h3
      have h72 : (4 : ℤ)= 2 * 2 :=by exact rfl
      rw[h72] at h3
      apply nengajo
      rw[← mul_assoc]
      exact h3
    unfold Even
    use s
    rw[← two_mul]
    exact h71
  have h8 : Even q :=by
    exact ekiden q h7
  have h9 : Even (Int.natAbs p) :=by exact Int.natAbs_even.mpr h5
  have h10 : ¬Nat.Coprime (Int.natAbs p) (Int.natAbs q) :=by
    apply kakizome
    exact h9
    exact Int.natAbs_even.mpr h8
  contradiction

-- 学「なるほど, おじいちゃんすごいね! でも, 知らないコマンドがあったり,
--     変数が雑だったりするけど..., それと何で定理が正月関連なの?」
-- ワシ「...」
-- 学「それにね, おじいちゃん, 僕まだ7歳だよ?」
-- ワシ「...」
-- 学「おじいちゃん! おじいちゃん, どうしたの? おじいちゃん! おじいちゃん!」

-- 学「おじいちゃん!」
-- 目が覚めた... 病院?
-- 息子「おやじ, 大丈夫か? 学と一緒に山に行って, 倒れたらしいな. 若くないから, 気をつけろよ.」
-- そうじゃった, 学と一緒に出かけてた. ということは, あれは夢だったのか.
-- 大学生なのに, 妙に幼いと思ったら, 見た目だけ成長した学だったのか.
-- 息子「よかったよ. 学, お母さん呼んできて.」
-- 学「はーい.」
-- 息子「おやじ, 学に感謝しろよ. 急いで俺に電話してくれたぞ.」
-- 息子「しかし, 学は, 本当におやじが好きだな. 将来はおじいちゃんと数学の話がしたいから,
--      数学者になりたいって. それまで生きてろよ.」
-- ワシ「数学?」
-- 息子「あぁ. 将来どうするかな. 夫婦二人とも数学どころか算数もできないのに.」
-- ワシ「Lean4!」
-- 息子「?」
-- ワシ「Lean4を教えなさい. Lean4の良さを教えるのが, ワシの夢の続きだから.」

-- ご愛読ありがとうございました。
