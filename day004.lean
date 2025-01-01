import Mathlib

-- 第四話「rw」

-- ワシ「今日もまずは, `rw` の説明に入る. 前回がこれ.」

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

-- ワシ「`rw` は, まとめてかくこともできる. ついでに, `variable` も教える.」

-- `variable`: 引数を共通化する
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

-- 学「カンマの後にカーソルを置くと, 次の段階が表示されるね.」

-- 学「`variable` で事前に宣言することで,
--     `example` の行に `(a b c d e f : ℝ)` が不要になっているの?」
-- ワシ「その通り.」
-- 学「`variable` で宣言したものはファイルの最後まで有効なの?」
-- ワシ「その通り, 途中で変えたいときとかは, `section` で区切ればよい.」

-- LBE
-- `section`: スコープを区切る
-- `end` で閉じる. `end` がないとファイルの終わりまで.
section
  variable(g : ℝ)

  -- 宣言したので有効
  #check g
end

-- `check_failure`: 意図的なエラー
#check_failure g

-- 学「`#check_failure` は, ファイルでエラーを出したくないけど,
--     エラーが起きるか確認できるから便利とか?」
-- ワシ「さす孫! その通り.」

-- ワシ「`mul_comm`, `mul_assoc` は昨日名前から推測できたが, もちろんわからないときもある.
--      そのときは, 以前教えた `#check` が便利だ.」

-- MIL
#check mul_comm a b
#check mul_assoc a b c

-- 学「`mul_assoc a b c : a * b * c = a * (b * c)` と出るけど,
--     型 `a * b * c = a * (b * c)` の証明が項 `mul_assoc a b c : a * b * c`
--     ということ?」
-- ワシ「よく覚えてたな. その通り. また, 以下のようにすることで,
--      型や定理が正しいことも確認できる(=正しくないとエラーが出る).」

#check (a : ℝ)
#check (mul_comm a b : a * b = b * a)

-- ワシ「次はこれ. `rw` はgoalに対してだけでなく, 仮定にも書き換えができる.」

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  -- `exact`: 証明を直接構成
  exact hyp

-- 学「`rw[*] at (仮定)` で, できるんだ! `exact` は何?」
-- ワシ「これもtacticで, goalが仮定と同じになったら,
--      仮定を指定することでgoalを閉じることができる.」

-- ワシ「`rw` に似たもので, `nth_rw` がある. `rw` は当てはまる項を全部変えるけど,
--       `nth_rw` は, 指定した項だけ変える.」

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

-- 学「単に `rw` だと, `(a + b) * (a + b)` が `c * c` になるけど, `nth_rw 2` で,
--     2個目だけ `c` になっている.」

-- ワシ「最後に `rw` で1点だけ. 昨日言ったように, `rw` は `=` だけでなく,
--       `↔` (`\iff` で打てる) にも使える. 今日はここまで.」
