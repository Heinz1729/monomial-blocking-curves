import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Integer choices for the two steps of the alteration in §17. -/
namespace BlockingCurves.CubicAlterationSize
open Real

private lemma log_three_bounds : (2/3:ℝ) ≤ log 3 ∧ log 3 ≤ 2 := by
  have h := log_le_sub_one_of_pos (show (0:ℝ) < 3⁻¹ by norm_num)
  rw [log_inv, inv_eq_one_div] at h
  exact ⟨by linarith, by linarith only [log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]⟩

/-- At most this many residual lines can be repaired using the genus test.
The floor still gives enough lines to save one full log-log term. -/
private theorem repair_size {q : ℝ} (hq : 0 < q) (hL : 128 ≤ log q) :
    ∃ t : ℕ, 0 < t ∧ log (log q) ≤ log t + 4 ∧
      (3:ℝ)^t + (2+(2*(t:ℝ)-1)*3^t)*sqrt q < q+1 := by
  let L := log q
  let t : ℕ := ⌊L/(4*log 3)⌋₊
  let u := exp (L/4)
  have hL' : 128 ≤ L := hL
  have hL0 : 0 < L := by linarith
  obtain ⟨hd,hd'⟩ := log_three_bounds
  have hd0 : 0 < 4*log 3 := by linarith
  have hi := Nat.floor_le (show 0 ≤ L/(4*log 3) by positivity)
  have htL : (t:ℝ)*(4*log 3) ≤ L := (le_div_iff hd0).mp hi
  have hLt : L < ((t:ℝ)+1)*(4*log 3) :=
    (div_lt_iff hd0).mp (Nat.lt_floor_add_one _)
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have htL' : 2*(t:ℝ)+4 ≤ L+4 := by
    linarith only [htL, mul_le_mul_of_nonneg_left hd ht0,ht0]
  have hLt' : L ≤ 16*(t:ℝ) := by
    linarith only [hLt, mul_le_mul_of_nonneg_left hd' (show (0:ℝ) ≤ (t:ℝ)+1 by positivity),hL']
  have htpos : (0:ℝ) < t := by linarith
  have ht1 : 1 ≤ t := by exact_mod_cast (Nat.pos_of_ne_zero (fun h => by simp [h] at htpos))
  have hu : L+4 ≤ u := by
    have h := pow_div_factorial_le_exp (L/4) (show 0 ≤ L/4 by positivity) 2
    norm_num [Nat.factorial] at h
    dsimp [u]
    nlinarith only [h, mul_nonneg (by linarith : 0 ≤ L-128) hL0.le, hL']
  have hu0 : 2 ≤ u := by linarith
  have hpower : (3:ℝ)^t ≤ u := by
    dsimp [u]
    rw [← exp_log (by norm_num : (0:ℝ) < 3), ← exp_nat_mul]
    exact exp_le_exp.mpr (by linarith only [htL])
  have hqeq : u^4 = q := by
    dsimp [u,L]
    rw [← exp_nat_mul]
    norm_num
    convert exp_log hq using 2
    ring
  have hsqrt : sqrt q = u^2 := by
    apply (sqrt_eq_iff_sq_eq (by positivity) (sq_nonneg _)).2
    simpa only [← pow_mul] using hqeq
  have hprod : (2*(t:ℝ)-1)*3^t ≤ (u-4)*u := by
    apply mul_le_mul (by linarith) hpower (by positivity)
    linarith
  refine ⟨t,ht1,?_,?_⟩
  · have hlog := log_le_log hL0 hLt'
    rw [log_mul (by norm_num) htpos.ne'] at hlog
    have hs : log (16:ℝ) = 4*log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, log_pow]; norm_num
    have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith only [hlog, hs, h2]
  · rw [hsqrt, ← hqeq]
    have hb := mul_le_mul_of_nonneg_right (add_le_add_left hprod 2) (sq_nonneg u)
    nlinarith only [hpower, hb, mul_nonneg (by linarith : 0 ≤ u-2) (sq_nonneg u),
      sq_nonneg (u-1),hu0]

/-- The residual-line budget, the Hasse--Weil positivity test, and the
total number of parameters after adjoining one common repair parameter. -/
theorem parameters {q : ℝ} (hq : 0 < q) (hL : 128 ≤ log q) :
    ∃ k t : ℕ, 0 < k ∧ 0 < t ∧ q^2*((q+1)/3)^k ≤ (t:ℝ)*q^k ∧
      (3:ℝ)^t + (2+(2*(t:ℝ)-1)*3^t)*sqrt q < q+1 ∧
      (k:ℝ)+1 ≤ (2*log q-log (log q))/log 3+17 := by
  obtain ⟨t,ht,hlogt,hgenus⟩ := repair_size hq hL
  obtain ⟨hd,_⟩ := log_three_bounds
  have hd0 : 0 < log 3 := by linarith
  have hL0 : 0 < log q := by linarith
  have hlL := log_le_sub_one_of_pos hL0
  have hlL0 := log_nonneg (show 1 ≤ log q by linarith)
  let a := (2*log q-log (log q))/log 3
  let k : ℕ := ⌊a⌋₊+16
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hd0.le
  have hka : (k:ℝ) ≤ a+16 := by
    dsimp [k]; push_cast; linarith only [Nat.floor_le ha0]
  have hak : a+15 < (k:ℝ) := by
    dsimp [k]; push_cast; linarith only [Nat.lt_floor_add_one a]
  have haid : a*log 3 = 2*log q-log (log q) := div_mul_cancel₀ _ hd0.ne'
  have hal : a ≤ 3*log q := by
    apply (div_le_iff hd0).mpr
    linarith only [mul_le_mul_of_nonneg_left hd hL0.le, hlL0]
  have hkq : (k:ℝ)/q ≤ 4 := by
    apply (div_le_iff hq).mpr
    linarith only [hka, hal, log_le_sub_one_of_pos hq,hL]
  have h1 : 0 < 1+q⁻¹ := by positivity
  have hrem : (k:ℝ)*log (1+q⁻¹) ≤ 4 := by
    rw [div_eq_mul_inv] at hkq
    linarith only [hkq,mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos h1) (Nat.cast_nonneg k)]
  have hlog : log (q+1) = log q+log (1+q⁻¹) := by
    rw [← log_mul hq.ne' h1.ne']; congr 1; field_simp
  refine ⟨k,t,by dsimp [k]; omega,ht,?_,hgenus,by linarith only [hka]⟩
  apply (log_le_log_iff (by positivity) (by positivity)).mp
  rw [log_mul (by positivity) (by positivity), log_pow, log_pow,
    log_div (by positivity) (by norm_num), log_mul (by positivity) (by positivity),
    log_pow, hlog]
  norm_num
  linarith only [mul_lt_mul_of_pos_right hak hd0,haid,hlogt,hd,hrem]

end BlockingCurves.CubicAlterationSize
