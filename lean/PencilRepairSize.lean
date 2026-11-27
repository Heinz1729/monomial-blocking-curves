import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A common numerical threshold for genus and pole-fibre bounds in every degree. -/
namespace BlockingCurves.PencilRepairSize
open Real

/-- Starting at the rational parameter field, the Castelnuovo--Severi
recurrence gives g_j ≤ j d^j. -/
theorem genus_bound {d : ℕ} (g : ℕ → ℕ) (h0 : g 0 = 0)
    (hstep : ∀ j, g (j+1) ≤ d*g j + (d-1)*d^j) (j : ℕ) : g j ≤ j*d^j := by
  induction j with
  | zero => simp [h0]
  | succ j ih =>
    apply (hstep j).trans
    calc
      _ ≤ d*(j*d^j)+d*d^j :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ih) (Nat.mul_le_mul_right _ (Nat.sub_le d 1))
      _ = _ := by ring

/-- The standard Hasse--Weil lower bound exceeds the number of poles even
when the number of prescribed lines grows as floor(log q / (4 log d)). -/
theorem point_budget {q : ℝ} (hq : 0 < q) (hL : 128 ≤ log q)
    {d t : ℕ} (hd : 2 ≤ d) (ht : t ≤ ⌊log q / (4*log (d:ℝ))⌋₊) :
    (d:ℝ)^t + 2*(t:ℝ)*(d:ℝ)^t * sqrt q < q+1 := by
  let L := log q
  let u := exp (L/4)
  have hL' : 128 ≤ L := hL
  have hL0 : 0 < L := by linarith
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
  rw [log_inv] at h2
  norm_num at h2
  have hlog : (1/2:ℝ) ≤ log (d:ℝ) := by linarith only [h2, log_le_log (by norm_num : (0:ℝ)<2) hd']
  have hpos : 0 < 4*log (d:ℝ) := by linarith
  have ht' : (t:ℝ)*(4*log (d:ℝ)) ≤ L := (le_div_iff hpos).1
    ((show (t:ℝ) ≤ ⌊log q / (4*log (d:ℝ))⌋₊ from by exact_mod_cast ht).trans
      (Nat.floor_le (div_nonneg hL0.le hpos.le)))
  have ht₀ : 0 ≤ (t:ℝ) := Nat.cast_nonneg _
  have htL : 2*(t:ℝ) ≤ L := by linarith only [ht',mul_le_mul_of_nonneg_left hlog ht₀]
  have hu : L+4 ≤ u := by
    have he := pow_div_factorial_le_exp (L/4) (show 0 ≤ L/4 by positivity) 2
    norm_num [Nat.factorial] at he
    dsimp [u]
    nlinarith only [he, mul_nonneg (by linarith : 0 ≤ L-128) hL0.le, hL']
  have hu' : 2 ≤ u := by linarith
  have hdpos : (0:ℝ) < d := by linarith
  have hpower : (d:ℝ)^t ≤ u := by
    calc
      _ = exp ((t:ℝ)*log (d:ℝ)) := by rw [exp_nat_mul, exp_log hdpos]
      _ ≤ _ := exp_le_exp.mpr (by linarith only [ht'])
  have hqeq : u^4 = q := by
    dsimp [u,L]
    rw [← exp_nat_mul]
    norm_num
    convert exp_log hq using 2
    ring
  have hsqrt : sqrt q = u^2 := by
    apply (sqrt_eq_iff_sq_eq (by positivity) (sq_nonneg _)).2
    simpa only [← pow_mul] using hqeq
  have hp : 2*(t:ℝ)*(d:ℝ)^t ≤ (u-2)*u := by
    apply mul_le_mul (by linarith) hpower (by positivity) (by linarith)
  rw [hsqrt, ← hqeq]
  nlinarith only [hpower, mul_le_mul_of_nonneg_right hp (sq_nonneg u),
    mul_nonneg (by linarith : 0 ≤ u-2) (sq_nonneg u), sq_nonneg (u-1), hu']

end BlockingCurves.PencilRepairSize
