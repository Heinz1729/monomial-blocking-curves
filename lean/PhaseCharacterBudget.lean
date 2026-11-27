import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Pi

/-! Coordinate independence in a split fibre and the logarithmic range in
the two character-sum estimates for a cyclotomic Frobenius monomial. -/

namespace BlockingCurves.PhaseCharacter
open Finset Real
open scoped BigOperators

/-- The multiplicity contributed by one fibre coordinate is constant whenever
the sum of the multiplicities vanishes throughout the product. This applies
over ZMod m, also for composite m. -/
theorem coordinate_constant {ι K A : Type*} [Fintype ι] [AddCommGroup A]
    (v : ι → K → A) (zeroSum : ∀ x : ι → K, ∑ i, v i (x i) = 0)
    (i : ι) (u w : K) : v i u = v i w := by
  classical
  let f : ι → K := fun _ => w
  have hz := zeroSum (Function.update f i u)
  have hw := zeroSum f
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hz hw
  have he : ∑ j ∈ (Finset.univ.erase i), v j (Function.update f i u j) =
      ∑ j ∈ (Finset.univ.erase i), v j (f j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_noteq (Finset.mem_erase.mp hj).1]
  rw [he, Function.update_same] at hz
  exact add_left_cancel (hz.trans hw.symm)

/-- At most one branch can prescribe all coordinates of its rational kernel
fibre. The other branches have an unused value, forcing every weight to vanish. -/
theorem weights_vanish_with_one_full_branch {ι K A : Type*} [Fintype ι] [AddCommGroup A]
    (v : ι → K → A) (j : ι) (unused : ∀ i, i ≠ j → ∃ t, v i t = 0)
    (zeroSum : ∀ x : ι → K, ∑ i, v i (x i) = 0) : ∀ i t, v i t = 0 := by
  classical
  have ho (i : ι) (hi : i ≠ j) (t : K) : v i t = 0 := by
    obtain ⟨u, hu⟩ := unused i hi
    exact (coordinate_constant v zeroSum i t u).trans hu
  intro i t
  by_cases hij : i = j
  · subst i
    have hz := zeroSum (fun _ => t)
    rw [Finset.sum_eq_single j (fun k _ h => ho k h t) (by simp)] at hz
    exact hz
  · exact ho i hij t

/-- A common logarithmic budget for both reductions. L is log q and X the
logarithm of the field size on which the character sum is evaluated. -/
theorem pattern_budget {m l M : ℕ} (hm : 2 ≤ m) {L X : ℝ}
    (budget : (l:ℝ) * (32*(m:ℝ)^2*log m) ≤ L)
    (regime : (M ≤ 2*m*l ∧ L = X) ∨ (M ≤ m*l ∧ L ≤ 4*m*X))
    (hX : 0 ≤ X) : (M:ℝ)*log m ≤ X/8 := by
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < log (m:ℝ) := log_pos (by linarith)
  have hml : 0 ≤ (m:ℝ)*(l:ℝ)*log (m:ℝ) := by positivity
  rcases regime with ⟨h, rfl⟩ | ⟨h, hx⟩
  · have h' : (M:ℝ) ≤ 2*(m:ℝ)*l := by exact_mod_cast h
    nlinarith only [budget, mul_le_mul_of_nonneg_right h' hp.le,
      mul_nonneg (show 0 ≤ (m:ℝ)-1 by linarith) hml, hml]
  · have h' : (M:ℝ) ≤ (m:ℝ)*l := by exact_mod_cast h
    have hh : (m:ℝ)*l*log m ≤ X/8 := by
      apply le_of_mul_le_mul_left (a := (32:ℝ)*m) _ (by positivity)
      nlinarith only [budget, hx]
    exact (mul_le_mul_of_nonneg_right h' hp.le).trans hh

/-- An error C(1+log Q) Q^(3/4) is smaller than the normalized principal
term Q/m^M, with an explicit threshold uniform in M. -/
theorem main_term_dominates {Q C : ℝ} {m M : ℕ} (hq : 0 < Q) (hm : 2 ≤ m)
    (hC : 0 ≤ C) (threshold : 256*(C+1) ≤ log Q)
    (budget : (M:ℝ)*log m ≤ log Q/8) :
    C*(1+log Q)*exp (3*log Q/4) < Q/(m:ℝ)^M := by
  have hL : 1 ≤ log Q := by linarith
  have hm' : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hp := pow_div_factorial_le_exp (log Q/8) (by linarith) 2
  norm_num [Nat.factorial] at hp
  have he : C*(1+log Q) < exp (log Q/8) := by
    nlinarith only [hp, mul_nonneg (sub_nonneg.mpr threshold) (show 0 ≤ log Q by linarith),
      mul_nonneg hC (sub_nonneg.mpr hL), hL]
  have hmM : (m:ℝ)^M ≤ exp (log Q/8) := by
    calc
      _ = exp ((M:ℝ)*log m) := by rw [exp_nat_mul, exp_log hm']
      _ ≤ _ := exp_le_exp.mpr budget
  apply (lt_div_iff (pow_pos hm' _)).mpr
  calc
    C*(1+log Q)*exp (3*log Q/4)*(m:ℝ)^M
      < exp (log Q/8)*exp (3*log Q/4)*(m:ℝ)^M := by
        exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right he (exp_pos _)) (pow_pos hm' _)
    _ ≤ exp (log Q/8)*exp (3*log Q/4)*exp (log Q/8) :=
      mul_le_mul_of_nonneg_left hmM (by positivity)
    _ = Q := by rw [← exp_add, ← exp_add, show log Q/8 + 3*log Q/4 + log Q/8 = log Q by ring, exp_log hq]

/-- At the explicit field threshold both the root-separation union bound
and the character-sum error threshold hold, with C = 8m². For a base-field
slice X = log(q)/n, n < 4m; for the large-extension argument X = log(q). -/
theorem explicit_field_threshold {m X L : ℝ} (hm : 2 ≤ m)
    (fieldSize : 16384*m^5 ≤ L) (scale : L ≤ 4*m*X) :
    256*(8*m^2+1) ≤ X ∧ (4*m^2*X)^2 < exp X := by
  have core : 4096*m^4 ≤ X := by
    apply le_of_mul_le_mul_left (a := 4*m) _ (by linarith)
    nlinarith only [fieldSize,scale]
  have h2 : 1 ≤ m^2 := by nlinarith only [hm,sq_nonneg (m-1)]
  have h4 : m^2 ≤ m^4 := by nlinarith only [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg m)]
  have hx : 0 < X := by linarith
  constructor
  · nlinarith only [core,h2,h4]
  · have he := pow_div_factorial_le_exp X hx.le 3
    norm_num [Nat.factorial] at he
    calc
      (4*m^2*X)^2 = (16*m^4)*X^2 := by ring
      _ < (X/6)*X^2 := mul_lt_mul_of_pos_right (by nlinarith only [core,h4,h2]) (by positivity)
      _ = X^3/6 := by ring
      _ ≤ _ := he

end BlockingCurves.PhaseCharacter
