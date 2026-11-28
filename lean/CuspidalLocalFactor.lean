import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.EisensteinCriterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Tactic

/-! The completed zero fibre in the coordinate on the simple sheet.
Write h = a + u, and take b = u h^k, where k = d - 1.
The factor remaining after removal of X - h is Eisenstein at u. -/
namespace BlockingCurves.CuspidalLocal

open Polynomial

variable {K : Type*} [Field K]

/-- The complementary factor for the simple-sheet parameter u. -/
noncomputable def complement (u h : PowerSeries K) : ℕ → (PowerSeries K)[X]
  | 0 => 1
  | n+1 => X * complement u h n + C (u * h^n)

theorem factorization (a u : PowerSeries K) (n : ℕ) :
    let h := a+u
    (X-C h)*complement u h n = X^n*(X-C a)-C (u*h^n) := by
  dsimp only
  induction n with
  | zero => simp [complement]; ring
  | succ n ih =>
    rw [complement, mul_add, ←mul_assoc, mul_comm (X-C _) X, mul_assoc, ih]
    simp only [pow_succ, map_mul, map_add]
    ring

private theorem monic_degree (u h : PowerSeries K) (n : ℕ) :
    (complement u h n).Monic ∧ (complement u h n).degree = n := by
  induction n with
  | zero => simp [complement, monic_one]
  | succ n ih =>
    have deg : (X * complement u h n).degree = ↑(n+1 : ℕ) := by
      rw [degree_mul, degree_X, ih.2]; norm_cast; omega
    have lower : (C (u*h^n)).degree < (X * complement u h n).degree := by
      rw [deg]
      exact degree_C_le.trans_lt (by exact_mod_cast Nat.zero_lt_succ n)
    exact ⟨(monic_X.mul ih.1).add_of_left lower,
      (degree_add_eq_left_of_degree_lt lower).trans deg⟩

private theorem complement_reduction (h : PowerSeries K) (n : ℕ) :
    (complement PowerSeries.X h n).map (PowerSeries.constantCoeff K) = X^n := by
  induction n with
  | zero => simp [complement]
  | succ n ih => simp [complement, ih, pow_succ, mul_comm]

/-- Irreducibility of the complete complementary factor, including when
the characteristic divides its degree. The coefficient at zero has order one. -/
theorem complement_irreducible (a : K) (ha : a ≠ 0) (n : ℕ) :
    Irreducible ((complement PowerSeries.X (PowerSeries.C K a + PowerSeries.X) (n+1)).map
      (algebraMap (PowerSeries K) (LaurentSeries K))) := by
  let u : PowerSeries K := PowerSeries.X
  let h := PowerSeries.C K a + u
  let Q := complement u h (n+1)
  let P := Ideal.span ({u} : Set (PowerSeries K))
  have hP : P.IsPrime := (Ideal.span_singleton_prime (show u ≠ 0 from PowerSeries.X_ne_zero)).mpr
    PowerSeries.X_prime
  have hQ := monic_degree u h (n+1)
  apply (hQ.1.irreducible_iff_irreducible_map_fraction_map (K:=LaurentSeries K)).mp
  apply irreducible_of_eisenstein_criterion (P := P) hP
  · rw [hQ.1.leadingCoeff]
    exact fun hh => hP.ne_top ((Ideal.eq_top_iff_one P).2 hh)
  · intro j hj
    rw [hQ.2] at hj
    have hlt : j < n+1 := by exact_mod_cast hj
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, ←coeff_map, complement_reduction]
    simp [coeff_X_pow, Ne.symm hlt.ne, hlt.ne]
  · rw [hQ.2]; exact_mod_cast Nat.zero_lt_succ n
  · intro hh
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hh
    have hc : Q.coeff 0 = u*h^n := by simp [Q, complement, coeff_zero_eq_eval_zero]
    change u^2 ∣ Q.coeff 0 at hh
    rw [hc, sq] at hh
    have hu : u ∣ h^n := (mul_dvd_mul_iff_left (show u≠0 from PowerSeries.X_ne_zero)).1 hh
    rw [PowerSeries.X_dvd_iff] at hu
    simp [h, u, pow_ne_zero n ha] at hu
  · exact hQ.1.isPrimitive

/-- This factor stays separable even when its leading exponent vanishes in K.
For degree at least two its linear coefficient is u times a power of h. -/
theorem complement_separable (a : K) (ha : a ≠ 0) (n : ℕ) :
    ((complement PowerSeries.X (PowerSeries.C K a + PowerSeries.X) (n+1)).map
      (algebraMap (PowerSeries K) (LaurentSeries K))).Separable := by
  apply (separable_iff_derivative_ne_zero (complement_irreducible a ha n)).2
  intro e
  have c := congrArg (fun f : (LaurentSeries K)[X] => f.coeff 0) e
  dsimp only at c
  simp only [coeff_derivative, coeff_zero, Nat.zero_add, Nat.cast_zero, zero_add, mul_one,
    coeff_map] at c
  let h := PowerSeries.C K a + PowerSeries.X
  have hn : h ≠ 0 := by
    intro hh
    apply ha
    simpa [h] using congrArg (PowerSeries.constantCoeff K) hh
  have zero := (IsFractionRing.injective (PowerSeries K) (LaurentSeries K))
    (c.trans (map_zero _).symm)
  cases n with
  | zero => simp [complement] at zero
  | succ n =>
    have first : (complement PowerSeries.X h (n+1+1)).coeff 1 =
        PowerSeries.X*h^n := by
      simp only [complement, coeff_add, coeff_C, if_false, one_ne_zero,
        coeff_X_mul, zero_add, add_zero, coeff_zero_eq_eval_zero, eval_add,
        eval_mul, eval_X, eval_C, zero_mul, Nat.one_ne_zero]
    exact (mul_ne_zero PowerSeries.X_ne_zero (pow_ne_zero _ hn)) (first.symm.trans zero)

/-- Automorphisms of any normal overfield of the local field move any
complementary root to any other, fixing the Laurent base pointwise. -/
theorem local_root_transport (a : K) (ha : a ≠ 0) (n : ℕ)
    {E : Type*} [Field E] [Algebra (LaurentSeries K) E] [Normal (LaurentSeries K) E]
    (y z : E)
    (hy : aeval y ((complement PowerSeries.X (PowerSeries.C K a + PowerSeries.X) (n+1)).map
      (algebraMap (PowerSeries K) (LaurentSeries K))) = 0)
    (hz : aeval z ((complement PowerSeries.X (PowerSeries.C K a + PowerSeries.X) (n+1)).map
      (algebraMap (PowerSeries K) (LaurentSeries K))) = 0) :
    ∃ g : E ≃ₐ[LaurentSeries K] E, g y = z := by
  have irr := complement_irreducible a ha n
  have same := (minpoly.eq_of_irreducible irr hz).symm.trans (minpoly.eq_of_irreducible irr hy)
  exact (Normal.minpoly_eq_iff_mem_orbit E).mp same

end BlockingCurves.CuspidalLocal
