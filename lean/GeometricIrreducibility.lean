import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.EisensteinCriterion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Ring

namespace BlockingCurves

open Polynomial

variable {K : Type*} [Field K]

/-- The homogeneous equation in coordinates 0 = X, 1 = Y, 2 = Z, monic in X. -/
noncomputable def monomialCurveForm (d : ℕ) (α : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 0 ^ d -
    (MvPolynomial.X 1 * MvPolynomial.X 2 ^ (d - 1) + MvPolynomial.C α * MvPolynomial.X 2 ^ d)

/-- Every monomial of the form has total degree `d`. -/
theorem monomialCurveForm_isHomogeneous (d : ℕ) (hd : 0 < d) (α : K) :
    (monomialCurveForm d α).IsHomogeneous d := by
  apply (MvPolynomial.isHomogeneous_X_pow _ _).sub
  apply MvPolynomial.IsHomogeneous.add _ (MvPolynomial.isHomogeneous_C_mul_X_pow α _ _)
  have h := (MvPolynomial.isHomogeneous_X (R := K) (σ := Fin 3) 1).mul
    (MvPolynomial.isHomogeneous_X_pow 2 (d - 1))
  rwa [show 1 + (d - 1) = d by omega] at h

/-- Its zero equation is precisely the curve equation tested in `ProjectiveBlocks`. -/
theorem monomialCurveForm_eval_eq_zero_iff (d : ℕ) (α x y z : K) :
    MvPolynomial.eval ![x, y, z] (monomialCurveForm d α) = 0 ↔
      y * z ^ (d - 1) = x ^ d - α * z ^ d := by
  simp [monomialCurveForm, sub_eq_zero, eq_sub_iff_add_eq, eq_comm]
  rw [sub_eq_iff_eq_add]

theorem irreducible_variable_binomial (d : ℕ) (hd : 0 < d) :
    Irreducible ((X : Polynomial (Polynomial K)) ^ d - C X) := by
  let P : Ideal (Polynomial K) := Ideal.span {X}
  have hP : P.IsPrime := (Ideal.span_singleton_prime X_ne_zero).2 prime_X
  apply irreducible_of_eisenstein_criterion (P := P) hP
  · rw [leadingCoeff_X_pow_sub_C hd]
    exact (Ideal.ne_top_iff_one P).1 hP.ne_top
  · intro n hn
    rw [degree_X_pow_sub_C hd] at hn
    have hnd : n ≠ d := ne_of_lt (WithBot.coe_lt_coe.1 hn)
    simp only [coeff_sub, coeff_X_pow, if_neg hnd, zero_sub, coeff_C]
    by_cases hn0 : n = 0
    · simpa [hn0, P] using (Ideal.subset_span (Set.mem_singleton X) : (X : Polynomial K) ∈ P)
    · simp [hn0]
  · simp [degree_X_pow_sub_C hd, hd]
  · intro h
    simp only [coeff_sub, coeff_X_pow, if_neg hd.ne, coeff_C_zero, zero_sub] at h
    have hx : (X : Polynomial K) ∈ P ^ 2 := (P ^ 2).neg_mem_iff.1 h
    rw [show P = Ideal.span {X} by rfl, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    have hc := X_pow_dvd_iff.mp hx 1 (by decide)
    simp at hc
  · exact (monic_X_pow_sub_C _ hd.ne').isPrimitive

/-- Valid over every coefficient field, including every algebraic extension. -/
theorem monomialCurveForm_irreducible (d : ℕ) (hd : 0 < d) (α : K) :
    Irreducible (monomialCurveForm d α) := by
  classical
  let e := MvPolynomial.finSuccEquiv K 2
  let a : MvPolynomial (Fin 2) K :=
    MvPolynomial.X 0 * MvPolynomial.X 1 ^ (d - 1) + MvPolynomial.C α * MvPolynomial.X 1 ^ d
  have hC : e (MvPolynomial.C α) = C (MvPolynomial.C α) := e.commutes α
  have hform : e (monomialCurveForm d α) = X ^ d - C a := by
    have hy : (1 : Fin 3) = (0 : Fin 2).succ := rfl
    have hz : (2 : Fin 3) = (1 : Fin 2).succ := rfl
    simp only [monomialCurveForm, map_sub, map_add, map_mul, map_pow, hy, hz, hC]
    simp only [e, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ, a,
      map_add, map_mul, map_pow]
  -- On the chart Z = 1, translating Y specializes the monic polynomial to X^d - T.
  let φ := MvPolynomial.eval₂Hom (C : K →+* Polynomial K) ![X - C α, 1]
  have ha : φ a = X := by
    simp [φ, a]
  have hmap : Irreducible (e (monomialCurveForm d α)) := by
    rw [hform]
    apply Monic.irreducible_of_irreducible_map φ _ (monic_X_pow_sub_C _ hd.ne')
    simpa [Polynomial.map_sub, ha] using (irreducible_variable_binomial (K := K) d hd)
  refine ⟨fun h => hmap.not_unit (h.map e), ?_⟩
  intro b c h
  have hh : e (monomialCurveForm d α) = e b * e c := by rw [h, map_mul]
  exact (hmap.isUnit_or_isUnit hh).imp
    (fun hb => by simpa using hb.map e.symm) (fun hc => by simpa using hc.map e.symm)

/-- Geometric irreducibility, expressed by scalar extension of the original form. -/
theorem monomialCurveForm_geometrically_irreducible (d : ℕ) (hd : 0 < d) (α : K) :
    Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (monomialCurveForm d α)) := by
  simpa [monomialCurveForm] using
    (monomialCurveForm_irreducible d hd (algebraMap K (AlgebraicClosure K) α))

end BlockingCurves
