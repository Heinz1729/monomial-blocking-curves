import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace
import Mathlib.RingTheory.Norm
import Mathlib.Tactic.ComputeDegree

/-! In every cubic extension of finite fields, the norm of the trace-zero
plane takes every value in the base field. -/
namespace BlockingCurves.NormPencil
noncomputable section
open Polynomial
open scoped Polynomial

/-- Varying the linear coefficient of a depressed cubic with fixed nonzero
constant term excludes at most one coefficient per nonzero base-field element. -/
theorem exists_irreducible_depressed_cubic {F : Type*} [Field F] [Fintype F]
    (a : F) (ha : a ≠ 0) :
    ∃ c : F, Irreducible (X^3 + (C c*X - C a) : F[X]) := by
  classical
  let bad : Fˣ → F := fun u => (a-(u:F)^3)/(u:F)
  have hs : ¬Function.Surjective bad := by
    intro hs
    have he := Fintype.card_le_of_surjective bad hs
    rw [Fintype.card_units] at he
    have hq := Fintype.card_pos (α := F)
    omega
  unfold Function.Surjective at hs
  push_neg at hs
  obtain ⟨c,hc⟩ := hs
  let P : F[X] := X^3+(C c*X-C a)
  have hd : P.natDegree = 3 := by dsimp [P]; compute_degree <;> norm_num
  refine ⟨c, (irreducible_iff_roots_eq_zero_of_degree_le_three (p := P) (by omega) (by omega)).2 ?_⟩
  apply Multiset.eq_zero_iff_forall_not_mem.2
  intro x hx
  have hv := (mem_roots (p := P) (fun hz => by simp [hz] at hd)).1 hx
  change P.eval x = 0 at hv
  simp [P] at hv
  by_cases hx0 : x = 0
  · simp [hx0, ha] at hv
  · apply hc (Units.mk0 x hx0)
    change (a-x^3)/x = c
    apply (div_eq_iff hx0).2
    linear_combination -hv

/-- The two extensions split the same polynomial over their *given base field*.
This supplies an algebra isomorphism respecting all of its elements. -/
def sameCardEquiv (F K E : Type*) [Field F] [Field K] [Field E]
    [Fintype K] [Fintype E] [Algebra F K] [Algebra F E] (hc : Fintype.card K = Fintype.card E) :
    K ≃ₐ[F] E := by
  let P : F[X] := X ^ Fintype.card K - X
  letI : IsSplittingField F E P := by
    dsimp [P]
    rw [hc]
    infer_instance
  exact (IsSplittingField.algEquiv K P).trans (IsSplittingField.algEquiv E P).symm

/-- Realize a monic irreducible polynomial of the extension degree at a root
in the given field, with trace and norm given by its two distinguished coefficients. -/
theorem realize_monic (F E : Type*) [Field F] [Field E] [Fintype F] [Fintype E]
    [Algebra F E] [FiniteDimensional F E] (P : F[X]) (hi : Irreducible P) (hm : P.Monic)
    (hd : P.natDegree = FiniteDimensional.finrank F E) :
    ∃ x : E, Algebra.trace F E x = -P.nextCoeff ∧
      Algebra.norm F x = (-1)^(FiniteDimensional.finrank F E)*P.coeff 0 := by
  classical
  letI : Fact (Irreducible P) := ⟨hi⟩
  let pb := AdjoinRoot.powerBasis hm.ne_zero
  letI : FiniteDimensional F (AdjoinRoot P) := FiniteDimensional.of_fintype_basis pb.basis
  letI : Fintype (AdjoinRoot P) := FiniteDimensional.fintypeOfFintype F _
  have hdim : pb.dim = FiniteDimensional.finrank F E := hd
  have hcard : Fintype.card (AdjoinRoot P) = Fintype.card E := by
    rw [card_eq_pow_finrank (K := F), card_eq_pow_finrank (K := F) (V := E),
      FiniteDimensional.finrank_eq_card_basis pb.basis, Fintype.card_fin, hdim]
  let e := sameCardEquiv F (AdjoinRoot P) E hcard
  refine ⟨e pb.gen, ?_, ?_⟩
  · rw [Algebra.trace_eq_of_algEquiv, pb.trace_gen_eq_nextCoeff_minpoly,
      AdjoinRoot.minpoly_powerBasis_gen_of_monic hm]
  · rw [Algebra.norm_eq_of_algEquiv, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
      AdjoinRoot.minpoly_powerBasis_gen_of_monic hm, hdim]

/-- A root of the irreducible cubic has trace minus its quadratic coefficient
and norm minus its constant coefficient. The conclusion includes characteristic
three and the zero norm. -/
theorem exists_trace_zero_norm (F E : Type*) [Field F] [Field E] [Fintype F] [Fintype E]
    [Algebra F E] [FiniteDimensional F E] (hn : FiniteDimensional.finrank F E = 3) (a : F) :
    ∃ x : E, Algebra.trace F E x = 0 ∧ Algebra.norm F x = a := by
  classical
  by_cases ha : a = 0
  · exact ⟨0, map_zero _, by rw [Algebra.norm_zero, ha]⟩
  obtain ⟨c, hi⟩ := exists_irreducible_depressed_cubic a ha
  let P : F[X] := X^3+(C c*X-C a)
  have hd : P.natDegree = 3 := by dsimp [P]; compute_degree <;> norm_num
  have hm : P.Monic := by
    apply monic_X_pow_add
    compute_degree
    norm_num
  obtain ⟨x,htr,hN⟩ := realize_monic F E P hi hm (hd.trans hn.symm)
  refine ⟨x, ?_, ?_⟩
  · rw [htr, nextCoeff_of_natDegree_pos (by omega), hd]
    simp [P, coeff_X_pow, coeff_C_mul_X, coeff_C]
  · rw [hN, hn]
    norm_num [P, coeff_X_pow, coeff_C_mul_X]

end
end BlockingCurves.NormPencil
