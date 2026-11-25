import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.LinearAlgebra.Basis

/-! The affine blocking bound, with a finite-field polynomial proof. -/
namespace BlockingCurves

open MvPolynomial
open scoped BigOperators

variable {K V ι : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- A set meeting every affine hyperplane needs at least 1 + n (|K| - 1) points. -/
theorem lower_of_hyperplaneHits (b : Basis ι K V) (S : Finset V) (hS : S.Nonempty)
    (hit : ∀ (l : V →ₗ[K] K), l ≠ 0 → ∀ y, ∃ s ∈ S, l s = y) :
    (Fintype.card K - 1) * Fintype.card ι + 1 ≤ S.card := by
  classical
  obtain ⟨a, ha⟩ := hS
  let L (v : V) : MvPolynomial ι K := ∑ i, C (b.equivFun v i) * X i
  have evL (x : ι → K) (v : V) : eval x (L v) = b.constr K x v := by
    simp [L, Basis.constr_apply_fintype, smul_eq_mul]
  have degL (v : V) : (L v).totalDegree ≤ 1 := by
    apply (totalDegree_finset_sum _ _).trans
    apply Finset.sup_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simp)
  let f (s : V) : MvPolynomial ι K := 1 - L (s - a)
  let P := ∏ s ∈ S.erase a, f s
  have degP : P.totalDegree ≤ (S.erase a).card := by
    apply (totalDegree_finset_prod _ _).trans
    calc
      _ ≤ ∑ _s ∈ S.erase a, 1 := Finset.sum_le_sum fun s _ =>
        (totalDegree_sub _ _).trans (max_le (by simp) (degL (s-a)))
      _ = _ := by simp
  have value (x : ι → K) :
      eval x P = if x = 0 then 1 else 0 := by
    by_cases hx : x = 0
    · subst x
      simp [P, f, L]
    · rw [if_neg hx]
      have hnonzero : b.constr K x ≠ (0 : V →ₗ[K] K) := by
        intro he
        exact hx ((b.constr K).injective (he.trans (map_zero _).symm))
      obtain ⟨s, hs, hval⟩ := hit _ hnonzero (1 + b.constr K x a)
      have hsa : s ≠ a := by
        intro he
        subst s
        exact one_ne_zero (add_left_eq_self.mp hval.symm)
      change eval x (∏ t ∈ S.erase a, f t) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero_iff.mpr
      refine ⟨s, Finset.mem_erase.mpr ⟨hsa, hs⟩, ?_⟩
      simp [f, evL, map_sub, hval]
  by_contra! h
  have hcard := Finset.card_erase_of_mem ha
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hdeg : P.totalDegree < (Fintype.card K - 1) * Fintype.card ι := by omega
  have hz := P.sum_eval_eq_zero hdeg
  simp_rw [value] at hz
  simp at hz

end BlockingCurves

