import Mathlib.FieldTheory.Adjoin

/-! Degree of the field obtained by choosing one root of each cubic in §17. -/
namespace BlockingCurves.CubicRepairDegree
open Polynomial IntermediateField FiniteDimensional

variable {B K : Type*} [Field B] [Field K] [Algebra B K]

private theorem one_root (x : K) (m c : B)
    (hx : x^3 = algebraMap B K m * x + algebraMap B K c) :
    FiniteDimensional B (adjoin B {x}) ∧ finrank B (adjoin B {x}) ≤ 3 := by
  let f : B[X] := C m * X + C c
  have hf : f.natDegree ≤ 2 := by
    apply natDegree_add_le_of_degree_le
    · exact natDegree_mul_le.trans (by simp)
    · simp
  let P : B[X] := X^3-f
  have hm : P.Monic := monic_X_pow_sub (degree_le_of_natDegree_le hf)
  have hz : aeval x P = 0 := by simp [P,f,hx]
  have hInt : IsIntegral B x := ⟨P,hm,hz⟩
  refine ⟨adjoin.finiteDimensional hInt,?_⟩
  rw [adjoin.finrank hInt]
  apply (natDegree_le_natDegree (minpoly.min B x hm hz)).trans
  exact (natDegree_sub_le _ _).trans (max_le (by simp) (by omega))

/-- Choosing one root per line gives a finite intermediate field of
degree at most three to the number of lines, with repeated roots allowed. -/
theorem generated_degree {I : Type*} (S : Finset I) (x : I → K) (m c : I → B)
    (hx : ∀ i ∈ S, (x i)^3 = algebraMap B K (m i)*x i + algebraMap B K (c i)) :
    FiniteDimensional B (adjoin B (x '' (S:Set I))) ∧
      finrank B (adjoin B (x '' (S:Set I))) ≤ 3^S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Set.image_empty, adjoin_empty]
    exact ⟨inferInstance, by simp only [IntermediateField.finrank_bot, Finset.card_empty, pow_zero, le_refl]⟩
  | @insert i S hi ih =>
    obtain ⟨hfinite,hdegree⟩ := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    let A := adjoin B (x '' (S:Set I))
    let D := adjoin A {x i}
    letI : FiniteDimensional B A := hfinite
    have heq : (x i)^3 = algebraMap A K (algebraMap B A (m i))*x i +
        algebraMap A K (algebraMap B A (c i)) := by
      simpa only [← IsScalarTower.algebraMap_apply B A K] using hx i (Finset.mem_insert_self i S)
    obtain ⟨hnew,hd⟩ := one_root (x i) (algebraMap B A (m i)) (algebraMap B A (c i)) heq
    letI : FiniteDimensional A D := hnew
    have hfield : D.restrictScalars B = adjoin B (x '' (↑(insert i S) : Set I)) := by
      rw [Finset.coe_insert,Set.image_insert_eq,← Set.singleton_union, Set.union_comm]
      exact adjoin_adjoin_left _ _ _
    rw [← hfield]
    have hfinite' : FiniteDimensional B D := FiniteDimensional.trans B A D
    refine ⟨hfinite',?_⟩
    change finrank B D ≤ _
    rw [← finrank_mul_finrank B A D, Finset.card_insert_of_not_mem hi,pow_succ]
    exact Nat.mul_le_mul hdegree hd

end BlockingCurves.CubicRepairDegree
