import Mathlib.LinearAlgebra.Basis
import Mathlib.Data.Finset.Prod

/-! The origin and the nonzero points of the coordinate axes meet every affine
hyperplane. The explicit construction works in every characteristic. -/

namespace BlockingCurves

variable {K E ι : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E]
  [Fintype ι]

/-- Union of the coordinate axes, including the origin in dimension zero. -/
noncomputable def coordinateAxes (b : Basis ι K E) : Finset E := by
  classical
  let params := ((Finset.univ : Finset K).erase 0).product (Finset.univ : Finset ι)
  exact insert 0 (params.image (fun p : K × ι => p.1 • b p.2))

theorem coordinateAxes_card_le (b : Basis ι K E) :
    (coordinateAxes b).card ≤ (Fintype.card K - 1) * Fintype.card ι + 1 := by
  classical
  unfold coordinateAxes
  apply (Finset.card_insert_le _ _).trans
  apply Nat.add_le_add_right _ 1
  apply Finset.card_image_le.trans
  exact (Finset.card_product ((Finset.univ : Finset K).erase 0) (Finset.univ : Finset ι)).le.trans
    (by simp)

theorem coordinateAxes_hits (b : Basis ι K E) (l : E →ₗ[K] K) (hl : l ≠ 0)
    (y : K) : ∃ s ∈ coordinateAxes b, l s = y := by
  classical
  by_cases hy : y = 0
  · exact ⟨0, by simp [coordinateAxes], by simp [hy]⟩
  have hex : ∃ i : ι, l (b i) ≠ 0 := by
    by_contra h
    apply hl
    apply b.ext
    intro i
    change l (b i) = 0
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨(y / l (b i)) • b i, ?_, ?_⟩
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(y / l (b i), i), ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨div_ne_zero hy hi, Finset.mem_univ _⟩, Finset.mem_univ _⟩
  · rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hi]

/-- A blocking set of cardinality at most one plus dimension times field size
minus one, realized by the coordinate axes. -/
theorem exists_hyperplaneHits_le (b : Basis ι K E) :
    ∃ S : Finset E, S.card ≤ (Fintype.card K - 1) * Fintype.card ι + 1 ∧
      ∀ (l : E →ₗ[K] K), l ≠ 0 → ∀ y : K, ∃ s ∈ S, l s = y :=
  ⟨coordinateAxes b, coordinateAxes_card_le b, coordinateAxes_hits b⟩

#print axioms exists_hyperplaneHits_le

end BlockingCurves
