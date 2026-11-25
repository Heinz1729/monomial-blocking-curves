import CubicSymmetry

namespace BlockingCurves

namespace Cubic47

abbrev F := ZMod 47
instance : Fact (Nat.Prime 47) := ⟨by decide⟩

private theorem cubeRoot (u : F) : (u^31)^3 = u := by
  revert u
  decide

/-- Normalize two members to 0 and 1 while preserving the cardinality and the
blocking property. Cubing permutes F₄₇, with inverse exponent 31. -/
theorem normalize_with_image (S : Finset F) (hs : GraphHits (fun x : F => x^3) (S : Set F))
    {a b : F} (ha : a ∈ S) (hb : b ∈ S) (hab : b ≠ a) :
    ∃ u c : F, u ≠ 0 ∧ ∃ V : Finset F, V = S.image (fun s => u*s+c) ∧
       V.card = S.card ∧ 0 ∈ V ∧ 1 ∈ V ∧
       GraphHits (fun x : F => x^3) (V : Set F) := by
  let u : F := (b-a)⁻¹
  have hu : u ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hab)
  let f : F → F := fun s => u*s - u*a
  have hf : Function.Injective f := by
    intro x y he
    change u*x - u*a = u*y - u*a at he
    exact (mul_right_inj' hu).mp (sub_left_inj.mp he)
  refine ⟨u, -(u*a), hu, S.image f, ?_, Finset.card_image_of_injective _ hf, ?_, ?_, ?_⟩
  · simp [f, sub_eq_add_neg]
  · exact Finset.mem_image.mpr ⟨a, ha, sub_self _⟩
  · refine Finset.mem_image.mpr ⟨b, hb, ?_⟩
    change u*b-u*a = 1
    rw [← mul_sub]
    exact inv_mul_cancel (sub_ne_zero.mpr hab)
  · have h := cubic_affine_image hs (pow_ne_zero 31 hu) (-u*a)
    rw [cubeRoot] at h
    simpa only [Finset.coe_image, f, neg_mul, sub_eq_add_neg] using h

theorem normalize (S : Finset F) (hs : GraphHits (fun x : F => x^3) (S : Set F))
    {a b : F} (ha : a ∈ S) (hb : b ∈ S) (hab : b ≠ a) :
    ∃ V : Finset F, V.card = S.card ∧ 0 ∈ V ∧ 1 ∈ V ∧
       GraphHits (fun x : F => x^3) (V : Set F) := by
  obtain ⟨_, _, _, V, _, hV⟩ := normalize_with_image S hs ha hb hab
  exact ⟨V, hV⟩

end Cubic47
end BlockingCurves
