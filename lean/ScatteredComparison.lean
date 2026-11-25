import GeneralGeometry

/-! C. Zanella, *A condition for scattered linearized polynomials involving
Dickson matrices*, §1, pp. 2–3 (https://arxiv.org/abs/1909.07802). For
nonzero inputs a ratio collision is equivalent to spanning the same line
over the base field. The statement below uses a scalar multiple to express
equality of these lines. -/

namespace BlockingCurves

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]

/-- Source formulation in terms of slopes of nonzero vectors on the graph. -/
def ScatteredSlopes (T : F →ₗ[K] F) : Prop :=
  ∀ x y : F, x ≠ 0 → y ≠ 0 → (T x / x = T y / y ↔ ∃ c : K, c • x = y)

/-- The kernel criterion in the manuscript agrees with the slope criterion. -/
theorem scattered_iff_scatteredSlopes (T : F →ₗ[K] F) :
    Scattered T ↔ ScatteredSlopes T := by
  constructor
  · intro h x y hx hy
    constructor
    · intro he
      let m := T x / x
      let W := LinearMap.ker (T - LinearMap.mulLeft K m)
      have hmem (t : F) (ht : t ≠ 0) (heq : m = T t / t) : t ∈ W := by
        change T t - m * t = 0
        exact sub_eq_zero.mpr ((eq_div_iff ht).mp heq).symm
      let u : W := ⟨x, hmem x hx rfl⟩
      let v : W := ⟨y, hmem y hy he⟩
      have hu : u ≠ 0 := fun hz => hx (congrArg Subtype.val hz)
      have hdim : FiniteDimensional.finrank K W = 1 := by
        have hle : FiniteDimensional.finrank K W ≤ 1 := h m
        have hpos : 0 < FiniteDimensional.finrank K W :=
          FiniteDimensional.finrank_pos_iff.mpr (⟨⟨u, 0, hu⟩⟩ : Nontrivial W)
        omega
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' u hu).mp hdim v
      exact ⟨c, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc⟩
      apply (div_eq_div_iff hx hy).2
      rw [← hc, map_smul, Algebra.smul_def, Algebra.smul_def]
      ring
  · intro h m
    let W := LinearMap.ker (T - LinearMap.mulLeft K m)
    change FiniteDimensional.finrank K W ≤ 1
    by_cases hW : W = ⊥
    · exact (Submodule.finrank_eq_zero.mpr hW).le.trans (Nat.zero_le _)
    obtain ⟨x, hxW, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    refine finrank_le_one_iff.mpr ⟨⟨x, hxW⟩, ?_⟩
    intro v
    by_cases hv : (v : F) = 0
    · exact ⟨0, Subtype.ext (by simpa using hv.symm)⟩
    have hs (t : F) (ht : t ∈ W) (ht0 : t ≠ 0) : T t / t = m := by
      change T t - m * t = 0 at ht
      exact (div_eq_iff ht0).mpr (sub_eq_zero.mp ht)
    obtain ⟨c, hc⟩ := (h x v hx hv).mp ((hs x hxW hx).trans (hs v v.property hv).symm)
    exact ⟨c, Subtype.ext hc⟩

end BlockingCurves
