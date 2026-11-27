import PhaseConjugateOperators
import PhaseNormSlice

/-! The bounded-extension argument for a table of distinct nonzero coefficients.
The excluded products also rule out interchange of the two conjugates in degree two. -/
namespace BlockingCurves.PiecewiseNormSlice

open Finset NormPencil ExtensionPhase

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  [FiniteDimensional F E]

private theorem outside_powers_products (C : Finset Fˣ) (n : ℕ)
    (room : C.card+C.card^2 < Fintype.card F-1) :
    ∃ g : Fˣ, (∀ z ∈ C, g ≠ z^n) ∧ ∀ z ∈ C, ∀ w ∈ C, g ≠ z*w := by
  classical
  let P := C.image (fun z => z^n)
  let T := (C ×ˢ C).image (fun zw => zw.1*zw.2)
  have size : (P ∪ T).card < Fintype.card Fˣ := by
    rw [Fintype.card_units]
    apply lt_of_le_of_lt _ room
    exact (card_union_le _ _).trans (Nat.add_le_add card_image_le
      (card_image_le.trans (by simp [card_product,pow_two])))
  obtain ⟨g,hg⟩ : ∃ g : Fˣ, g ∉ P ∪ T := by
    by_contra! h
    rw [eq_univ_of_forall h,card_univ] at size
    exact (lt_irrefl _ size)
  refine ⟨g,fun z hz e => hg (mem_union_left _ (mem_image.mpr ⟨z,hz,e.symm⟩)),
    fun z hz w hw e => hg (mem_union_right _ ?_)⟩
  exact mem_image.mpr ⟨(z,w),mem_product.mpr ⟨hz,hw⟩,e.symm⟩

/-- There is one slope and one base-field slice on which the conjugate roots of
every shifted inverse branch are pairwise distinct, also for arbitrary repeated labels. -/
theorem separated_inverse_slice (C : Finset Fˣ) (S : Finset E)
    (hn : 2 ≤ FiniteDimensional.finrank F E)
    (scope : C.card+C.card^2 < Fintype.card F-1)
    (room : (C.card*FiniteDimensional.finrank F E*S.card)^2 < Fintype.card F) :
    let n := FiniteDimensional.finrank F E
    ∃ (a : Eˣ) (σ : E ≃ₐ[F] E) (A : C → E ≃ₗ[F] E) (u : E),
      (∀ x : E, σ x=x^Fintype.card F) ∧
      (∀ (z : C) (x : E), algebraMap F E (z.val:F)*σ (A z x)-(a:E)*A z x=x) ∧
      Function.Injective (fun i : (C × Fin n) × S =>
        -((σ^i.1.2.val) (A i.1.1 (u+i.2.val)) / (σ^i.1.2.val) (A i.1.1 1))) := by
  classical
  let n := FiniteDimensional.finrank F E
  let D := normExponent (Fintype.card F) n
  have size := card_eq_pow_finrank (K:=F) (V:=E)
  obtain ⟨g,hg,products⟩ := outside_powers_products C n scope
  obtain ⟨a,ha⟩ := norm_power_surjective (by omega : 0<n) size (g:F)
  have anz : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (normExponent_pos Fintype.card_pos (by omega : 0<n)).ne'] at ha
    exact ((map_ne_zero (algebraMap F E)).2 g.ne_zero) ha.symm
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let L (z : C) : E →ₗ[F] E := (z.val:F) • σ.toLinearEquiv.toLinearMap - LinearMap.mulLeft F a
  have lv (z : C) (x : E) : L z x=algebraMap F E (z.val:F)*σ x-a*x := by simp [L,Algebra.smul_def]
  have inj (z : C) : Function.Injective (L z) := by
    have diff : a^D ≠ (algebraMap F E (z.val:F))^D := by
      rw [show a^D=algebraMap F E (g:F) from ha,← map_pow,scalar_norm_power]
      exact fun e => hg z.val z.property (Units.ext ((algebraMap F E).injective e))
    simpa only [Function.Injective,lv,hσ] using branch_injective_of_norm_ne size _ _ diff
  let A (z : C) := (LinearEquiv.ofBijective (L z) ⟨inj z,Finite.surjective_of_injective (inj z)⟩).symm
  have inv (z : C) (x : E) : algebraMap F E (z.val:F)*σ (A z x)-a*A z x=x := by
    rw [← lv]
    exact (A z).symm_apply_apply x
  have ho : orderOf σ = n := relative_order σ hσ
  have hne : σ ≠ 1 := fun h => by simp [h] at ho; omega
  let U (i : (C × Fin n) × S) := (A i.1.1).trans (σ^i.1.2.val).toLinearEquiv
  have rigid (i j : (C × Fin n) × S) (c : E) (hp : ∀ x, U i x=c*U j x) :
      i.1 = j.1 := by
    have exc (sqId : σ^2=1) : a*σ a ≠ algebraMap F E ((i.1.1.val:F)*(j.1.1.val:F)) := by
      have dv := orderOf_dvd_of_pow_eq_one sqId
      have dim : n=2 := le_antisymm (ho ▸ Nat.le_of_dvd (by decide) dv) hn
      have he : a^D=a*σ a := by simp [D,dim,normExponent,hσ,pow_add]
      intro same
      exact products _ i.1.1.property _ j.1.1.property (Units.ext
        ((algebraMap F E).injective (ha.symm.trans (he.trans same))))
    obtain ⟨h₁,h₂⟩ := inverse_branch_conjugates_rigid σ (σ^i.1.2.val) (σ^j.1.2.val)
      hne a anz (i.1.1.val:F) (j.1.1.val:F) j.1.1.val.ne_zero exc
      (A i.1.1).toEquiv (A j.1.1).toEquiv (inv _) (inv _) c hp
    exact Prod.ext (Subtype.ext (Units.ext h₂)) (Fin.ext (pow_injOn_Iio_orderOf
      (lt_of_lt_of_eq i.1.2.isLt ho.symm)
      (lt_of_lt_of_eq j.1.2.isLt ho.symm) h₁))
  have pairs (i j : (C × Fin n) × S) (ne : i ≠ j) :
      (¬ ∃ c : E, ∀ x : E, U i x = c*U j x) ∨ (U i=U j ∧ i.2.val ≠ j.2.val) := by
    by_cases h : i.1=j.1
    · right
      exact ⟨congrArg (fun k : C × Fin n => (A k.1).trans (σ^k.2.val).toLinearEquiv) h,
        fun e => ne (Prod.ext h (Subtype.ext e))⟩
    · exact Or.inl fun ⟨c,hp⟩ => h (rigid i j c hp)
  obtain ⟨u,hu⟩ := PhaseNormSlice.conjugate_roots_separate U (fun i => i.2.val)
    one_ne_zero pairs (by simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] using room)
  exact ⟨Units.mk0 a anz,σ,A,u,hσ,inv,hu⟩

end BlockingCurves.PiecewiseNormSlice
