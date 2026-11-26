import CubicRationalGenus
import CubicRepairPlaces

/-! Transport of regular Kähler differentials along a change of function
field presentation. In particular the final stage and the branch field have
the same genus, with their specified embeddings of the constant field. -/
noncomputable section
namespace BlockingCurves.CubicRationalGenus

open KaehlerDifferential IntermediateField
universe u
variable {F K L : Type u} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

private def transportChart (e : K ≃ₐ[F] L) (C : Chart F K) : Chart F L where
  A := C.A
  toField := e.toAlgHom.comp C.toField
  injective := e.injective.comp C.injective
  generates := by
    change adjoin F (Set.range (e.toAlgHom ∘ C.toField)) = ⊤
    rw [Set.range_comp, ← adjoin_map, C.generates]
    apply eq_top_iff.mpr
    intro y _
    exact ⟨e.symm y, trivial, e.apply_symm_apply y⟩

private def formMap (e : K ≃ₐ[F] L) :
    KaehlerDifferential F K →ₗ[F] KaehlerDifferential F L := by
  letI : Algebra K L := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  exact (KaehlerDifferential.map F F K L).restrictScalars F

private theorem formMap_deriv (e : K ≃ₐ[F] L) (x : K) :
    formMap e (D F K x) = D F L (e x) := by
  letI : Algebra K L := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  exact map_D F F K L x

private theorem formMap_smul (e : K ≃ₐ[F] L) (a : K) (w : KaehlerDifferential F K) :
    formMap e (a • w) = e a • formMap e w := by
  letI : Algebra K L := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun c => (e.commutes c).symm
  change KaehlerDifferential.map F F K L (a • w) = _
  rw [map_smul]
  exact (algebraMap_smul L a _).symm

private theorem formMap_inverse (e : K ≃ₐ[F] L) (w : KaehlerDifferential F K) :
    formMap e.symm (formMap e w) = w := by
  have hw : w ∈ Submodule.span K (Set.range (D F K)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun v => formMap e.symm (formMap e v) = v) hw ?_ ?_ ?_ ?_
  · rintro _ ⟨a,rfl⟩; simp only [formMap_deriv, AlgEquiv.symm_apply_apply]
  · simp
  · intro x y hx hy; simp only [map_add, hx, hy]
  · intro a x hx; simp only [formMap_smul, AlgEquiv.symm_apply_apply, hx]

private theorem formMap_regular (e : K ≃ₐ[F] L) {w : KaehlerDifferential F K}
    (hw : w ∈ regularForms F K) : formMap e w ∈ regularForms F L := by
  rw [regularForms, Submodule.mem_iInf] at hw ⊢
  intro C
  have h := hw (transportChart e.symm C)
  refine Submodule.span_induction (p := fun v => formMap e v ∈ chartForms C) h ?_ ?_ ?_ ?_
  · rintro _ ⟨a,b,rfl⟩
    change formMap e (e.symm (C.toField a) • D F K (e.symm (C.toField b))) ∈ chartForms C
    rw [formMap_smul, formMap_deriv, e.apply_symm_apply, e.apply_symm_apply]
    exact Submodule.subset_span ⟨a,b,rfl⟩
  · simp
  · intro x y hx hy; rw [map_add]; exact (chartForms C).add_mem hx hy
  · intro a x hx; rw [map_smul]; exact (chartForms C).smul_mem a hx

/-- The induced isomorphism on global regular differentials uses the canonical
map on Kähler differentials on the function fields and transports every chart. -/
def regularFormsEquiv (e : K ≃ₐ[F] L) : regularForms F K ≃ₗ[F] regularForms F L where
  toFun w := ⟨formMap e w, formMap_regular e w.property⟩
  invFun w := ⟨formMap e.symm w, formMap_regular e.symm w.property⟩
  left_inv w := Subtype.ext (formMap_inverse e w)
  right_inv w := Subtype.ext (formMap_inverse e.symm w)
  map_add' x y := Subtype.ext (map_add (formMap e) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (formMap e) c x.val)

theorem genus_congr (e : K ≃ₐ[F] L) : genus F K = genus F L :=
  (regularFormsEquiv e).finrank_eq

theorem regularForms_finiteDimensional_congr (e : K ≃ₐ[F] L) :
    FiniteDimensional F (regularForms F K) ↔ FiniteDimensional F (regularForms F L) :=
  Module.Finite.equiv_iff (regularFormsEquiv e)

end BlockingCurves.CubicRationalGenus

namespace BlockingCurves.CubicRepairGeometry
open CubicAlteration CubicRepairPlaces CubicRationalGenus IntermediateField
universe u
variable {F : Type u} [Field F] {R : Finset (Line F)}

/-- Genus of the full stage equals genus of the branch itself over the same
constant field. -/
theorem full_stage_genus (D : Branch F R) :
    letI : Algebra F D.K := (constant D).toAlgebra
    let E := adjoin (RatFunc F) (D.root '' ((Finset.univ : Finset R) : Set R))
    letI : Algebra F E := ((algebraMap (RatFunc F) E).comp RatFunc.C).toAlgebra
    genus F E = genus F D.K := by
  letI : Algebra F D.K := (constant D).toAlgebra
  let E := adjoin (RatFunc F) (D.root '' ((Finset.univ : Finset R) : Set R))
  letI : Algebra F E := ((algebraMap (RatFunc F) E).comp RatFunc.C).toAlgebra
  have hE : E = ⊤ := by simpa only [E, Finset.coe_univ, Set.image_univ] using D.generated
  let eqv : E ≃ₐ[RatFunc F] D.K := (equivOfEq hE).trans IntermediateField.topEquiv
  apply genus_congr (F := F)
  exact AlgEquiv.ofRingEquiv (f := eqv.toRingEquiv) (fun a => eqv.commutes (RatFunc.C a))

end BlockingCurves.CubicRepairGeometry
