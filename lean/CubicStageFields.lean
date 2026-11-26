import CubicRepairBranch
import CubicRepairDegree

/-! The stages in the Castelnuovo–Severi application. All roots lie in one
actual common branch. The relative degrees are those of the two subfields
inside their compositum, over the original constant field as well. -/
namespace BlockingCurves.CubicRepairGeometry
open Finset IntermediateField FiniteDimensional CubicAlteration CubicRepairPlaces
universe u
variable {F : Type u} [Field F] {R : Finset (Line F)}

noncomputable def stage (D : Branch F R) (S : Finset R) : IntermediateField (RatFunc F) D.K :=
  adjoin (RatFunc F) (D.root '' (S : Set R))

/-- Relative degree after adding the roots in T over the stage for S. -/
noncomputable def relativeDegree (D : Branch F R) (S T : Finset R) : ℕ :=
  finrank (stage D S) (adjoin (stage D S) (D.root '' (T : Set R)))

section
variable [DecidableEq R]

theorem stage_union (D : Branch F R) (S T : Finset R) :
    stage D (S ∪ T) = stage D S ⊔ stage D T := by
  simp only [stage, coe_union, Set.image_union]
  exact (IntermediateField.gc.l_sup)

theorem stage_adjoin_union (D : Branch F R) (S T : Finset R) :
    (adjoin (stage D S) (D.root '' (T : Set R))).restrictScalars (RatFunc F) = stage D (S ∪ T) := by
  simp only [stage, coe_union, Set.image_union, adjoin_adjoin_left]

/-- View an ambient subfield inside the compositum. When it is contained in
the compositum, lifting back returns that original field. -/
def inside {B K : Type*} [Field B] [Field K] [Algebra B K]
    (E U : IntermediateField B K) : IntermediateField B U := E.comap U.val

theorem lift_inside {B K : Type*} [Field B] [Field K] [Algebra B K]
    {E U : IntermediateField B K} (h : E ≤ U) : U.lift (inside E U) = E := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩; exact hz
  · intro hx
    exact ⟨⟨x,h hx⟩,hx,rfl⟩

private theorem sup_subfield {B K : Type*} [Field B] [Field K] [Algebra B K]
    (E L : IntermediateField B K) :
    (E ⊔ L).toSubfield = E.toSubfield ⊔ L.toSubfield := by
  let W := E.toSubfield ⊔ L.toSubfield
  let M : IntermediateField B K := W.toIntermediateField (by
    intro b
    exact (le_sup_left : E.toSubfield ≤ W) (E.algebraMap_mem b))
  apply le_antisymm
  · change E ⊔ L ≤ M
    exact sup_le (show E.toSubfield ≤ W from le_sup_left) (show L.toSubfield ≤ W from le_sup_right)
  · exact sup_le (show E ≤ E ⊔ L from le_sup_left) (show L ≤ E ⊔ L from le_sup_right)

/-- Even with all base-field structure forgotten, these are two subfields of
the joined stage and their field compositum is the entire joined stage. -/
theorem stage_compositum_top (D : Branch F R) (S T : Finset R) :
    let U := stage D (S ∪ T)
    (inside (stage D S) U).toSubfield ⊔ (inside (stage D T) U).toSubfield = ⊤ := by
  dsimp only
  let U := stage D (S ∪ T)
  have he : stage D S ≤ U := by change stage D S ≤ stage D (S ∪ T); rw [stage_union]; exact le_sup_left
  have hf : stage D T ≤ U := by change stage D T ≤ stage D (S ∪ T); rw [stage_union]; exact le_sup_right
  have ht : inside (stage D S) U ⊔ inside (stage D T) U = ⊤ := by
    apply U.lift_injective
    rw [lift_top, lift, IntermediateField.map_sup]
    change U.lift (inside (stage D S) U) ⊔ U.lift (inside (stage D T) U) = U
    rw [lift_inside he,lift_inside hf]
    exact (stage_union D S T).symm
  rw [← sup_subfield,ht,top_toSubfield]

/-- Carrier of the pulled-back subfield, with both inclusions explicit. -/
abbrev insideField {B K : Type*} [Field B] [Field K] [Algebra B K]
    (E U : IntermediateField B K) := {z : U // z ∈ inside E U}

local instance (priority := 2000) insideAlgebra {B K : Type*} [Field B] [Field K] [Algebra B K]
    (E U : IntermediateField B K) : Algebra (insideField E U) U :=
  (inside E U).val.toRingHom.toAlgebra

local instance (priority := 2000) insideModule {B K : Type*} [Field B] [Field K] [Algebra B K]
    (E U : IntermediateField B K) : Module (insideField E U) U :=
  (insideAlgebra E U).toModule

local instance (priority := 2000) insideTower {B K : Type*} [Field B] [Field K] [Algebra B K]
    (E U : IntermediateField B K) : IsScalarTower B (insideField E U) U :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private noncomputable def insideEquiv {B K : Type*} [Field B] [Field K] [Algebra B K]
    {E U : IntermediateField B K} (h : E ≤ U) : insideField E U ≃ₐ[B] E where
  toFun z := ⟨z.1.1,z.2⟩
  invFun z := ⟨⟨z.val,h z.property⟩,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The degree written with the genuine source and target fields of CS equals
the degree computed by adjoining the second list of roots over the first. -/
theorem stage_relative_finrank (D : Branch F R) (S T : Finset R) :
    let U := stage D (S ∪ T)
    FiniteDimensional (insideField (stage D S) U) U ∧
      finrank (insideField (stage D S) U) U = relativeDegree D S T := by
  let B := RatFunc F
  let E := stage D S
  let U := stage D (S ∪ T)
  let V := insideField E U
  let A := adjoin E (D.root '' (T : Set R))
  have finiteStage (L : Finset R) : FiniteDimensional B (stage D L) :=
    (CubicRepairDegree.generated_degree L D.root (fun i => RatFunc.C (i.val.1:F))
      (fun i => RatFunc.X + RatFunc.C i.val.2) (fun i _ => D.equation i)).1
  letI : FiniteDimensional B E := finiteStage S
  letI : FiniteDimensional B U := finiteStage _
  letI : FiniteDimensional E A :=
    (CubicRepairDegree.generated_degree T D.root (fun i => algebraMap B E (RatFunc.C (i.val.1:F)))
      (fun i => algebraMap B E (RatFunc.X+RatFunc.C i.val.2))
      (fun i _ => by simpa only [← IsScalarTower.algebraMap_apply B E D.K] using D.equation i)).1
  have hEU : E ≤ U := by change stage D S ≤ stage D (S ∪ T); rw [stage_union]; exact le_sup_left
  have hVU : FiniteDimensional V U := FiniteDimensional.right B V U
  refine ⟨hVU,?_⟩
  change finrank V U = finrank E A
  apply Nat.eq_of_mul_eq_mul_left (show 0 < finrank B V from finrank_pos)
  rw [finrank_mul_finrank B V U, (insideEquiv hEU).toLinearEquiv.finrank_eq, finrank_mul_finrank B E A]
  change finrank B U = finrank B (A.restrictScalars B)
  exact congrArg (fun L : IntermediateField (RatFunc F) D.K => finrank (RatFunc F) L)
    (stage_adjoin_union D S T).symm

end

/-- Exact constants descend to every stage of the tower. -/
theorem full_constants_stage (D : Branch F R) (H : CubicRepairBranch.FullConstants D)
    (E : IntermediateField (RatFunc F) D.K) :
    letI : Algebra F E := ((algebraMap (RatFunc F) E).comp RatFunc.C).toAlgebra
    ∀ x : E, IsAlgebraic F x → ∃ c : F, x = algebraMap F E c := by
  letI : Algebra F D.K := (constant D).toAlgebra
  letI : Algebra F E := ((algebraMap (RatFunc F) E).comp RatFunc.C).toAlgebra
  let j : E →ₐ[F] D.K := {E.val.toRingHom with commutes' := fun _ => rfl}
  intro x hx
  obtain ⟨a,ha⟩ := H (j x) (hx.algHom j)
  exact ⟨a,Subtype.ext ha⟩

end BlockingCurves.CubicRepairGeometry

