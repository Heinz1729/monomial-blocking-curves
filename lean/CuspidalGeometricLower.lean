import CuspidalGenericAction
import CuspidalZeroCluster
import CuspidalSheetAction

/-! The all-characteristic bound with the actual geometric monodromy group.
Root permutations are derived from the automorphisms of the common splitting
field over the algebraic closure of the constant field. -/
namespace BlockingCurves.CuspidalGeneral

open Polynomial
noncomputable section

variable {F : Type*} [Field F]

private abbrev incl (F : Type*) [Field F] := algebraMap F (AlgebraicClosure F)

private def geometricShifts (S : Finset F) : Finset (AlgebraicClosure F) :=
  S.map ⟨incl F,(incl F).injective⟩

/-- The product splitting field over the geometric rational function field. -/
abbrev GeometricSplitting (d : ℕ) (a : F) (S : Finset F) :=
  cuspCompositum d (incl F a) (geometricShifts S)

private abbrev sheets (d : ℕ) (a : F) (S : Finset F) (i : S) :=
  (cuspCoordinate d (incl F a) (incl F i.val)).rootSet (GeometricSplitting d a S)

private theorem shifted_mem (S : Finset F) (i : S) : incl F i.val ∈ geometricShifts S :=
  Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩

private def rootLabel {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a≠0) (S : Finset F) (i : S) :
    Fin d ≃ sheets d a S i := by
  classical
  apply Equiv.symm
  apply Fintype.equivFinOfCardEq
  rw [card_rootSet_eq_natDegree (cuspCoordinate_separable hd ((_root_.map_ne_zero (incl F)).mpr ha) _)
    (coordinate_splits_in_compositum (by omega) _ _ (shifted_mem S i))]
  exact cuspCoordinate_natDegree (by omega) _ _

private def rootRestriction {K E : Type*} [Field K] [Field E] [Algebra K E] {P : K[X]}
    (nz : P≠0) (g : E ≃ₐ[K] E) : Equiv.Perm (P.rootSet E) := by
  let lift (σ : E ≃ₐ[K] E) (x : P.rootSet E) : P.rootSet E :=
    ⟨σ x.val,(mem_rootSet_of_ne nz).mpr (by
      rw [aeval_algHom_apply σ x.val P,(mem_rootSet_of_ne nz).mp x.property,map_zero])⟩
  exact { toFun := lift g
          invFun := lift g.symm
          left_inv := fun x => Subtype.ext (g.symm_apply_apply x.val)
          right_inv := fun x => Subtype.ext (g.apply_symm_apply x.val) }

/-- Geometric automorphisms act in all coordinates via arbitrary fixed
labellings of their actual d-element root sets. -/
def geometricRootAction {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a≠0) (S : Finset F) :
    (GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S) →*
    (S → Equiv.Perm (Fin d)) where
  toFun g i := (rootLabel hd ha S i).trans
    ((rootRestriction (cuspCoordinate_irreducible (by omega : 2 ≤ d) (incl F a) (incl F i.val)).ne_zero
      g).trans (rootLabel hd ha S i).symm)
  map_one' := by
    funext i
    apply Equiv.ext
    intro x
    exact (rootLabel hd ha S i).symm_apply_apply x
  map_mul' := by
    intro g h
    funext i
    apply Equiv.ext
    intro x
    change (rootLabel hd ha S i).symm _ = (rootLabel hd ha S i).symm _
    apply (rootLabel hd ha S i).symm.injective.eq_iff.mpr
    apply Subtype.ext
    change g (h ((rootLabel hd ha S i x).val)) = g ((rootLabel hd ha S i
      ((rootLabel hd ha S i).symm _)).val)
    rw [Equiv.apply_symm_apply]
    rfl

private theorem rootLabel_action {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a≠0)
    (S : Finset F) (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)]
      GeometricSplitting d a S) (i : S) (x : Fin d) :
    (rootLabel hd ha S i (geometricRootAction hd ha S g i x)).val =
      g (rootLabel hd ha S i x).val := by
  change ((rootLabel hd ha S i) ((rootLabel hd ha S i).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Finite branch separation survives passage to the algebraic closure of
the constants, including when the extra critical value is zero. -/
private theorem separation_maps {d : ℕ} {a u v : F}
    (sep : Disjoint ({-u,extraCritical d a-u} : Set F) {-v,extraCritical d a-v}) :
    Disjoint ({-(incl F u),extraCritical d (incl F a)-incl F u} : Set (AlgebraicClosure F))
      {-(incl F v),extraCritical d (incl F a)-incl F v} := by
  simpa [Set.image_insert_eq,extraCritical] using
    Set.disjoint_image_of_injective (incl F).injective sep

/-- The twist criterion on the actual monodromy action. Point, genus and
specialization data are as in the root-tower criterion; transitivity and
the simultaneously supported root permutations are proved here. -/
theorem lower_of_geometric_root_tower [Fintype F] [DecidableEq F] {d : ℕ} (hd : 3 ≤ d)
    (S : Finset F) {a : F} (ha : a≠0)
    (separated : ∀ u ∈ S, ∀ v ∈ S, u≠v →
      Disjoint ({-u,extraCritical d a-u} : Set F) {-v,extraCritical d a-v})
    (σ : S → Equiv.Perm (Fin d)) (T : CuspidalTower.RootTower d S.card)
    (twist : ∀ g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S,
      ∃ P : TwistPointData d a S (σ*geometricRootAction hd ha S g),
        P.genus=T.genus S.card 0 ∧ P.degree=T.degree S.card 0)
    (hq : 16 ≤ (Fintype.card F:ℝ)) (blocks : Blocks d (S:Set F)) :
    (Real.log (Fintype.card F)-2*Real.log (Real.log (Fintype.card F))) /
      (2*Real.log (d.factorial:ℝ)) - Real.log (16*(d:ℝ))/Real.log (d.factorial:ℝ) < S.card := by
  classical
  let π := geometricRootAction hd ha S
  let e := rootLabel hd ha S
  have move_eq (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S) (i : S) (x y : Fin d)
      (h : g (e i x).val = (e i y).val) : π g i x=y := by
    apply (e i).injective
    apply Subtype.ext
    exact (rootLabel_action hd ha S g i x).trans h
  apply lower_of_inertia_root_tower hd S a π.range _ _ σ T _ hq blocks
  · intro i x y
    obtain ⟨g,h⟩ := compositum_coordinate_transitive (by omega : 2 ≤ d) (incl F a)
      (incl F i.val) (geometricShifts S) (e i x) (e i y)
    exact ⟨⟨π g,g,rfl⟩,move_eq g i x y h⟩
  · intro i
    obtain ⟨r,hr,move⟩ := CuspidalLocal.supported_global_transport (K:=AlgebraicClosure F) (a:=incl F a) (α:=incl F i.val) hd
      ((_root_.map_ne_zero (incl F)).mpr ha) (geometricShifts S) (shifted_mem S i) (by
        intro v hv neq
        obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
        exact separation_maps (separated i.val i.property w hw (fun h => neq (by rw [←h];rfl))))
    let j := (e i).symm ⟨r,hr⟩
    have ej : (e i j).val=r := congrArg Subtype.val ((e i).apply_symm_apply ⟨r,hr⟩)
    refine ⟨j,?_⟩
    intro y z hy hz
    have away (v : Fin d) (hn : v≠j) : (e i v).val≠r := by
      intro h
      exact hn ((e i).injective (Subtype.ext (h.trans ej.symm)))
    obtain ⟨g,fixed,send,off⟩ := move _ (e i y).property _ (e i z).property (away y hy) (away z hz)
    refine ⟨⟨π g,g,rfl⟩,?_,move_eq g i j j (by rw [ej];exact fixed),move_eq g i y z send⟩
    intro w hw
    apply Equiv.ext
    intro t
    apply move_eq g w t t
    apply off _ (shifted_mem S w) _ _ (e w t).property
    exact ((incl F).injective.ne (fun h => hw (Subtype.ext h)))
  · rintro ⟨_,g,rfl⟩
    exact twist g

/-- Choose the nonzero base-field slope internally. Only the arithmetic
Frobenius lift, root tower, and geometric information on its twists must
be supplied at allowable slopes. -/
theorem lower_of_twist_geometry [Fintype F] [DecidableEq F] {d : ℕ} (hd : 3 ≤ d)
    (S : Finset F) (room : 1+S.offDiag.card*d < Fintype.card F)
    (geometry : ∀ (a : F) (ha : a≠0), (∀ u ∈ S, ∀ v ∈ S, u≠v →
        Disjoint ({-u,extraCritical d a-u} : Set F) {-v,extraCritical d a-v}) →
      ∃ (σ : S → Equiv.Perm (Fin d)) (T : CuspidalTower.RootTower d S.card),
        ∀ g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S,
          ∃ P : TwistPointData d a S (σ*geometricRootAction hd ha S g),
            P.genus=T.genus S.card 0 ∧ P.degree=T.degree S.card 0)
    (hq : 16 ≤ (Fintype.card F:ℝ)) (blocks : Blocks d (S:Set F)) :
    (Real.log (Fintype.card F)-2*Real.log (Real.log (Fintype.card F))) /
      (2*Real.log (d.factorial:ℝ)) - Real.log (16*(d:ℝ))/Real.log (d.factorial:ℝ) < S.card := by
  let c := ((d-1:ℕ):F)/(d:F)
  obtain ⟨a,ha,sep⟩ := exists_separating_slope (by omega : 0<d) S (c^d-c^(d-1)) room
  obtain ⟨σ,T,tw⟩ := geometry a ha sep
  exact lower_of_geometric_root_tower hd S ha sep σ T tw hq blocks

end
end BlockingCurves.CuspidalGeneral
