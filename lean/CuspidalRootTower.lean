import CuspidalGenericAction
import CuspidalZeroCluster

/-! Adjoin the distinct roots of each translate in order, inside the splitting
field of their product. The constants may in particular be algebraically closed. -/
namespace BlockingCurves.CuspidalRootTower

open Polynomial IntermediateField CuspidalGeneral
noncomputable section

variable {k : Type*} [Field k]

private def shifts (S : Finset k) : Fin S.card ≃ S :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm

def shift (S : Finset k) (i : Fin S.card) : k := (shifts S i).val

theorem shift_mem (S : Finset k) (i : Fin S.card) : shift S i ∈ S := (shifts S i).property

def sheetEquiv {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k) (i : Fin S.card) :
    Fin d ≃ (cuspCoordinate d a (shift S i)).rootSet (cuspCompositum d a S) := by
  classical
  apply Equiv.symm
  apply Fintype.equivFinOfCardEq
  rw [card_rootSet_eq_natDegree (cuspCoordinate_separable hd ha _)
    (coordinate_splits_in_compositum (by omega) _ _ (shift_mem S i))]
  exact cuspCoordinate_natDegree (by omega) _ _

def sheet {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k) (i : Fin S.card)
    (j : Fin d) : cuspCompositum d a S := (sheetEquiv hd ha S i j).val

theorem sheet_mem_rootSet {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k)
    (i : Fin S.card) (j : Fin d) :
    sheet hd ha S i j ∈ (cuspCoordinate d a (shift S i)).rootSet (cuspCompositum d a S) :=
  (sheetEquiv hd ha S i j).property

theorem sheet_injective {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k)
    (i : Fin S.card) : Function.Injective (sheet hd ha S i) :=
  fun _ _ h => (sheetEquiv hd ha S i).injective (Subtype.ext h)

theorem sheet_aeval {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k)
    (i : Fin S.card) (j : Fin d) :
    aeval (sheet hd ha S i j) (cuspCoordinate d a (shift S i)) = 0 :=
  (mem_rootSet.mp (sheet_mem_rootSet hd ha S i j)).2

private def rootPrefix {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k) (i j : ℕ) :
    Set (cuspCompositum d a S) :=
  {x | ∃ u : Fin S.card, ∃ r : Fin d, (u.val < i ∨ u.val = i ∧ r.val < j) ∧
    sheet hd ha S u r = x}

/-- After all coordinates with index less than i, adjoin the first j sheets of coordinate i. -/
def stage {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k) (i j : ℕ) :
    IntermediateField (RatFunc k) (cuspCompositum d a S) :=
  adjoin (RatFunc k) (rootPrefix hd ha S i j)

theorem sheet_mem_stage {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k)
    (i : Fin S.card) (j : Fin d) {t : ℕ} (hj : j.val < t) :
    sheet hd ha S i j ∈ stage hd ha S i t :=
  subset_adjoin _ _ ⟨i, j, Or.inr ⟨rfl,hj⟩, rfl⟩

theorem stage_base {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k) :
    stage hd ha S 0 0 = ⊥ := by
  apply eq_bot_iff.mpr
  apply adjoin_le_iff.mpr
  rintro _ ⟨u, r, h, _⟩
  omega

theorem stage_glue {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k)
    (i : Fin S.card) : stage hd ha S (i.val+1) 0 = stage hd ha S i d := by
  apply congrArg (adjoin (RatFunc k))
  ext x
  constructor <;> rintro ⟨u, r, h, hx⟩ <;> refine ⟨u, r, ?_, hx⟩ <;>
    have hr := r.isLt <;> omega

theorem stage_succ {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k)
    (i : Fin S.card) (j : Fin d) : stage hd ha S i (j.val+1) =
      stage hd ha S i j ⊔ adjoin (RatFunc k) {sheet hd ha S i j} := by
  have hset : rootPrefix hd ha S i (j.val+1) =
      rootPrefix hd ha S i j ∪ {sheet hd ha S i j} := by
    ext x
    constructor
    · rintro ⟨u, r, h, rfl⟩
      by_cases hh : u.val < i.val ∨ u.val = i.val ∧ r.val < j.val
      · exact Or.inl ⟨u, r, hh, rfl⟩
      · have hu : u = i := Fin.ext (by omega)
        have hr : r = j := Fin.ext (by omega)
        subst u
        subst r
        exact Or.inr rfl
    · rintro (⟨u,r,h,hx⟩ | rfl)
      · exact ⟨u,r,by omega,hx⟩
      · exact ⟨i,j,Or.inr ⟨rfl,Nat.lt_succ_self _⟩,rfl⟩
  change adjoin (RatFunc k) _ = adjoin (RatFunc k) _ ⊔ _
  rw [hset]
  exact IntermediateField.gc.l_sup

/-- The complete tower generates the actual splitting field, also for the empty family. -/
theorem stage_top {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k) :
    stage hd ha S S.card 0 = ⊤ := by
  classical
  let P := ∏ u ∈ S, cuspCoordinate d a u
  have hp : P ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun u _ => (cuspCoordinate_irreducible (by omega) a u).ne_zero)
  have hgen : adjoin (RatFunc k) (P.rootSet (cuspCompositum d a S)) = ⊤ :=
    (isSplittingField_iff_intermediateField.mp
      (inferInstance : P.IsSplittingField (RatFunc k) (cuspCompositum d a S))).2
  apply eq_top_iff.mpr
  rw [← hgen]
  apply adjoin_le_iff.mpr
  intro x hx
  rw [show P.rootSet (cuspCompositum d a S) = _ from
    rootSet_prod (cuspCoordinate d a) S hp] at hx
  obtain ⟨u,hu,hx⟩ := Set.mem_iUnion₂.mp hx
  let i := (shifts S).symm ⟨u,hu⟩
  have hi : shift S i = u := congrArg Subtype.val ((shifts S).apply_symm_apply ⟨u,hu⟩)
  rw [← hi] at hx
  let r := (sheetEquiv hd ha S i).symm ⟨x,hx⟩
  apply subset_adjoin (RatFunc k) (rootPrefix hd ha S S.card 0)
  exact ⟨i,r,Or.inl i.isLt,congrArg Subtype.val ((sheetEquiv hd ha S i).apply_symm_apply ⟨x,hx⟩)⟩

end
end BlockingCurves.CuspidalRootTower
