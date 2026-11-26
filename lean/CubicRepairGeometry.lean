import CubicRepairPlaces
import CubicRepairDegree
import CubicAlterationSize

/-! Castelnuovo–Severi, Hasse–Weil and the pole fibre in the one-parameter
repair. The numerical consequences below are proved for the generated fields
and rational places, with no assumption about the number of common hits. -/
namespace BlockingCurves.CubicRepairGeometry
open Finset IntermediateField FiniteDimensional CubicAlteration CubicRepairPlaces
universe u
variable {F : Type u} [Field F] [Fintype F] {R : Finset (Line F)}

noncomputable def stage (D : Branch F R) (S : Finset R) : IntermediateField (RatFunc F) D.K :=
  adjoin (RatFunc F) (D.root '' (S : Set R))

/-- Relative degree after adding the roots in T over the stage for S. -/
noncomputable def relativeDegree (D : Branch F R) (S T : Finset R) : ℕ :=
  finrank (stage D S) (adjoin (stage D S) (D.root '' (T : Set R)))

theorem relativeDegree_le (D : Branch F R) (S T : Finset R) :
    relativeDegree D S T ≤ 3^T.card := by
  let B := RatFunc F
  let E := stage D S
  exact (CubicRepairDegree.generated_degree T D.root
    (fun i => algebraMap B E (RatFunc.C (i.val.1:F)))
    (fun i => algebraMap B E (RatFunc.X+RatFunc.C i.val.2))
    (fun i _ => by simpa only [← IsScalarTower.algebraMap_apply B E D.K] using D.equation i)).2

theorem branch_degree_le (D : Branch F R) : finrank (RatFunc F) D.K ≤ 3^R.card := by
  have h := (CubicRepairDegree.generated_degree (univ : Finset R) D.root
    (fun i => RatFunc.C (i.val.1:F)) (fun i => RatFunc.X + RatFunc.C i.val.2)
    (fun i _ => D.equation i)).2
  rw [Finset.coe_univ, Set.image_univ, D.generated, IntermediateField.finrank_top'] at h
  simpa only [Finset.card_univ, Fintype.card_coe] using h

noncomputable def poles (D : Branch F R) (P : Finset (Place D)) : Finset (Place D) := by
  classical
  exact P.filter fun p => parameter D ∉ p.ring

/-- The one-root stages and the base are rational. The compositum inequality
uses both actual relative degrees. The point count and the pole bound are
separate statements on a finite set of degree-one places of this branch. -/
structure CurveLaws (D : Branch F R)
    (g : IntermediateField (RatFunc F) D.K → ℕ) (P : Finset (Place D)) : Prop where
  rationalGenus : ∀ (E : IntermediateField (RatFunc F) D.K) (e : RatFunc F ≃+* E),
    (∀ c : F, (e (RatFunc.C c) : D.K) = constant D c) → g E = 0
  compositum : ∀ (S : Finset R) (i : R), i ∉ S → by
    classical
    exact g (stage D (insert i S)) ≤ relativeDegree D S {i} * g (stage D S) +
      relativeDegree D {i} S * g (stage D {i}) +
      (relativeDegree D S {i} - 1) * (relativeDegree D {i} S - 1)
  poleFibre : (poles D P).card ≤ finrank (RatFunc F) D.K
  hasseWeil : (Fintype.card F : ℝ)+1 - 2*(g (stage D univ) : ℝ)*Real.sqrt (Fintype.card F) ≤ P.card

private theorem base_genus (D : Branch F R) {g P} (H : CurveLaws D g P) :
    g (stage D ∅) = 0 := by
  simp only [stage, coe_empty, Set.image_empty, adjoin_empty]
  apply H.rationalGenus _ (IntermediateField.botEquiv (RatFunc F) D.K).symm.toRingEquiv
  intro c
  rfl

private theorem single_genus (D : Branch F R) {g P} (H : CurveLaws D g P) (i : R) :
    g (stage D {i}) = 0 := by
  obtain ⟨e,he⟩ := single_root_rational D i
  simpa only [stage, coe_singleton, Set.image_singleton] using H.rationalGenus _ e he

theorem genus_bound (D : Branch F R) {g P} (H : CurveLaws D g P) (S : Finset R) :
    2*(g (stage D S) : ℝ) ≤ 2+(2*(S.card:ℝ)-1)*3^S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [base_genus D H]
  | @insert i S hi ih =>
    have cs := H.compositum S i hi
    rw [single_genus D H i, Nat.mul_zero, Nat.add_zero] at cs
    have ha : relativeDegree D S {i} ≤ 3 := by simpa using relativeDegree_le D S {i}
    have hb := relativeDegree_le D {i} S
    have hd : (relativeDegree D S {i}-1)*(relativeDegree D {i} S-1) ≤ 2*3^S.card :=
      Nat.mul_le_mul (by omega) ((Nat.sub_le _ _).trans hb)
    have step := cs.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ha) hd)
    have step' : (g (stage D (insert i S)):ℝ) ≤ 3*(g (stage D S):ℝ)+2*(3:ℝ)^S.card := by
      exact_mod_cast step
    by_cases hs : S = ∅
    · subst S
      simpa [single_genus D H] using (by norm_num : (0:ℝ) ≤ 2+(2*1-1)*3^1)
    · have hc : 1 ≤ S.card := Finset.card_pos.mpr (nonempty_iff_ne_empty.mpr hs)
      have hp : (3:ℝ) ≤ 3^S.card := by
        simpa using pow_le_pow_right (by norm_num : (1:ℝ) ≤ 3) hc
      rw [card_insert_of_not_mem hi, pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith only [ih,step',hp]

/-- Allowance for the pole fibre and the Hasse–Weil error together. -/
noncomputable def repairCost (q : ℝ) (s : ℕ) : ℝ :=
  3^s + (2+(2*(s:ℝ)-1)*3^s)*Real.sqrt q

theorem repairCost_mono (q : ℝ) {s t : ℕ} (hs : s ≤ t) : repairCost q s ≤ repairCost q t := by
  rcases Nat.eq_zero_or_pos t with hz | ht
  · have he : s = t := by omega
    rw [he]
  have hp : (3:ℝ)^s ≤ 3^t := pow_le_pow_right (by norm_num) hs
  have hst : (s:ℝ) ≤ t := by exact_mod_cast hs
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  exact add_le_add hp (mul_le_mul_of_nonneg_right
    (add_le_add_left (mul_le_mul (by linarith) hp (by positivity) (by linarith)) 2) (Real.sqrt_nonneg _))

/-- A strict Hasse–Weil surplus forces a rational place away from all poles. -/
theorem common_of_laws (D : Branch F R) {g P} (H : CurveLaws D g P)
    (htest : repairCost (Fintype.card F) R.card < (Fintype.card F:ℝ)+1) :
    ∃ a : F, ∀ l ∈ R, Hits a l := by
  classical
  by_cases hR : R = ∅
  · subst R; exact ⟨0, by simp⟩
  have hg := genus_bound D H (univ : Finset R)
  simp only [card_univ,Fintype.card_coe] at hg
  unfold repairCost at htest
  have hpoles : ((poles D P).card:ℝ) ≤ (3:ℝ)^R.card := by
    exact_mod_cast H.poleFibre.trans (branch_degree_le D)
  have hcard : (poles D P).card < P.card := by
    apply (Nat.cast_lt (α := ℝ)).mp
    linarith only [hpoles,htest,H.hasseWeil,
      mul_le_mul_of_nonneg_right hg (Real.sqrt_nonneg (Fintype.card F))]
  obtain ⟨p,hP,hn⟩ : ∃ p ∈ P, p ∉ poles D P := by
    by_contra! cover
    exact (not_le_of_lt hcard) (card_le_card cover)
  have hreg : parameter D ∈ p.ring := by simpa [poles,hP] using hn
  exact hit_of_regular_place D p hreg

end BlockingCurves.CubicRepairGeometry
