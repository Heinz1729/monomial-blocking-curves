import CubicGenusTransport
import CubicFiniteFibres
import CubicStageFields
import CubicZetaPoints
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

/-- The pole bound applies to every finite collection of actual rational places. -/
theorem poles_card_le (D : Branch F R) (P : Finset (Place D)) :
    (poles D P).card ≤ finrank (RatFunc F) D.K := by
  classical
  apply CubicPoleDegree.card_le_degree_of_polar
  intro p hp
  exact (mem_filter.mp hp).2

private noncomputable instance coefficientAlgebra {K : Type u} [Field K] [Algebra (RatFunc F) K]
    (E : IntermediateField (RatFunc F) K) : Algebra F E :=
  ((algebraMap (RatFunc F) E).comp RatFunc.C).toAlgebra

noncomputable abbrev stageForms (D : Branch F R) (S : Finset R) :=
  CubicRationalGenus.regularForms F (stage D S)

noncomputable abbrev stageGenus (D : Branch F R) (S : Finset R) : ℕ :=
  CubicRationalGenus.genus F (stage D S)

noncomputable def branchGenus (D : Branch F R) : ℕ := by
  letI : Algebra F D.K := (constant D).toAlgebra
  exact CubicRationalGenus.genus F D.K

theorem stageGenus_univ (D : Branch F R) : stageGenus D univ = branchGenus D :=
  full_stage_genus D

private theorem base_rational (D : Branch F R) : Nonempty (RatFunc F ≃ₐ[F] stage D ∅) := by
  let T (E : IntermediateField (RatFunc F) D.K) := Nonempty (RatFunc F ≃ₐ[F] E)
  change T (stage D ∅)
  rw [show stage D ∅ = ⊥ by simp [stage]]
  exact ⟨AlgEquiv.ofRingEquiv (f := (IntermediateField.botEquiv (RatFunc F) D.K).symm.toRingEquiv)
    (by intro a; rfl)⟩

private theorem single_rational (D : Branch F R) (i : R) :
    Nonempty (RatFunc F ≃ₐ[F] stage D {i}) := by
  obtain ⟨e,he⟩ := single_root_rational D i
  let T (E : IntermediateField (RatFunc F) D.K) := Nonempty (RatFunc F ≃ₐ[F] E)
  change T (stage D {i})
  rw [show stage D {i} = adjoin (RatFunc F) {D.root i} by simp [stage]]
  exact ⟨AlgEquiv.ofRingEquiv (f := e) (fun a => Subtype.ext (he a))⟩

theorem base_regularForms_eq_bot (D : Branch F R) : stageForms D ∅ = ⊥ :=
  CubicRationalGenus.regularForms_eq_bot (base_rational D).some

theorem single_regularForms_eq_bot (D : Branch F R) (i : R) : stageForms D {i} = ⊥ :=
  CubicRationalGenus.regularForms_eq_bot (single_rational D i).some

theorem base_genus (D : Branch F R) : stageGenus D ∅ = 0 :=
  CubicRationalGenus.rational_genus_zero (base_rational D).some

theorem single_genus (D : Branch F R) (i : R) : stageGenus D {i} = 0 :=
  CubicRationalGenus.rational_genus_zero (single_rational D i).some

/-- The classical compositum inequality, stated as a rank bound on regular
differentials. A finite previous stage therefore gives a finite next stage. -/
def CompositumBound (D : Branch F R) : Prop := by
  classical
  exact ∀ (S : Finset R) (i : R), i ∉ S → FiniteDimensional F (stageForms D S) →
    Module.rank F (stageForms D (insert i S)) ≤
      ((relativeDegree D S {i} * stageGenus D S + relativeDegree D {i} S * stageGenus D {i} +
        (relativeDegree D S {i} - 1) * (relativeDegree D {i} S - 1) : ℕ) : Cardinal)

/-- A point bound on the same field whose differentials give the genus. -/
structure CurveLaws (D : Branch F R) : Prop where
  compositum : CompositumBound D
  hasseWeil : (Fintype.card F : ℝ)+1 - 2*(branchGenus D : ℝ)*Real.sqrt (Fintype.card F) ≤
    (Nat.card (Place D) : ℝ)

/-- The classical zeta numerator and its individual weights suffice for the
point-count input, by taking the linear coefficient of the actual Euler product. -/
theorem CurveLaws.of_weil_roots (D : Branch F R) (cs : CompositumBound D)
    (W : CubicZetaPoints.WeilLaws D (Fintype.card F) (branchGenus D)) : CurveLaws D := by
  refine ⟨cs,?_⟩
  rw [← Nat.card_congr (CubicZetaPoints.degreeOneEquiv D)]
  exact CubicZetaPoints.point_lower D W

/-- The cardinal form of Castelnuovo–Severi also gives finite dimensionality.
Consequently each finrank in the numerical recursion is an actual dimension. -/
theorem stage_finite (D : Branch F R) (cs : CompositumBound D) (S : Finset R) :
    FiniteDimensional F (stageForms D S) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact CubicRationalGenus.rational_finiteDimensional (base_rational D).some
  | @insert i S hi ih =>
    have h := (cs S i hi ih).trans_lt (Cardinal.nat_lt_aleph0 _)
    let b := Basis.ofVectorSpace F (stageForms D (insert i S))
    letI := b.fintypeIndexOfRankLtAleph0 h
    exact FiniteDimensional.of_fintype_basis b

theorem genus_bound (D : Branch F R) (H : CompositumBound D) (S : Finset R) :
    2*(stageGenus D S : ℝ) ≤ 2+(2*(S.card:ℝ)-1)*3^S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [base_genus D]
  | @insert i S hi ih =>
    have hr := H S i hi (stage_finite D H S)
    letI := stage_finite D H (insert i S)
    rw [← FiniteDimensional.finrank_eq_rank', single_genus D i, Nat.mul_zero, Nat.add_zero] at hr
    have cs := Nat.cast_le.mp hr
    have ha : relativeDegree D S {i} ≤ 3 := by simpa using relativeDegree_le D S {i}
    have hb := relativeDegree_le D {i} S
    have hd : (relativeDegree D S {i}-1)*(relativeDegree D {i} S-1) ≤ 2*3^S.card :=
      Nat.mul_le_mul (by omega) ((Nat.sub_le _ _).trans hb)
    have step := cs.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ha) hd)
    have step' : (stageGenus D (insert i S):ℝ) ≤ 3*(stageGenus D S:ℝ)+2*(3:ℝ)^S.card := by
      exact_mod_cast step
    by_cases hs : S = ∅
    · subst S
      simpa [single_genus D] using (by norm_num : (0:ℝ) ≤ 2+(2*1-1)*3^1)
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
theorem common_of_laws (D : Branch F R) (H : CurveLaws D)
    (htest : repairCost (Fintype.card F) R.card < (Fintype.card F:ℝ)+1) :
    ∃ a : F, ∀ l ∈ R, Hits a l := by
  classical
  by_cases hR : R = ∅
  · subst R; exact ⟨0, by simp⟩
  letI := CubicFiniteFibres.placeFintype D
  let P : Finset (Place D) := univ
  have hpoints : (Fintype.card F : ℝ)+1 - 2*(stageGenus D univ : ℝ)*Real.sqrt (Fintype.card F) ≤ P.card := by
    simpa only [stageGenus_univ, P, Finset.card_univ, Nat.card_eq_fintype_card] using H.hasseWeil
  have hg := genus_bound D H.compositum (univ : Finset R)
  simp only [card_univ,Fintype.card_coe] at hg
  unfold repairCost at htest
  have hpoles : ((poles D P).card:ℝ) ≤ (3:ℝ)^R.card := by
    exact_mod_cast (poles_card_le D P).trans (branch_degree_le D)
  have hcard : (poles D P).card < P.card := by
    apply (Nat.cast_lt (α := ℝ)).mp
    linarith only [hpoles,htest,hpoints,
      mul_le_mul_of_nonneg_right hg (Real.sqrt_nonneg (Fintype.card F))]
  obtain ⟨p,hP,hn⟩ : ∃ p ∈ P, p ∉ poles D P := by
    by_contra! cover
    exact (not_le_of_lt hcard) (card_le_card cover)
  have hreg : parameter D ∈ p.ring := by simpa [poles,hP] using hn
  exact hit_of_regular_place D p hreg

end BlockingCurves.CubicRepairGeometry
