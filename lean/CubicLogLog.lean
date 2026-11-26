import CubicRepairGeometry
import CubicRepairBranch
import CubicDoubleMiss

/-! The §17 upper bound on the independent projective-plane specification. -/
namespace BlockingCurves.CubicLogLog
open CubicAlteration CubicRepairPlaces CubicRepairGeometry Real
universe u
variable {F : Type u} [Field F] [Fintype F]

/-- Cubing is separable in the permutation range, including characteristic two. -/
theorem three_ne_zero (hq : Fintype.card F % 3 = 2) : (3:F) ≠ 0 := by
  intro h3
  have hcard := congrArg (fun n : ℕ => (n:F)) (Nat.mod_add_div (Fintype.card F) 3)
  rw [hq] at hcard
  push_cast at hcard
  rw [h3, zero_mul, add_zero, FiniteField.cast_card_eq_zero] at hcard
  exact one_ne_zero (by linear_combination h3 - hcard : (1:F) = 0)

/-- The branch obtained by the simultaneous Laurent expansions over F. -/
noncomputable def branch (R : Finset (Line F)) (hq : Fintype.card F % 3 = 2) : Branch F R :=
  Classical.choose (CubicRepairBranch.exists_expansion R (three_ne_zero hq))

theorem branch_expansion (R : Finset (Line F)) (hq : Fintype.card F % 3 = 2) :
    Nonempty (CubicRepairBranch.Expansion (branch R hq)) :=
  Classical.choose_spec (CubicRepairBranch.exists_expansion R (three_ne_zero hq))

/-- The outstanding classical function-field statements, only on the selected
branches. The genus and rational places refer to the same generated field. -/
def GeometryAt (F : Type u) [Field F] [Fintype F] (hq : Fintype.card F % 3 = 2) : Prop :=
  ∀ R : Finset (Line F), 3 ≤ R.card → repairCost (Fintype.card F) R.card < (Fintype.card F:ℝ)+1 →
    ∃ g P, CurveLaws (branch R hq) g P

private theorem minimum_of_cover {S : Finset F} (hS : ProjectiveBlocks 3 (S : Set F))
    {C : ℝ} (hsize : (S.card:ℝ) ≤ C) :
    ∃ n : ℕ, AsgarliGhiocaYip.isPencilMinimum F 3 n ∧ (n:ℝ) ≤ C := by
  classical
  let P := fun n : ℕ => ∃ T : Finset F, T.card = n ∧ ProjectiveBlocks 3 (T : Set F)
  have h : P S.card := ⟨S,rfl,hS⟩
  have hex : ∃ n, P n := ⟨_,h⟩
  refine ⟨Nat.find hex,(AGY_minimum_iff (by decide : 2 ≤ 3) _).2
    ⟨Nat.find_spec hex,fun _ hn => Nat.find_min' hex hn⟩,?_⟩
  exact (show (Nat.find hex : ℝ) ≤ S.card by exact_mod_cast Nat.find_min' hex h).trans hsize

/-- In this explicit finite range even the point-counting inputs are unnecessary. -/
theorem minimum_upper_finite_range (hq : Fintype.card F % 3 = 2)
    (hL : log (Fintype.card F) ≤ (3:ℝ)^9) :
    ∃ n : ℕ, AsgarliGhiocaYip.isPencilMinimum F 3 n ∧
      (n:ℝ) ≤ (2*log (Fintype.card F)-log (log (Fintype.card F)))/log 3+17 := by
  let q : ℝ := Fintype.card F
  have hq1 : 1 < q := by dsimp [q]; exact_mod_cast Fintype.one_lt_card (α := F)
  have hpos : 0 < log q := log_pos hq1
  have h3 : (0:ℝ) < log 3 := log_pos (by norm_num)
  by_cases h16 : 16 ≤ Fintype.card F
  · obtain ⟨n,hn,hs⟩ := CubicCovering.cubic_minimum_upper (F := F) h16 hq
    refine ⟨n,hn,hs.trans ?_⟩
    have hl : log (log q) ≤ 9*log 3 := by simpa using log_le_log hpos hL
    change 2*log q/log 3+8 ≤ (2*log q-log (log q))/log 3+17
    rw [sub_div]
    linarith only [(div_le_iff h3).2 hl]
  · classical
    have hc : (Fintype.card F:ℝ) ≤ 16 := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h16))
    apply minimum_of_cover (S := Finset.univ)
    · apply (projectiveBlocks_iff_graphHits (by decide : 2 ≤ 3) _).2
      intro m b
      exact ⟨0,Finset.mem_univ _⟩
    · rw [Finset.card_univ]
      have hl := log_le_sub_one_of_pos hpos
      have hz : 0 ≤ (2*log q-log (log q))/log 3 := div_nonneg (by linarith) h3.le
      change (Fintype.card F:ℝ) ≤ (2*log q-log (log q))/log 3+17
      linarith

/-- All rounding, sampling, simultaneous specialization and extraction of the
projective minimum. No miss probability or simultaneous-hit bound is an input. -/
theorem minimum_upper (hq : Fintype.card F % 3 = 2) (geom : GeometryAt F hq) :
    ∃ n : ℕ, AsgarliGhiocaYip.isPencilMinimum F 3 n ∧
      (n:ℝ) ≤ (2*log (Fintype.card F)-log (log (Fintype.card F)))/log 3+17 := by
  let q : ℝ := Fintype.card F
  have hp : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := F)
  by_cases hL : 128 ≤ log q
  · obtain ⟨k,t,_,_,hs,hgeom,hbound⟩ := CubicAlterationSize.parameters hp hL
    have hcommon : CommonHit F t := by
      intro R hR
      by_cases hn : 3 ≤ R.card
      · have hc := (repairCost_mono q hR).trans_lt hgeom
        obtain ⟨g,P,H⟩ := geom R hn hc
        exact common_of_laws _ H hc
      · have hq2 : 2 < Fintype.card F := by
          by_contra! hz
          have hq' : q ≤ 2 := by dsimp [q]; exact_mod_cast hz
          linarith only [hL, log_le_sub_one_of_pos hp, hq']
        exact CubicDoubleMiss.commonHit_two hq hq2 R (by omega)
    let Q := Fintype.card F
    have hdivNat : ((Q+1)/3)*3 ≤ Q+1 := Nat.div_mul_le_self _ _
    have hdiv : (((Q+1)/3 : ℕ):ℝ) ≤ (q+1)/3 := by
      apply (le_div_iff (by norm_num : (0:ℝ)<3)).2
      change (((Q+1)/3 : ℕ):ℝ)*3 ≤ (Q:ℝ)+1
      exact_mod_cast hdivNat
    have hp2 := pow_le_pow_left (Nat.cast_nonneg ((Q+1)/3) : (0:ℝ) ≤ _) hdiv k
    have ha : Q*(Q-1) ≤ Q^2 := by rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hs' : (Q:ℝ)^2*(((Q+1)/3:ℕ):ℝ)^k ≤ (t:ℝ)*(Q:ℝ)^k :=
      (mul_le_mul_of_nonneg_left hp2 (sq_nonneg q)).trans hs
    have hn : Q^2*((Q+1)/3)^k ≤ t*Q^k := by exact_mod_cast hs'
    have size := (Nat.mul_le_mul_right (((Q+1)/3)^k) ha).trans hn
    obtain ⟨S,hS,hb⟩ := projective_cover_after_repair k t hq (by simpa [Nat.mul_comm t] using size) hcommon
    apply minimum_of_cover hb
    exact (show (S.card:ℝ) ≤ (k:ℝ)+1 by exact_mod_cast hS).trans hbound
  · apply minimum_upper_finite_range hq
    change log q ≤ (3:ℝ)^9
    exact (le_of_not_ge hL).trans (by norm_num)

end BlockingCurves.CubicLogLog
