import PencilRepairBranchGeometry
import PencilRepairSize
import PencilFrobeniusCount
import PencilCharacterCollisions

/-! The explicit log-log budget from the classical curve theorems on the
constructed Laurent branch. -/
namespace BlockingCurves.PencilSampling
open Real PencilRepairBranch
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

def repairRate (d : ℕ) : ℝ := (4*log (d:ℝ))⁻¹


/-- The explicit second-order bound, with the two slope classes retained. -/
def repairedCutoff (d q : ℕ) (δ C : ℝ) : ℝ :=
  let L := log (q:ℝ)
  let rate := log (1/δ)
  let c := repairRate d
  max ((L-log L-log c+log 2)/horizontalRate (d.gcd (q-1)) rate)
    ((2*L-log L-log c+log 2)/rate + 12*(C/δ)/rate^2) + 2

/-- The genus and point estimates are needed only on the actual Laurent
models for lists within the repair budget. -/
def RepairCurveEstimates (F : Type*) [Field F] [Fintype F] (d : ℕ) : Prop :=
  (∀ (R : Finset (Lines F)), R.card ≤ ⌊repairRate d*log (Fintype.card F)⌋₊ →
    ∀ D : Model F d R, CompositumBound D) ∧
  (∀ (R : Finset (Lines F)), R.card ≤ ⌊repairRate d*log (Fintype.card F)⌋₊ →
    ∀ D : Model F d R, HasseWeilBound D)

private theorem repair_budget_fits {d : ℕ} (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q)
    (hL : max 128 (2*log (d:ℝ)) ≤ log q) :
    0 < repairRate d ∧ 1/2 ≤ repairRate d*log q ∧ repairRate d*log q ≤ q := by
  have hD : (2:ℝ) ≤ d := by exact_mod_cast hd
  have h₂ := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
  rw [log_inv] at h₂
  norm_num at h₂
  have hl : (1/2:ℝ) ≤ log (d:ℝ) := by linarith only [h₂,log_le_log (by norm_num : (0:ℝ)<2) hD]
  have hd0 : 0 < 4*log (d:ℝ) := by linarith
  have hqL := (le_max_right _ _).trans hL
  simp only [repairRate, inv_mul_eq_div]
  refine ⟨inv_pos.mpr hd0, (le_div_iff hd0).2 (by linarith), (div_le_iff hd0).2 ?_⟩
  nlinarith only [log_le_sub_one_of_pos hq, mul_le_mul_of_nonneg_right hl hq.le, hq.le]

/-- No residual-line covering assumption. The only inputs for the repair
are Castelnuovo--Severi and Hasse--Weil, evaluated on the constructed models. -/
theorem projective_loglog_of_curve_estimates {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0)
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C)
    (large : max 128 (2*log (d:ℝ)) ≤ log (Fintype.card F))
    (error : 2*(C/δ) ≤ log (1/δ)*sqrt (Fintype.card F))
    (oneLine : ∀ l : Fˣ × F, ((missed d (.inr l : Lines F)).card:ℝ) ≤
      Fintype.card F*(δ+C/sqrt (Fintype.card F)))
    (cs : ∀ (R : Finset (Lines F)), R.card ≤ ⌊repairRate d*log (Fintype.card F)⌋₊ →
      ∀ D : Model F d R, CompositumBound D)
    (hw : ∀ (R : Finset (Lines F)), R.card ≤ ⌊repairRate d*log (Fintype.card F)⌋₊ →
      ∀ D : Model F d R, HasseWeilBound D) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card:ℝ) ≤ repairedCutoff d (Fintype.card F) δ C := by
  have hq : (0:ℝ)<Fintype.card F := by exact_mod_cast Fintype.card_pos
  obtain ⟨hc,hlo,hhi⟩ := repair_budget_fits hd _ hq large
  apply projective_loglog_of_nonzero_value_set hd hc hlo hhi hδ hδ1 hC error oneLine
  apply commonHit_of_classical_bounds hd hp cs hw
  apply PencilRepairSize.point_budget hq ((le_max_left _ _).trans large) hd
  simp only [repairRate, inv_mul_eq_div, le_refl]

/-- Specialization to the actual Frobenius distribution on separable fibres,
with the exceptional-parameter contribution included in the error constant. -/
theorem tame_repaired_upper {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0) {A : ℝ} (hA : 0 ≤ A)
    (cheb : ChebotarevUpper F hd A) (curves : RepairCurveEstimates F d)
    (large : max 128 (2*log (d:ℝ)) ≤ log (Fintype.card F))
    (error : 2*((A+(d-1:ℕ))/derangementFraction d) ≤
      log (1/derangementFraction d)*sqrt (Fintype.card F)) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card:ℝ) ≤ repairedCutoff d (Fintype.card F) (derangementFraction d) (A+(d-1:ℕ)) :=
  projective_loglog_of_curve_estimates hd hp (derangementFraction_bounds hd).1
    (derangementFraction_bounds hd).2 (by positivity) large error
    (line_miss_of_chebotarev hd cheb) curves.1 curves.2

/-- The characteristic dividing d−1 is allowed. All collision algebra is
proved internally; only the classical Kummer and curve estimates enter. -/
theorem kummer_repaired_upper {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0)
    (nonpower : ∀ v : ℕ, d ≠ (ringChar F)^v)
    (weil : PencilCharacterCollisions.AffineKummerBound F) (curves : RepairCurveEstimates F d)
    (large : max 128 (2*log (d:ℝ)) ≤ log (Fintype.card F))
    (error : 1+(d:ℝ)^2 ≤ log 2 * sqrt (Fintype.card F)) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card:ℝ) ≤ repairedCutoff d (Fintype.card F) (1/2) ((1+(d:ℝ)^2)/4) := by
  apply projective_loglog_of_curve_estimates hd hp (by norm_num) (by norm_num) (by positivity) large
    _ (PencilCharacterCollisions.nonzero_line_bound hd nonpower weil) curves.1 curves.2
  norm_num
  linarith only [error]

end
end BlockingCurves.PencilSampling
