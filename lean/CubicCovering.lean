import Projective
import CubicSlope
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Counting ordered samples gives the finite upper bound of §10.
The application only needs the number of parameters missed by each nonhorizontal line. -/
namespace BlockingCurves.CubicCovering

variable {F : Type*} [Field F] [Fintype F]

/-- Parameters whose cubic misses the line y = mx+b. -/
noncomputable def missedParameters (m b : F) : Finset F := by
  classical
  exact Finset.univ.filter (fun a : F => ¬ ∃ x : F, x^3 - m*x - b = a)

theorem exists_projective_cover (h k : ℕ) (hk : 0 < k) (hq : Fintype.card F % 3 = 2)
    (hline : ∀ m b : F, m ≠ 0 → (missedParameters m b).card ≤ h)
    (hsize : Fintype.card F * (Fintype.card F - 1) * h^k < (Fintype.card F)^k) :
    ∃ S : Finset F, S.card ≤ k ∧ ProjectiveBlocks 3 (S : Set F) := by
  classical
  let L := Fˣ × F
  let bad (l : L) : Finset (Fin k → F) :=
    Fintype.piFinset (fun _ : Fin k => missedParameters (l.1 : F) l.2)
  let U := (Finset.univ : Finset L).biUnion bad
  have hbad (l : L) : (bad l).card ≤ h^k := by
    dsimp [bad]
    simpa using pow_le_pow_left' (hline (l.1:F) l.2 l.1.ne_zero) k
  have hcard : U.card < Fintype.card (Fin k → F) := by
    have hb := Finset.card_biUnion_le_card_mul (Finset.univ : Finset L) bad (h^k) (fun l _ => hbad l)
    have hc : Fintype.card L = Fintype.card F * (Fintype.card F - 1) := by
      simp [L, Fintype.card_units, Nat.mul_comm]
    rw [Finset.card_univ, hc] at hb
    simpa [U] using hb.trans_lt hsize
  obtain ⟨f, hf⟩ : ∃ f : Fin k → F, f ∉ U := by
    by_contra! hall
    rw [Finset.eq_univ_of_forall hall, Finset.card_univ] at hcard
    exact (Nat.lt_irrefl _) hcard
  refine ⟨Finset.univ.image f, ?_, (projectiveBlocks_iff_graphHits (by decide) _).2 ?_⟩
  · simpa using Finset.card_image_le (f := f) (s := Finset.univ)
  · intro m b
    by_cases hm : m = 0
    · let i : Fin k := ⟨0, hk⟩
      obtain ⟨x, hx⟩ := CubicSlope.cube_surjective hq (f i + b)
      exact ⟨x, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [hm, hx]⟩⟩
    · let l : L := (Units.mk0 m hm, b)
      have hn : f ∉ bad l := fun he => hf (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, he⟩)
      rw [show bad l = Fintype.piFinset (fun _ : Fin k => missedParameters m b) from rfl,
        Fintype.mem_piFinset] at hn
      push_neg at hn
      obtain ⟨i, hi⟩ := hn
      simp [missedParameters] at hi
      obtain ⟨x, hx⟩ := hi
      exact ⟨x, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx.symm⟩⟩

open Real

/-- The logarithmic rounding in the union bound, including the finite-q correction
from an individual miss probability of (q+1)/(3q). -/
private theorem sample_size {q : ℝ} (hq : 16 ≤ q) :
    ∃ k : ℕ, 0 < k ∧ (k:ℝ) ≤ 2*log q/log 3 + 8 ∧
      q^2 * ((q+1)/3)^k < q^k := by
  have hq0 : 0 < q := by linarith
  have h3 : (2/3:ℝ) ≤ log 3 := by
    have hb := log_le_sub_one_of_pos (show (0:ℝ) < 3⁻¹ by norm_num)
    rw [log_inv, inv_eq_one_div] at hb
    linarith only [hb]
  have hd : 0 < log 3 := by linarith
  have hL := log_nonneg (show 1 ≤ q by linarith)
  let a := 2*log q/log 3
  let k : ℕ := ⌊a⌋₊+8
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hka : (k:ℝ) ≤ a+8 := by
    dsimp [k]
    push_cast
    linarith only [Nat.floor_le ha]
  have hak : a+7 < (k:ℝ) := by
    dsimp [k]
    push_cast
    linarith only [Nat.lt_floor_add_one a]
  have haklog := mul_lt_mul_of_pos_right hak hd
  have haid : a*log 3 = 2*log q := div_mul_cancel₀ _ hd.ne'
  have hal : a ≤ 3*log q := by
    apply (div_le_iff hd).mpr
    linarith only [mul_le_mul_of_nonneg_left h3 hL]
  have hkq : (k:ℝ)/q ≤ 4 := by
    apply (div_le_iff hq0).mpr
    linarith only [hka, hal, log_le_sub_one_of_pos hq0, hq]
  have ha1 : 0 < 1 + q⁻¹ := by positivity
  have hrem : (k:ℝ) * log (1+q⁻¹) ≤ 4 := by
    have ht := log_le_sub_one_of_pos ha1
    rw [div_eq_mul_inv] at hkq
    linarith only [hkq, mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hlog : log (q+1) = log q + log (1+q⁻¹) := by
    rw [← log_mul hq0.ne' ha1.ne']
    congr 1
    field_simp
  refine ⟨k, by dsimp [k]; omega, hka, ?_⟩
  apply (log_lt_log_iff (by positivity) (by positivity)).mp
  rw [log_mul (by positivity) (by positivity), log_pow, log_pow,
    log_div (by positivity) (by norm_num), log_pow, hlog]
  norm_num
  linarith only [haklog, haid, h3, hrem]

/-- The individual value-set bound is the only geometric input for the
2/log(3) upper coefficient. The conclusion quantifies over projective blocking sets. -/
theorem cubic_upper_of_miss_bound (h : ℕ) (hq16 : 16 ≤ Fintype.card F)
    (hq : Fintype.card F % 3 = 2) (hmiss : 3*h ≤ Fintype.card F + 1)
    (hline : ∀ m b : F, m ≠ 0 → (missedParameters m b).card ≤ h) :
    ∃ S : Finset F, ProjectiveBlocks 3 (S : Set F) ∧
      (S.card:ℝ) ≤ 2*log (Fintype.card F)/log 3 + 8 := by
  let Q := Fintype.card F
  have hQ : (16:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hq16
  obtain ⟨k, hk, hka, hsize⟩ := sample_size hQ
  have hmiss' : (h:ℝ) ≤ ((Q:ℝ)+1)/3 := by
    have ht : 3*(h:ℝ) ≤ (Q:ℝ)+1 := by exact_mod_cast hmiss
    linarith
  have hpow := pow_le_pow_left (Nat.cast_nonneg h : (0:ℝ) ≤ h) hmiss' k
  have hstrong : Q^2 * h^k < Q^k := by
    exact_mod_cast (mul_le_mul_of_nonneg_left hpow (sq_nonneg (Q:ℝ))).trans_lt hsize
  have hsub : Q*(Q-1) ≤ Q^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  obtain ⟨S, hS, hb⟩ := exists_projective_cover h k hk hq hline
    ((Nat.mul_le_mul_right _ hsub).trans_lt hstrong)
  exact ⟨S, hb, (show (S.card:ℝ) ≤ k by exact_mod_cast hS).trans hka⟩

end BlockingCurves.CubicCovering
