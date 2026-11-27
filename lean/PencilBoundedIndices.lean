import PencilVariableGrowth
import PencilHorizontal

/-! Uniform logarithmic bounds when the two multiplicative indices are bounded. -/
namespace BlockingCurves.PencilCollisionCover
open Real PencilSampling

/-- The upper constant depends only on the caps R and H. The lower estimate
is Zhou--Wu Proposition 4.1 for the *reduced* horizontal power index. -/
theorem bounded_indices_log_bounds (F : Type*) [Field F] [Fintype F] (d R H : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ d.gcd (Fintype.card F-1))
    (hrR : d.gcd (Fintype.card F-1) ≤ R) (hhH : (d-1).gcd (Fintype.card F-1) ≤ H)
    (lower : let r := d.gcd (Fintype.card F-1)
      (r:ℝ)*log (Fintype.card F)/(8*log r) ≤ horizontalMinimum F r) :
    ∃ B : ℕ, AsgarliGhiocaYip.isPencilMinimum F d B ∧
      log (Fintype.card F)/8 ≤ (B:ℝ) ∧
      (B:ℝ) ≤ (4/log (1+1/((R:ℝ)+H+1))+2)*log (Fintype.card F) := by
  let q := Fintype.card F
  let r := d.gcd (q-1)
  let h : ℝ := (d-1).gcd (q-1)
  let K : ℝ := R+H+1
  let L := log (q:ℝ)
  let ρ := log (1+1/K)
  let μ := log ((r:ℝ)/(r-1))
  let ν := log (1+1/h)
  have hq : (2:ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q from Fintype.one_lt_card)
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hR : (r:ℝ) ≤ R := by exact_mod_cast hrR
  have hh : 0 < h := by
    dsimp [h]; exact_mod_cast Nat.gcd_pos_of_pos_left (q-1) (show 0 < d-1 by omega)
  have hH : h ≤ H := by dsimp [h]; exact_mod_cast hhH
  have hK : 0 < K := by dsimp [K]; positivity
  have hρ : 0 < ρ := log_pos (by linarith only [one_div_pos.mpr hK])
  have hlo : ρ ≤ μ := by
    apply log_le_log (by positivity : 0 < 1+1/K)
    calc
      1+1/K ≤ 1+1/((r:ℝ)-1) := by
        apply add_le_add_left
        apply one_div_le_one_div_of_le (by linarith only [hr2])
        dsimp [K]; linarith only [hR,Nat.cast_nonneg (α := ℝ) H]
      _ = _ := by
        field_simp [show (r:ℝ)-1≠0 by linarith only [hr2]]
  have hhi : ρ ≤ ν := by
    apply log_le_log (by positivity : 0 < 1+1/K)
    apply add_le_add_left
    apply one_div_le_one_div_of_le hh
    dsimp [K]; linarith only [hH,Nat.cast_nonneg (α := ℝ) R]
  have h2 : log 2 ≤ L := log_le_log (by norm_num) hq
  have hinv := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
  rw [log_inv] at hinv
  norm_num at hinv
  have hL : 1/2 ≤ L := hinv.trans h2
  have hL0 : 0 ≤ L := by linarith only [hL]
  obtain ⟨S,hS,hSc⟩ := projective_split_collision_upper (F := F) d hd
  have hrnat : 2 ≤ r := hr
  have hrate : horizontalRate r ν = μ := if_neg (show ¬r≤1 by omega)
  change (S.card:ℝ) ≤ sampleCutoff q (1/2) (horizontalRate r ν) ν 0 + 1 at hSc
  rw [hrate] at hSc
  simp only [sampleCutoff,one_div,log_inv,sub_neg_eq_add,mul_zero,zero_div,add_zero] at hSc
  have hsamp : (S.card:ℝ) ≤ 4*L/ρ+1 := by
    apply hSc.trans (add_le_add_right (max_le _ _) 1)
    · change (L+log 2+log 2)/μ ≤ 4*L/ρ
      apply (div_le_div_of_nonneg_left (by linarith only [hL0,hinv]) hρ hlo).trans
      apply (div_le_div_right hρ).2
      change L+log 2+log 2 ≤ 4*L
      linarith only [h2,hL0]
    · change (2*L+log 2+log 2)/ν ≤ 4*L/ρ
      apply (div_le_div_of_nonneg_left (by linarith only [hL0,hinv]) hρ hhi).trans
      apply (div_le_div_right hρ).2
      change 2*L+log 2+log 2 ≤ 4*L
      linarith only [h2]
  obtain ⟨B,hB,hτ,_⟩ := variable_degree_minimum_gap F d hd
  have hmin : B ≤ S.card := ((AGY_minimum_iff hd _).1 hB).2 ⟨S,rfl,hS⟩
  have hr' : 0 < log (r:ℝ) := log_pos (by linarith only [hr2])
  have hB' : (r:ℝ)*L/(8*log r) ≤ B := by
    rw [horizontal_minimum_index F d (by omega)] at hτ
    exact lower.trans (by exact_mod_cast hτ)
  refine ⟨B,hB,?_,?_⟩
  · apply le_trans _ hB'
    apply (le_div_iff (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_right
      (log_le_sub_one_of_pos (by positivity : 0 < (r:ℝ))) hL0,hL0]
  · change (B:ℝ) ≤ (4/ρ+2)*L
    have hb : (B:ℝ) ≤ S.card := by exact_mod_cast hmin
    rw [add_mul,div_mul_eq_mul_div]
    linarith only [hb,hsamp,hL]

end BlockingCurves.PencilCollisionCover
