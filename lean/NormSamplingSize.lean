import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Pow

/-! Numerical thresholds for the independent-coset argument. -/
namespace BlockingCurves.NormPencil

private theorem exponent_budget {s : ℕ} (hs : 2 ≤ s) :
    ∀ n : ℕ, 4 ≤ n → (n+1) * (s-1)^2 ≤ s^(n-1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hs
    rw [hk]
    have hsub : 2+k-1 = k+1 := by omega
    rw [hsub]
    norm_num
    ring_nf
    omega
  | succ n hn ih =>
    have he : n+1-1 = (n-1)+1 := by omega
    rw [he, pow_succ]
    calc
      _ ≤ ((n+1)*(s-1)^2)*s := by
        have h := Nat.mul_le_mul_right ((s-1)^2) (show n+1+1 ≤ (n+1)*s by nlinarith)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ ih

/-- All extension dimensions at least four pass the sparse-row union bound,
including the binary ground field. -/
theorem sparse_threshold {s n : ℕ} (hs : 2 ≤ s) (hn : 4 ≤ n) :
    (s-1) * s^n * (s-1)^(s^(n-1)) < s^(s^(n-1)) := by
  let a : ℝ := s-1
  have hsa : (s:ℝ) = a+1 := by dsimp [a]; ring
  have ha : 0 < a := by dsimp [a]; exact sub_pos.mpr (by exact_mod_cast (show 1 < s by omega))
  have hcast : ((s-1 : ℕ):ℝ) = a := by dsimp [a]; rw [Nat.cast_sub (by omega)]; simp
  let R : ℝ := (s:ℝ)/a
  have hR : R = 1+a⁻¹ := by dsimp [R]; rw [hsa]; field_simp
  have hR1 : 1 ≤ R := by rw [hR]; linarith [inv_pos.mpr ha]
  have htwo : 2 ≤ R^(s-1) := by
    have h := one_add_mul_le_pow (a := a⁻¹) (by linarith [inv_pos.mpr ha]) (s-1)
    rw [hcast, mul_inv_cancel ha.ne'] at h
    rw [hR]
    linarith
  have hs2 : s ≤ 2^(s-1) := by
    have := Nat.lt_two_pow (s-1)
    omega
  have hthreshold : ((s-1 : ℕ):ℝ) * (s:ℝ)^n < R^(s^(n-1)) := by
    calc
      _ < (s:ℝ)^(n+1) := by
        rw [pow_succ, mul_comm ((s-1:ℕ):ℝ)]
        exact mul_lt_mul_of_pos_left (by exact_mod_cast (show s-1 < s by omega)) (pow_pos (by positivity) _)
      _ ≤ ((2:ℝ)^(s-1))^(n+1) := by gcongr; exact_mod_cast hs2
      _ = 2^((s-1)*(n+1)) := (pow_mul _ _ _).symm
      _ ≤ (R^(s-1))^((s-1)*(n+1)) := pow_le_pow_left (by norm_num) htwo _
      _ = R^((n+1)*(s-1)^2) := by rw [← pow_mul]; congr 1; ring
      _ ≤ _ := pow_le_pow_right hR1 (exponent_budget hs n hn)
  rw [show R^(s^(n-1)) = (s:ℝ)^(s^(n-1))/a^(s^(n-1)) by simp [R, div_pow]] at hthreshold
  have h := (lt_div_iff (pow_pos ha _)).mp hthreshold
  rw [← hcast] at h
  exact_mod_cast h

/-- The quadratic density one third suffices uniformly from s=25. -/
theorem dense_threshold {s : ℕ} (hs : 25 ≤ s) : (s-1)*s^2*2^s < 3^s := by
  suffices h : s^3*2^s < 3^s by
    apply lt_of_le_of_lt _ h
    exact Nat.mul_le_mul_right _ (by nlinarith [Nat.mul_le_mul_right (s^2) (Nat.sub_le s 1)])
  induction s, hs using Nat.le_induction with
  | base => decide
  | succ s hs ih =>
    have hf : 2*(s+1)^3 ≤ 3*s^3 := by
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hs
      rw [hk]
      ring_nf
      omega
    rw [pow_succ (2:ℕ), pow_succ (3:ℕ)]
    calc
      _ = (2*(s+1)^3)*2^s := by ring
      _ ≤ (3*s^3)*2^s := Nat.mul_le_mul_right _ hf
      _ < _ := by nlinarith [Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 3)]
end BlockingCurves.NormPencil
