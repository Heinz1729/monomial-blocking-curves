import NormCubicMinimum
import NormSamplingMinimum
import NormSmallMinimum
import NormSmallOdd
import Mathlib.Algebra.IsPrimePow

/-! The full norm-pencil theorem in the exponent (q-1)/(s-1) of the manuscript. -/
namespace BlockingCurves.NormPencil

open FiniteDimensional
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

private theorem remaining_sizes (s : ℕ) (hs : s < 25) (hp : IsPrimePow s)
    (hc : ¬(s-1).Coprime 2) : s ∈ ([3,5,7,9,11,13,17,19,23] : List ℕ) := by
  have h15 : s ≠ 15 := fun h => (by decide : ¬IsPrimePow 15) (h ▸ hp)
  have h21 : s ≠ 21 := fun h => (by decide : ¬IsPrimePow 21) (h ▸ hp)
  have h2 := hp.ne_one
  have h0 := hp.ne_zero
  rw [Nat.coprime_two_right, Nat.odd_iff] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- All finite extensions, in the division-free exponent used in the proofs. -/
theorem norm_minimum_all {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n) :
    AsgarliGhiocaYip.isPencilMinimum E (m * normExponent (Fintype.card F) n)
      (Fintype.card F ^ (n-1) * coverNumber F m) := by
  have hs : 1 < Fintype.card F := Fintype.one_lt_card
  have rank : finrank F E = n :=
    (Nat.pow_right_injective hs) ((card_eq_pow_finrank (K := F) (V := E)).symm.trans size)
  by_cases h4 : 4 ≤ n
  · exact high_rank_norm_minimum h4 hm size
  rcases (by omega : n = 3 ∨ n = 2) with rfl | rfl
  · simpa only [Nat.reduceSub] using cubic_extension_norm_minimum rank hm
  by_cases hc : (Fintype.card F - 1).Coprime 2
  · exact coprime_norm_minimum (by decide : 2 ≤ 2) hm size hc
  by_cases h25 : 25 ≤ Fintype.card F
  · exact large_quadratic_norm_minimum hm h25 size
  obtain ⟨e,hp,he⟩ := FiniteField.card F (ringChar F)
  have hpp : IsPrimePow (Fintype.card F) := he ▸ hp.isPrimePow.pow e.2.ne'
  have hw := small_odd_scalar_witness F hm (remaining_sizes _ (by omega) hpp hc)
  simpa using quadratic_minimum_of_scalar_targets hm rank hw

/-- For q=s^n and D=(q-1)/(s-1), the true projective blocking minimum of the
mD-pencil is the number of additive subfield cosets times the optimal power cover. -/
theorem norm_power_minimum {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n) :
    AsgarliGhiocaYip.isPencilMinimum E (m * ((Fintype.card E - 1) / (Fintype.card F - 1)))
      (Fintype.card F ^ (n-1) * coverNumber F m) := by
  simpa only [normExponent_eq_div _ _ Fintype.one_lt_card, ← size] using norm_minimum_all hn hm size

theorem norm_minimum {n : ℕ} (hn : 2 ≤ n) (size : Fintype.card E = Fintype.card F ^ n) :
    AsgarliGhiocaYip.isPencilMinimum E ((Fintype.card E - 1) / (Fintype.card F - 1))
      (Fintype.card F ^ (n-1)) := by
  simpa [coverNumber_one] using norm_power_minimum hn (m := 1) (by decide) size

/-- Every optimal norm-power pencil satisfies the original no-full-projective-line condition. -/
theorem norm_power_optimal_nontrivial {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n) (S : Finset E)
    (hc : S.card = Fintype.card F ^ (n-1) * coverNumber F m) :
    AsgarliGhiocaYip.containsNoLine (AsgarliGhiocaYip.pencilPoints
      (m * ((Fintype.card E - 1) / (Fintype.card F - 1))) (S : Set E)) := by
  have hd := (normExponent_two_le (s := Fintype.card F) Fintype.one_lt_card hn).trans
    (Nat.le_mul_of_pos_left _ hm)
  have h := (AGY_containsNoLine_iff hd (S : Set E)).2 (norm_optimum_no_line hn hm size S hc)
  simpa only [normExponent_eq_div _ _ Fintype.one_lt_card, ← size] using h

end BlockingCurves.NormPencil
