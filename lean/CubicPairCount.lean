import CubicSlope
import Projective
import CubicAsymptotics

namespace BlockingCurves.CubicPairCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Normalized intercept of §12 in ordered coordinates. -/
def parameter (v w a : F) : F := 2 * (v+w+2*a) / (v-w)

/-- Rational points counted by N in (12.1), using the no-root test for cubics. -/
def escapePairs (S : Finset F) : Finset (F × F) := Finset.univ.filter fun P =>
  P.1 ≠ P.2 ∧ (∀ a ∈ S, P.1 ≠ -a ∧ P.2 ≠ -a) ∧
    ∀ a ∈ S, ∀ t : F, t^3 - 3*t ≠ parameter P.1 P.2 a

def escapeCount (S : Finset F) : ℕ := (escapePairs S).card

theorem escapeCount_eq_zero_of_blocks (S : Finset F) (h2 : (2 : F) ≠ 0)
    (hq : Fintype.card F % 3 = 2) (hs : ProjectiveBlocks 3 (S : Set F)) :
    escapeCount S = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  rintro ⟨v,w⟩ hP
  obtain ⟨hd, _, hn⟩ := (Finset.mem_filter.mp hP).2
  have hd' : v - w ≠ 0 := sub_ne_zero.mpr hd
  have h4 : (4 : F) ≠ 0 := by rw [show (4:F) = 2*2 by ring]; exact mul_ne_zero h2 h2
  obtain ⟨u, hu⟩ := CubicSlope.cube_surjective hq ((v-w)/4)
  change u^3 = (v-w)/4 at hu
  have hdiff : v-w = 4*u^3 := by rw [hu, mul_comm, div_mul_cancel₀ _ h4]
  have hu0 : u ≠ 0 := by intro h; simp [h] at hdiff; exact hd' hdiff
  obtain ⟨x, hx⟩ := (projectiveBlocks_iff_graphHits (by decide : 2 ≤ 3) _).mp hs
    (3*u^2) ((v+w)/2)
  apply hn _ hx (x/u)
  dsimp [parameter]
  rw [hdiff]
  field_simp
  ring

/-- The sole geometric estimate assumed here is (12.1), on the actual count for S. -/
theorem blocking_card_lower_of_trace (S : Finset F) (h2 : (2 : F) ≠ 0)
    (hq : Fintype.card F % 3 = 2) (hlarge : 16 ≤ (Fintype.card F : ℝ))
    (htrace : CubicAsymptotics.traceDeviation (Fintype.card F) S.card (escapeCount S))
    (hs : ProjectiveBlocks 3 (S : Set F)) :
    (Real.log (Fintype.card F) - 2 * Real.log (Real.log (Fintype.card F))) /
      Real.log 4 - 5 < (S.card : ℝ) := by
  rw [escapeCount_eq_zero_of_blocks S h2 hq hs] at htrace
  exact CubicAsymptotics.cubic_lower_of_trace _ _ hlarge htrace

/-- Unbranched intercepts at slope one with no root in any translate (§18). -/
def fixedEscapeCount (S : Finset F) : ℕ :=
  (Finset.univ.filter fun b : F =>
    ∀ a ∈ S, b ≠ -a ∧ ∀ x : F, x^3 - x - b ≠ a).card

theorem fixed_blocking_card_lower_of_trace (S : Finset F)
    (hlarge : 16 ≤ (Fintype.card F : ℝ))
    (htrace : CubicAsymptotics.fixedSlopeDeviation (Fintype.card F) S.card (fixedEscapeCount S))
    (hs : ProjectiveBlocks 3 (S : Set F)) :
    (Real.log (Fintype.card F) - 2 * Real.log (Real.log (Fintype.card F))) /
      Real.log 16 < (S.card : ℝ) := by
  have hz : fixedEscapeCount S = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro b hb
    obtain ⟨x, hx⟩ := (projectiveBlocks_iff_graphHits (by decide : 2 ≤ 3) _).mp hs 1 b
    have hx' : x^3 - x - b ∈ S := by simpa using hx
    exact ((Finset.mem_filter.mp hb).2 _ hx').2 x rfl
  rw [hz] at htrace
  exact CubicAsymptotics.fixedSlope_lower_of_trace _ _ hlarge htrace

end BlockingCurves.CubicPairCount
