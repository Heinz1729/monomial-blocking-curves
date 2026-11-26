import CubicCovering

/-! Ordered sampling followed by a single extra cubic (§17). -/

namespace BlockingCurves.CubicAlteration

open Finset CubicCovering

variable {F : Type*} [Field F] [Fintype F]

/-- Nonhorizontal affine lines, indexed without duplicate slopes. -/
abbrev Line (F : Type*) [Field F] := Fˣ × F

/-- Parameters that meet the line represented by `l`. -/
def Hits (a : F) (l : Line F) : Prop := ∃ x : F, x^3 - (l.1:F)*x - l.2 = a

/-- One additional cubic can meet every line in any residual family of size at most `t`. -/
def CommonHit (F : Type*) [Field F] (t : ℕ) : Prop :=
  ∀ R : Finset (Line F), R.card ≤ t → ∃ a : F, ∀ l ∈ R, Hits a l

/-- A residual line is missed by all entries of this ordered sample. -/
noncomputable def residual {k : ℕ} (f : Fin k → F) : Finset (Line F) := by
  classical
  exact univ.filter fun l => ∀ i, f i ∈ missedParameters (l.1:F) l.2

/-- First-moment sampling, as a finite incidence count. The threshold may
be attained, and samples can have repetitions or even be empty. -/
theorem exists_sample (k t : ℕ) (hq : Fintype.card F % 3 = 2)
    (hsize : Fintype.card F * (Fintype.card F - 1) * ((Fintype.card F + 1)/3)^k ≤
      (Fintype.card F)^k * t) :
    ∃ f : Fin k → F, (residual f).card ≤ t := by
  classical
  let missed (l : Line F) (f : Fin k → F) :=
    ∀ i, f i ∈ missedParameters (l.1:F) l.2
  have count (l : Line F) :
      ((univ : Finset (Fin k → F)).filter (missed l)).card ≤ ((Fintype.card F+1)/3)^k := by
    have he : (univ : Finset (Fin k → F)).filter (missed l) =
        Fintype.piFinset (fun _ : Fin k => missedParameters (l.1:F) l.2) := by
      ext f
      simp [missed, Fintype.mem_piFinset]
    rw [he]
    have hb := line_miss_bound (l.1:F) l.2 hq
    have hl : (missedParameters (l.1:F) l.2).card ≤ (Fintype.card F+1)/3 := by omega
    simpa using pow_le_pow_left' hl k
  have hc : Fintype.card (Line F) = Fintype.card F * (Fintype.card F - 1) := by
    simp [Line, Fintype.card_units, Nat.mul_comm]
  have total : (∑ f : Fin k → F, (residual f).card) ≤ ∑ _f : Fin k → F, t := calc
    _ = ∑ l : Line F, ((univ : Finset (Fin k → F)).filter (missed l)).card := by
      simp_rw [residual, card_eq_sum_ones, sum_filter]
      exact sum_comm
    _ ≤ ∑ _l : Line F, ((Fintype.card F + 1)/3)^k := sum_le_sum fun l _ => count l
    _ ≤ _ := by simpa [hc] using hsize
  obtain ⟨f, _, hf⟩ := exists_le_of_sum_le univ_nonempty total
  exact ⟨f, hf⟩

/-- The extra parameter itself deals with the horizontal slopes, even if the
ordered sample is empty. Vertical lines and infinity are covered by the projective bridge. -/
theorem complete_sample {k t : ℕ} (f : Fin k → F) (hq : Fintype.card F % 3 = 2)
    (hf : (residual f).card ≤ t) (hcommon : CommonHit F t) :
    ∃ S : Finset F, S.card ≤ k+1 ∧ ProjectiveBlocks 3 (S : Set F) := by
  classical
  obtain ⟨a,ha⟩ := hcommon (residual f) hf
  refine ⟨insert a (univ.image f), ?_, (projectiveBlocks_iff_graphHits (by decide) _).2 ?_⟩
  · have hu : (univ.image f).card ≤ k := by simpa using card_image_le (s := univ) (f := f)
    exact (card_insert_le _ _).trans (Nat.add_le_add_right hu 1)
  · intro m b
    by_cases hm : m = 0
    · obtain ⟨x,hx⟩ := CubicSlope.cube_surjective hq (a+b)
      exact ⟨x, by simp [hm, hx]⟩
    · let l : Line F := (Units.mk0 m hm, b)
      by_cases hl : l ∈ residual f
      · obtain ⟨x,hx⟩ := ha l hl
        exact ⟨x, mem_insert.mpr (Or.inl hx)⟩
      · have hn : ¬ ∀ i, f i ∈ missedParameters m b := by
          intro hi
          exact hl (mem_filter.mpr ⟨mem_univ _,hi⟩)
        push_neg at hn
        obtain ⟨i,hi⟩ := hn
        simp [missedParameters] at hi
        obtain ⟨x,hx⟩ := hi
        exact ⟨x, mem_insert.mpr (Or.inr (mem_image.mpr ⟨i,mem_univ _,hx.symm⟩))⟩

/-- The finite alteration bound. Geometry enters only through the simultaneous
hit of a residual family. No independence between distinct lines is required. -/
theorem projective_cover_after_repair (k t : ℕ) (hq : Fintype.card F % 3 = 2)
    (hsize : Fintype.card F * (Fintype.card F - 1) * ((Fintype.card F+1)/3)^k ≤
      (Fintype.card F)^k * t) (hcommon : CommonHit F t) :
    ∃ S : Finset F, S.card ≤ k+1 ∧ ProjectiveBlocks 3 (S : Set F) := by
  obtain ⟨f,hf⟩ := exists_sample k t hq hsize
  exact complete_sample f hq hf hcommon

end BlockingCurves.CubicAlteration
