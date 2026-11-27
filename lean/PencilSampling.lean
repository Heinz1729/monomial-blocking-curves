import CubicCovering

/-! Sampling horizontal and nonhorizontal lines separately for a monomial pencil. -/
namespace BlockingCurves.PencilSampling

open Finset
variable {F : Type*} [Field F] [Fintype F]

noncomputable local instance : DecidableEq F := Classical.decEq _

/-- Coordinates of an affine line, separated into the two slope classes. -/
abbrev Lines (F : Type*) [Field F] := Sum F (Fˣ × F)

def coordinates : Lines F → F × F
  | .inl b => (0,b)
  | .inr (m,b) => (m,b)

private lemma coordinates_surjective : Function.Surjective (coordinates (F := F)) := by
  rintro ⟨m,b⟩
  by_cases hm : m = 0
  · exact ⟨.inl b, by simp [coordinates, hm]⟩
  · exact ⟨.inr (Units.mk0 m hm, b), rfl⟩

def Hits (d : ℕ) (l : Lines F) (a : F) : Prop :=
  ∃ x : F, x^d - (coordinates l).1*x - (coordinates l).2 = a

noncomputable def missed (d : ℕ) (l : Lines F) : Finset F := by
  classical
  exact univ.filter (fun a => ¬ Hits d l a)

noncomputable def residual (d : ℕ) {k : ℕ} (f : Fin k → F) : Finset (Lines F) := by
  classical
  exact univ.filter (fun l => ∀ i, f i ∈ missed d l)

/-- A one-parameter repair for a family of residual affine lines, in the
original finite-field incidence relation. -/
def CommonHit (F : Type*) [Field F] (d t : ℕ) : Prop :=
  ∀ R : Finset (Lines F), R.card ≤ t → ∃ a : F, ∀ l ∈ R, Hits d l a

/-- Exact count of ordered-sample / residual-line incidences. -/
theorem residual_sum (d k : ℕ) :
    (∑ f : Fin k → F, (residual d f).card) =
      (∑ b : F, (missed d (.inl b : Lines F)).card^k) +
        ∑ l : Fˣ × F, (missed d (.inr l : Lines F)).card^k := by
  classical
  let miss (l : Lines F) (f : Fin k → F) := ∀ i, f i ∈ missed d l
  have count (l : Lines F) :
      ((univ : Finset (Fin k → F)).filter (miss l)).card = (missed d l).card^k := by
    have he : (univ : Finset (Fin k → F)).filter (miss l) =
        Fintype.piFinset (fun _ : Fin k => missed d l) := by
      ext f
      simp [miss, Fintype.mem_piFinset]
    simp [he]
  calc
    _ = ∑ l : Lines F, ((univ : Finset (Fin k → F)).filter (miss l)).card := by
      simp_rw [residual, card_eq_sum_ones, sum_filter]
      exact sum_comm
    _ = ∑ l : Lines F, (missed d l).card^k := sum_congr rfl fun l _ => count l
    _ = _ := Fintype.sum_sum_type _

/-- Sharp split first-moment threshold, including threshold zero. -/
theorem exists_sample (d k t H N : ℕ)
    (hh : ∀ b : F, (missed d (.inl b : Lines F)).card ≤ H)
    (hn : ∀ l : Fˣ × F, (missed d (.inr l : Lines F)).card ≤ N)
    (hsize : Fintype.card F * H^k + Fintype.card F * (Fintype.card F-1) * N^k <
      Fintype.card F^k * (t+1)) :
    ∃ f : Fin k → F, (residual d f).card ≤ t := by
  classical
  have hs : (∑ f : Fin k → F, (residual d f).card) < ∑ _f : Fin k → F, (t+1) := calc
    _ ≤ (∑ _b : F, H^k) + ∑ _l : Fˣ × F, N^k := by
      rw [residual_sum]
      exact add_le_add (sum_le_sum fun b _ => pow_le_pow_left' (hh b) k)
        (sum_le_sum fun l _ => pow_le_pow_left' (hn l) k)
    _ < _ := by simpa [Fintype.card_units, Nat.mul_comm (Fintype.card F-1)] using hsize
  obtain ⟨f, _, hf⟩ := exists_lt_of_sum_lt hs
  exact ⟨f, by omega⟩

private lemma assemble {d k : ℕ} (hd : 2 ≤ d) (f : Fin k → F) {S : Finset F}
    (hs : ∀ i, f i ∈ S) (hr : ∀ l ∈ residual d f, ∃ a ∈ S, Hits d l a) :
    ProjectiveBlocks d (S : Set F) := by
  classical
  apply (projectiveBlocks_iff_graphHits hd _).2
  intro m b
  obtain ⟨l, hl⟩ := coordinates_surjective (m,b)
  by_cases h : l ∈ residual d f
  · obtain ⟨a,ha,x,hx⟩ := hr l h
    rw [hl] at hx
    exact ⟨x, hx ▸ ha⟩
  · have h' : ¬ ∀ i, f i ∈ missed d l := fun he => h (mem_filter.mpr ⟨mem_univ _,he⟩)
    push_neg at h'
    obtain ⟨i,hi⟩ := h'
    simp [missed] at hi
    obtain ⟨x,hx⟩ := hi
    rw [hl] at hx
    exact ⟨x, hx ▸ hs i⟩

/-- First-moment existence on the actual projective pencil, with zero repairs. -/
theorem projective_first_moment {d : ℕ} (hd : 2 ≤ d) (k H N : ℕ)
    (hh : ∀ b : F, (missed d (.inl b : Lines F)).card ≤ H)
    (hn : ∀ l : Fˣ × F, (missed d (.inr l : Lines F)).card ≤ N)
    (hsize : Fintype.card F * H^k + Fintype.card F * (Fintype.card F-1) * N^k <
      Fintype.card F^k) :
    ∃ S : Finset F, S.card ≤ k ∧ ProjectiveBlocks d (S : Set F) := by
  classical
  obtain ⟨f,hf⟩ := exists_sample d k 0 H N hh hn (by simpa using hsize)
  have he : residual d f = ∅ := card_eq_zero.mp (by omega)
  exact ⟨univ.image f, by simpa using card_image_le (s := univ) (f := f),
    assemble hd f (fun i => mem_image_of_mem f (mem_univ i)) (by simp [he])⟩

/-- One common parameter repairs all lines left by the sample. -/
theorem projective_after_repair {d : ℕ} (hd : 2 ≤ d) (k t H N : ℕ)
    (hh : ∀ b : F, (missed d (.inl b : Lines F)).card ≤ H)
    (hn : ∀ l : Fˣ × F, (missed d (.inr l : Lines F)).card ≤ N)
    (hsize : Fintype.card F * H^k + Fintype.card F * (Fintype.card F-1) * N^k <
      Fintype.card F^k * (t+1)) (hcommon : CommonHit F d t) :
    ∃ S : Finset F, S.card ≤ k+1 ∧ ProjectiveBlocks d (S : Set F) := by
  classical
  obtain ⟨f,hf⟩ := exists_sample d k t H N hh hn hsize
  obtain ⟨a,ha⟩ := hcommon (residual d f) hf
  have hu : (univ.image f).card ≤ k := by simpa using card_image_le (s := univ) (f := f)
  exact ⟨insert a (univ.image f), (card_insert_le _ _).trans (Nat.add_le_add_right hu 1),
    assemble hd f (fun i => mem_insert_of_mem (mem_image_of_mem f (mem_univ i)))
      (fun l hl => ⟨a, mem_insert_self _ _, ha l hl⟩)⟩

end BlockingCurves.PencilSampling
