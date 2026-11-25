import ProblemStatement
import Projective

namespace BlockingCurves

variable {F : Type*} [Field F]

theorem graphHits_iff_AGY (d : ℕ) (S : Set F) :
    GraphHits (fun x : F => x ^ d) S ↔ AsgarliGhiocaYip.hitsValueSets d S := by
  constructor
  · intro h u v
    obtain ⟨x, hx⟩ := h (-u) (-v)
    refine ⟨_, ?_, x, rfl⟩
    simpa only [neg_mul, sub_neg_eq_add] using hx
  · intro h m b
    obtain ⟨_, hS, x, rfl⟩ := h (-m) (-b)
    refine ⟨x, ?_⟩
    simpa only [neg_mul, ← sub_eq_add_neg] using hS

/-- The manuscript's homogeneous blocking predicate answers the source specification. -/
theorem projectiveBlocks_iff_AGY {d : ℕ} (hd : 2 ≤ d) (S : Set F) :
    ProjectiveBlocks d S ↔ AsgarliGhiocaYip.hitsValueSets d S :=
  (projectiveBlocks_iff_graphHits hd S).trans (graphHits_iff_AGY d S)

end BlockingCurves
