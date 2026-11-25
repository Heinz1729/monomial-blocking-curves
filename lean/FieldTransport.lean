import Paper

namespace BlockingCurves

variable {E K : Type*} [Field E] [Field K]

/-- The homogeneous pencil incidence predicate is invariant under a field isomorphism. -/
theorem projectiveBlocks_image_iff (φ : E ≃+* K) {d : ℕ} (hd : 2 ≤ d) (S : Set E) :
    ProjectiveBlocks d (φ '' S) ↔ ProjectiveBlocks d S := by
  simp only [projectiveBlocks_iff_graphHits hd]
  constructor
  · intro h m b
    obtain ⟨y, s, hs, he⟩ := h (φ m) (φ b)
    refine ⟨φ.symm y, ?_⟩
    have hval : (φ.symm y)^d - m * φ.symm y - b = s := by
      apply φ.injective
      simpa using he.symm
    rwa [hval]
  · intro h m b
    obtain ⟨x, hx⟩ := h (φ.symm m) (φ.symm b)
    exact ⟨φ x, _, hx, by simp⟩

private theorem transfer_parameters (e : E ≃+* K) {d : ℕ} (hd : 2 ≤ d)
    (A : Finset E) (ha : ProjectiveBlocks d (A : Set E)) :
    ∃ V : Finset K, V.card = A.card ∧ ProjectiveBlocks d (V : Set K) := by
  refine ⟨A.map e.toEquiv.toEmbedding, Finset.card_map _, ?_⟩
  rw [Finset.coe_map]
  exact (projectiveBlocks_image_iff e hd (A : Set E)).mpr ha

theorem projective_minimum_ringEquiv (φ : E ≃+* K) {d n : ℕ} (hd : 2 ≤ d)
    (h : IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧ ProjectiveBlocks d (S : Set E)} n) :
    IsLeast {r : ℕ | ∃ S : Finset K, S.card = r ∧ ProjectiveBlocks d (S : Set K)} n := by
  constructor
  · obtain ⟨S, hc, hs⟩ := h.1
    simpa [hc] using transfer_parameters φ hd S hs
  · rintro r ⟨A, rfl, ha⟩
    exact h.2 (transfer_parameters φ.symm hd A ha)

end BlockingCurves
