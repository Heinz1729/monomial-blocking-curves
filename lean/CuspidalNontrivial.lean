import CuspidalGeneral
import Paper

namespace BlockingCurves.CuspidalGeneral

open Finset

variable {E : Type*} [Field E]

/-- Each rational line contains a point outside the union of the projective cusp curves. -/
def NoFullLine (d : ℕ) (S : Set E) : Prop :=
  ∀ a b c : E, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
    ∃ X Y Z : E, (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) ∧ a*X+b*Y+c*Z=0 ∧
      ∀ α ∈ S, (Y+α*Z)^(d-1)*Z ≠ X^d

/-- Only vertical affine lines require a finite count: a member occupies
at most d-1 affine points on each of them. -/
theorem noFullLine_of_card [Fintype E] {d : ℕ} (hd : 2 ≤ d) (S : Finset E)
    (small : S.card * (d-1) < Fintype.card E) : NoFullLine d (S : Set E) := by
  classical
  intro a b c _
  by_cases hb : b=0
  · subst b
    by_cases ha : a=0
    · subst a
      exact ⟨1,0,0,Or.inl one_ne_zero,by simp,fun _ _ => by simp⟩
    · let x := -c/a
      let R := (Polynomial.nthRoots (d-1) (x^d)).toFinset
      let V := S.biUnion (fun α => R.image (fun r => r-α))
      have rcard : R.card ≤ d-1 :=
        (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
      have many : V.card < Fintype.card E :=
        (card_biUnion_le_card_mul S _ (d-1) fun _ _ => card_image_le.trans rcard).trans_lt small
      obtain ⟨y,hy⟩ : ∃ y : E, y ∉ V := by
        by_contra! all
        rw [eq_univ_of_forall all,card_univ] at many
        exact (lt_irrefl _) many
      refine ⟨x,y,1,Or.inr (Or.inr one_ne_zero),?_,?_⟩
      · dsimp [x]
        field_simp [ha]
        ring
      · intro α hα he
        apply hy
        have hr : y+α ∈ R := by
          apply Multiset.mem_toFinset.mpr
          apply (Polynomial.mem_nthRoots (by omega : 0<d-1)).mpr
          simpa using he
        exact mem_biUnion.mpr ⟨α,hα,mem_image.mpr ⟨y+α,hr,by ring⟩⟩
  · exact ⟨b,-a,0,Or.inl hb,by ring,fun _ _ => by simp [(pow_ne_zero d hb).symm]⟩

theorem quadratic_three_nontrivial [Fintype E] {s : ℕ}
    (hs : 2 ≤ s) (size : Fintype.card E=s^2) (S : Finset E) (hc : S.card=3) :
    NoFullLine s (S : Set E) := by
  apply noFullLine_of_card hs
  rw [size,hc]
  obtain ⟨k,rfl⟩ : ∃ k, s=k+2 := ⟨s-2,by omega⟩
  rw [show k+2-1=k+1 by omega]
  nlinarith

theorem cubic_four_nontrivial [Fintype E] {s : ℕ}
    (hs : 2 ≤ s) (size : Fintype.card E=s^3) (S : Finset E) (hc : S.card=4) :
    NoFullLine s (S : Set E) := by
  apply noFullLine_of_card hs
  rw [size,hc]
  obtain ⟨k,rfl⟩ : ∃ k, s=k+2 := ⟨s-2,by omega⟩
  rw [show k+2-1=k+1 by omega]
  nlinarith [Nat.zero_le (k^3),Nat.zero_le (k^2)]

/-- The graph side of the comparison on the very same finite field, with
the ambient extension degree retained as a parameter. -/
theorem relative_graph_minimum (F : Type*) [Field F] [Fintype F] [Fintype E] [Algebra F E] :
    IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧ ProjectiveBlocks (Fintype.card F) (S : Set E)}
      ((Fintype.card F-1) * FiniteDimensional.finrank F E + 1) := by
  apply projective_minimum_of_graph (show 2 ≤ Fintype.card F from Fintype.one_lt_card)
  simpa using (iterated_frobenius_minimum (K := F) (E := E) 1)

end BlockingCurves.CuspidalGeneral
