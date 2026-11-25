import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace BlockingCurves.CubicSlope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- All parameter differences, including zero whenever the set is nonempty. -/
def differences (S : Finset F) : Finset F :=
  (S.product S).image (fun ab => ab.1 - ab.2)

/-- The two finite critical values of the translate with parameter a and slope 3u². -/
def branchValues (u a : F) : Set F := {2*u^3 - a, -(2*u^3) - a}

theorem card_differences_le (S : Finset F) : (differences S).card ≤ S.card^2 := by
  calc
    (differences S).card ≤ (S.product S).card := Finset.card_image_le
    _ = S.card^2 := by simpa only [pow_two] using Finset.card_product S S

/-- The equation and its derivative in x vanish together exactly at the listed intercepts. -/
theorem critical_value_iff (h3 : (3 : F) ≠ 0) (u a b : F) :
    (∃ x : F, x^3 - 3*u^2*x = b+a ∧ 3*x^2 = 3*u^2) ↔ b ∈ branchValues u a := by
  change _ ↔ b = 2*u^3-a ∨ b = -(2*u^3)-a
  constructor
  · rintro ⟨x, hx, hd⟩
    have he : x^2 = u^2 := mul_left_cancel₀ h3 hd
    rcases ((Commute.all x u).sq_eq_sq_iff_eq_or_eq_neg.mp he) with h | h <;> subst x
    · right; linear_combination -hx
    · left; linear_combination -hx
  · rintro (rfl | rfl)
    · exact ⟨-u, by ring, by ring⟩
    · exact ⟨u, by ring, rfl⟩

private theorem difference_mem {S : Finset F} {a b : F} (ha : a ∈ S) (hb : b ∈ S) :
    a-b ∈ differences S :=
  Finset.mem_image.mpr ⟨(a,b), Finset.mk_mem_product ha hb, rfl⟩

/-- For q ≡ 2 mod 3 the cube map is onto, by Fermat's identity on nonzero elements. -/
theorem cube_surjective (hq : Fintype.card F % 3 = 2) :
    Function.Surjective (fun u : F => u^3) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp⟩
  let q := Fintype.card F
  let k := 2 * (q / 3) + 1
  have he : k * 3 = ((q-1)*2) + 1 := by
    dsimp [k, q]
    omega
  refine ⟨x^k, ?_⟩
  change (x^k)^3 = x
  rw [← pow_mul, he, pow_succ, pow_mul, FiniteField.pow_card_sub_one_eq_one x hx]
  simp

/-- A proper difference set leaves a nonzero u for which distinct translates
have disjoint finite branch loci, in characteristic greater than three. -/
theorem exists_collision_free {p : ℕ} [CharP F p] (hp : 3 < p)
    (hq : Fintype.card F % 3 = 2) (S : Finset F)
    (hsmall : (differences S).card < Fintype.card F) :
    ∃ u : F, u ≠ 0 ∧ 4*u^3 ∉ differences S ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (branchValues u a) (branchValues u b) := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨t, ht⟩ : ∃ t : F, t ∉ differences S := by
      by_contra! hall
      have he := Finset.eq_univ_of_forall hall
      rw [he, Finset.card_univ] at hsmall
      exact (Nat.lt_irrefl _ hsmall)
    obtain ⟨a, ha⟩ := hs
    have ht0 : t ≠ 0 := by
      intro h
      exact ht (by simpa [h] using difference_mem ha ha)
    have h2 : (2 : F) ≠ 0 := by
      intro h
      have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
    have h4 : (4 : F) ≠ 0 := by
      rw [show (4:F) = 2*2 by ring]
      exact mul_ne_zero h2 h2
    obtain ⟨u, hu⟩ := cube_surjective hq (t / 4)
    change u^3 = t / 4 at hu
    have htu : 4*u^3 = t := by rw [hu, mul_comm, div_mul_cancel₀ _ h4]
    refine ⟨u, ?_, htu ▸ ht, ?_⟩
    · intro h
      exact ht0 (by simpa [h] using htu.symm)
    · intro a ha b hb hab
      apply Set.disjoint_left.mpr
      intro x hax hbx
      change x = 2*u^3-a ∨ x = -(2*u^3)-a at hax
      change x = 2*u^3-b ∨ x = -(2*u^3)-b at hbx
      rcases hax with hax | hax <;> rcases hbx with hbx | hbx
      · exact hab (by linear_combination hax - hbx)
      · apply ht
        rw [← htu, show 4*u^3 = a-b by linear_combination hbx - hax]
        exact difference_mem ha hb
      · apply ht
        rw [← htu, show 4*u^3 = b-a by linear_combination hax - hbx]
        exact difference_mem hb ha
      · exact hab (by linear_combination hax - hbx)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    refine ⟨1, one_ne_zero, ?_, by simp⟩
    intro h
    obtain ⟨z, hz, _⟩ := Finset.mem_image.mp h
    exact Finset.not_mem_empty _ (Finset.mem_product.mp hz).1

#print axioms cube_surjective
#print axioms critical_value_iff
#print axioms exists_collision_free

end BlockingCurves.CubicSlope
