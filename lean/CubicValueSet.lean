import CubicSlope
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators

/-! The number of missed values of a depressed cubic, via its collision conic. -/
namespace BlockingCurves.CubicValueSet

variable {F : Type*} [Field F] [Fintype F]

def normForm (x y : F) := x^2 + x*y + y^2
def cubic (m b x : F) := x^3 - m*x - b

noncomputable section
open Classical
local instance : DecidableEq F := Classical.decEq _

def conic (m : F) := (Finset.univ : Finset (F × F)).filter
  (fun p => normForm p.1 p.2 = m)

lemma unit_form_ne (hq : Fintype.card F % 3 = 2) (s : F) : 1+s+s^2 ≠ 0 := by
  intro hs
  have hi : Function.Injective (fun x : F => x^3) :=
    Finite.injective_iff_surjective.mpr (CubicSlope.cube_surjective hq)
  have hcube : s^3 = 1^3 := by linear_combination (s-1)*hs
  have hs1 : s = 1 := hi hcube
  subst s
  have hz : (3:F) = 0 := by linear_combination hs
  have hc := CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_three hz
  obtain ⟨n, _, hcard⟩ := FiniteField.card F (ringChar F)
  rw [hc] at hcard
  have hd : 3 ∣ Fintype.card F := by
    rw [hcard]
    exact dvd_pow_self _ n.property.ne'
  omega

/-- Draw all lines through one rational point; its tangent parametrizes the point itself. -/
lemma conic_card_le (m : F) (hq : Fintype.card F % 3 = 2) :
    (conic m).card ≤ Fintype.card F + 1 := by
  classical
  by_cases hC : (conic m).Nonempty
  · obtain ⟨⟨x,y⟩, hp⟩ := hC
    have hp' : normForm x y = m := (Finset.mem_filter.mp hp).2
    let step (s : F) := -(2*x+y+s*(x+2*y))/(1+s+s^2)
    let atDir : Option F → F × F
      | none => (x, y-(x+2*y))
      | some s => (x+step s, y+s*step s)
    have hsub : conic m ⊆ Finset.univ.image atDir := by
      rintro ⟨v,w⟩ hvw
      have he := (Finset.mem_filter.mp hvw).2
      change normForm v w = m at he
      apply Finset.mem_image.mpr
      by_cases hv : v = x
      · subst v
        have hprod : (w-y)*(w+y+x)=0 := by
          dsimp [normForm] at he hp'
          linear_combination he-hp'
        rcases mul_eq_zero.mp hprod with h | h
        · have hw := sub_eq_zero.mp h
          subst w
          by_cases hB : x+2*y=0
          · exact ⟨none, Finset.mem_univ _, by simp [atDir,hB]⟩
          · let s := -(2*x+y)/(x+2*y)
            have hs : 2*x+y+s*(x+2*y)=0 := by dsimp [s]; field_simp; ring
            have hj : step s = 0 := by dsimp only [step]; rw [hs, neg_zero, zero_div]
            exact ⟨some s, Finset.mem_univ _, by simp [atDir,hj]⟩
        · exact ⟨none, Finset.mem_univ _, Prod.ext rfl (by dsimp [atDir]; linear_combination -h)⟩
      · let s := (w-y)/(v-x)
        have hd : v-x ≠ 0 := sub_ne_zero.mpr hv
        have hdy : s*(v-x)=w-y := div_mul_cancel₀ _ hd
        have hy : w = y+s*(v-x) := by linear_combination -hdy
        have hprod : (v-x)*((v-x)*(1+s+s^2)+(2*x+y+s*(x+2*y)))=0 := by
          dsimp [normForm] at he hp'
          rw [hy] at he
          linear_combination he-hp'
        have hf := (mul_eq_zero.mp hprod).resolve_left hd
        have hjump : step s = v-x := by
          apply (div_eq_iff (unit_form_ne hq s)).mpr
          linear_combination -hf
        exact ⟨some s, Finset.mem_univ _, Prod.ext (by dsimp [atDir]; rw [hjump]; ring)
          (by dsimp [atDir]; rw [hjump, ← hy])⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hC]

def rootsAt (m b a : F) := Finset.univ.filter (fun x => cubic m b x = a)
def pairsAt (m b a : F) := (conic m).filter (fun p => cubic m b p.1 = a)

private lemma collision {m b x y : F} (hxy : x ≠ y) (he : cubic m b x = cubic m b y) :
    normForm x y = m := by
  have hp : (x-y)*(normForm x y-m) = 0 := by
    dsimp [cubic] at he
    dsimp [normForm]
    linear_combination he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hxy))

/-- A fibre of size two supplies the missing diagonal point of the conic:
the third root, counted with multiplicity, equals one of its two rational roots. -/
lemma fibre_budget (m b a : F) :
    3*(rootsAt m b a).card + (if (rootsAt m b a).card = 0 then 3 else 0)
      ≤ 3 + (pairsAt m b a).card := by
  classical
  let R := rootsAt m b a
  change 3*R.card + (if R.card = 0 then 3 else 0) ≤ 3 + _
  have root {x : F} (hx : x ∈ R) : cubic m b x = a := (Finset.mem_filter.mp hx).2
  have hpair : R.offDiag ⊆ pairsAt m b a := by
    rintro ⟨x,y⟩ h
    obtain ⟨hx,hy,hxy⟩ := Finset.mem_offDiag.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, collision hxy ((root hx).trans (root hy).symm)⟩, root hx⟩
  by_cases h2 : R.card = 2
  · obtain ⟨x,y,hxy,hR⟩ := Finset.card_eq_two.mp h2
    have hx : x ∈ R := by simp [hR]
    have hy : y ∈ R := by simp [hR]
    have hn := collision hxy ((root hx).trans (root hy).symm)
    have hthird : -x-y ∈ R := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← root hx]
      dsimp [cubic, normForm] at *
      linear_combination (-2*x-y)*hn
    rw [hR, Finset.mem_insert, Finset.mem_singleton] at hthird
    have hd : ∃ t ∈ R, normForm t t = m := by
      rcases hthird with hz | hz
      · refine ⟨x,hx,?_⟩
        dsimp [normForm] at *
        linear_combination hn - (x-y)*hz
      · refine ⟨y,hy,?_⟩
        dsimp [normForm] at *
        linear_combination hn - (y-x)*hz
    obtain ⟨t,ht,hd⟩ := hd
    have hstrict : R.offDiag ⊂ pairsAt m b a := by
      apply Finset.ssubset_iff_of_subset hpair |>.2
      refine ⟨(t,t),Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, root ht⟩, ?_⟩
      simp [Finset.mem_offDiag]
    have hl := Finset.card_lt_card hstrict
    rw [Finset.offDiag_card, h2] at hl
    simp [h2]
    omega
  · have hl := Finset.card_le_card hpair
    rw [Finset.offDiag_card] at hl
    by_cases hn : R.card ≤ 1
    · split <;> omega
    · have hh : 3 ≤ R.card := by omega
      have hm := Nat.mul_le_mul_right (R.card-1) hh
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib] at hm
      simp only [Nat.mul_one] at hm
      split <;> omega

/-- All slopes and intercepts in either characteristic, with no value-set input. -/
theorem three_mul_missed_le (m b : F) (hq : Fintype.card F % 3 = 2) :
    3 * (Finset.univ.filter (fun a : F => ¬ ∃ x : F, x^3-m*x-b=a)).card ≤ Fintype.card F+1 := by
  classical
  have hroots : Fintype.card F = ∑ a : F, (rootsAt m b a).card := by
    simpa [rootsAt] using Finset.card_eq_sum_card_fiberwise
      (f := cubic m b) (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hpairs : (conic m).card = ∑ a : F, (pairsAt m b a).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (f := fun p : F × F => cubic m b p.1) (fun _ _ => Finset.mem_univ _)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => fibre_budget m b a)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hroots, ← hpairs] at hs
  have he : ∀ a : F, (rootsAt m b a).card = 0 ↔ ¬ ∃ x : F, x^3-m*x-b=a := by
    intro a
    simp [Finset.card_eq_zero, rootsAt, Finset.filter_eq_empty_iff, cubic]
  simp_rw [he] at hs
  rw [← Finset.sum_filter] at hs
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hs
  have h := conic_card_le m hq
  simp only [Nat.cast_id] at hs
  omega

end
end BlockingCurves.CubicValueSet
