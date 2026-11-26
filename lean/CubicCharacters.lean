import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Abs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The virtual character trivial + sign − standard of S₃ is three times
the indicator of a 3-cycle. This finite character calculation applies to both
the configuration surface and the fixed-slope curve. -/
namespace BlockingCurves.CubicCharacters
open Finset BigOperators

/-- Character labels are 0 = trivial, 1 = sign, 2 = standard.
On the unramified locus their values are determined by the number of rational
roots: 0 for a 3-cycle, 1 for a transposition, 3 for the identity. -/
def character (roots : ℕ) (j : Fin 3) : ℝ :=
  if j = 0 then 1 else if j = 1 then (if roots = 1 then -1 else 1)
  else if roots = 0 then -1 else if roots = 1 then 0 else 2

def coeff (j : Fin 3) : ℝ := if j = 2 then -1 else 1
def degree (j : Fin 3) : ℝ := if j = 2 then 2 else 1

theorem cubic_character_identity (n : ℕ) :
    ∑ j : Fin 3, coeff j * character n j = if n = 0 then 3 else 0 := by
  have a : (0 : Fin 3) ≠ 2 := by decide
  have b : (1 : Fin 3) ≠ 2 := by decide
  by_cases h : n = 0 <;> by_cases h' : n = 1 <;>
    norm_num [Fin.sum_univ_succ, coeff, character, h, h', a, b, Ne.symm a, Ne.symm b]

abbrev Word (I : Type*) := I → Fin 3
variable {I X : Type*} [Fintype I] [DecidableEq I]

noncomputable def coefficient (w : Word I) : ℝ := ∏ i, coeff (w i)
noncomputable def rank (w : Word I) : ℝ := ∏ i, degree (w i)

/-- Sum of the tensor character over rational points of the open base. -/
noncomputable def characterSum (U : Finset X) (roots : X → I → ℕ) (w : Word I) : ℝ :=
  ∑ p ∈ U, ∏ i, character (roots p i) (w i)

theorem expansion (f : I → Fin 3 → ℝ) :
    (∑ w : Word I, ∏ i, f i (w i)) = ∏ i, ∑ j, f i j := by
  rw [prod_univ_sum]
  simp

theorem sum_ranks : (∑ w : Word I, rank w) = 4 ^ Fintype.card I := by
  rw [show (∑ w : Word I, rank w) = _ from expansion (fun _ : I => degree)]
  have a : (0 : Fin 3) ≠ 2 := by decide
  have b : (1 : Fin 3) ≠ 2 := by decide
  norm_num [Fin.sum_univ_succ, degree, a, b]

theorem abs_coefficient (w : Word I) : |coefficient w| = 1 := by
  classical
  rw [coefficient, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  by_cases h : w i = 2 <;> simp [coeff,h]

def nontrivialWords (I : Type*) [Fintype I] [DecidableEq I] : Finset (Word I) :=
  univ.erase 0

theorem sum_nontrivial_ranks :
    ∑ w ∈ nontrivialWords I, rank w = 4 ^ Fintype.card I - 1 := by
  have h := sum_erase_add univ (f := rank) (mem_univ (0 : Word I))
  rw [sum_ranks] at h
  have hz : rank (0 : Word I) = 1 := by simp [rank,degree, show (0:Fin 3) ≠ 2 by decide]
  rw [hz] at h
  exact eq_sub_of_add_eq h

/-- The character expansion for the actual all-no-root count, with the
constant character removed. No independence or trace estimate enters. -/
theorem centered_count (U : Finset X) (roots : X → I → ℕ) :
    (3:ℝ) ^ Fintype.card I * (U.filter (fun p => ∀ i, roots p i = 0)).card - U.card =
      ∑ w ∈ nontrivialWords I, coefficient w * characterSum U roots w := by
  classical
  have inner (p : X) : (∑ w : Word I, coefficient w * ∏ i, character (roots p i) (w i)) =
      if ∀ i, roots p i = 0 then (3:ℝ) ^ Fintype.card I else 0 := by
    simp_rw [coefficient, ← Finset.prod_mul_distrib]
    rw [expansion (fun i j => coeff j * character (roots p i) j)]
    simp_rw [cubic_character_identity]
    split_ifs with h
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)
  have allwords : (∑ w : Word I, coefficient w * characterSum U roots w) =
      (3:ℝ) ^ Fintype.card I * (U.filter (fun p => ∀ i, roots p i = 0)).card := by
    simp only [characterSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [inner]
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have constant : coefficient (0 : Word I) * characterSum U roots 0 = U.card := by
    simp [coefficient, coeff, characterSum, character, show (0:Fin 3) ≠ 2 by decide]
  have h := sum_erase_add univ (f := fun w => coefficient w * characterSum U roots w)
    (mem_univ (0 : Word I))
  dsimp only at h
  rw [allwords, constant] at h
  exact (eq_sub_of_add_eq h).symm

/-- Real part of the Frobenius trace, from complex eigenvalues with multiplicities. -/
noncomputable def realTrace (L : List ℂ) : ℝ := (L.map Complex.re).sum

theorem abs_realTrace_le (L : List ℂ) (R : ℝ) (h : ∀ z ∈ L, Complex.abs z ≤ R) :
    |realTrace L| ≤ (L.length : ℝ) * R := by
  induction L with
  | nil => simp [realTrace]
  | cons z zs ih =>
    have h₁ := (Complex.abs_re_le_abs z).trans (h z (by simp))
    have h₂ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [show realTrace (z :: zs) = z.re + realTrace zs by simp [realTrace]]
    apply (abs_add _ _).trans
    simpa [Nat.cast_add, add_mul, add_comm] using add_le_add h₁ h₂

end BlockingCurves.CubicCharacters
