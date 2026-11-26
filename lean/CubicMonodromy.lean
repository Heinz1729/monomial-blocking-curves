import CubicCharacters
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Perm.Sign

/-! Geometric monodromy acts on the three roots in each coordinate.
The sum of a nontrivial tensor character over the full product is zero. -/
namespace BlockingCurves.CubicMonodromy
open Finset BigOperators CubicCharacters

abbrev SymThree := Equiv.Perm (Fin 3)
def fixedRoots (g : SymThree) : ℕ := (univ.filter fun x => g x = x).card

theorem cycle_counts :
    ((univ : Finset SymThree).filter (fun g => fixedRoots g = 0)).card = 2 ∧
    ((univ : Finset SymThree).filter (fun g => fixedRoots g = 1)).card = 3 ∧
    ((univ : Finset SymThree).filter (fun g => fixedRoots g = 3)).card = 1 ∧
    ∀ g : SymThree, fixedRoots g = 0 ∨ fixedRoots g = 1 ∨ fixedRoots g = 3 := by decide

private def intCharacter (j : Fin 3) (n : ℕ) : ℤ :=
  if j = 0 then 1 else if j = 1 then (if n = 1 then -1 else 1)
  else if n = 0 then -1 else if n = 1 then 0 else 2

theorem character_orthogonality (j : Fin 3) :
    (∑ g : SymThree, character (fixedRoots g) j) = if j = 0 then 6 else 0 := by
  have integral : ∀ i : Fin 3,
      (∑ g : SymThree, intCharacter i (fixedRoots g)) = if i = 0 then 6 else 0 := by decide
  have cast (n : ℕ) : (intCharacter j n : ℝ) = character n j := by
    simp [intCharacter, character, apply_ite Int.cast]
  simp_rw [← cast, ← Int.cast_sum]
  rw [integral]
  split_ifs <;> norm_num

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Each coordinate cover is transitive on its three roots. -/
def transitiveFactors (G : Subgroup (I → SymThree)) : Prop :=
  ∀ i (a b : Fin 3), ∃ h : G, ((h : I → SymThree) i) a = b

/-- An inertia transposition moves roots in just one coordinate. -/
def supportedInertia (G : Subgroup (I → SymThree)) : Prop :=
  ∀ i : I, ∃ s : SymThree, fixedRoots s = 1 ∧ (Pi.mulSingle i s : I → SymThree) ∈ G

private theorem conjugate_swap :
    ∀ (s : SymThree) (x y : Fin 3), fixedRoots s = 1 → x ≠ y →
      ∃ a b : Fin 3, ∀ u : SymThree, u a = b →
        ∀ z : Fin 3, (u*s*u⁻¹) z = Equiv.swap x y z := by
  set_option maxRecDepth 4096 in decide

/-- Transitivity in each factor and one isolated inertia transposition per
factor imply the entire product. This includes the shared point at infinity. -/
theorem full_of_inertia (G : Subgroup (I → SymThree))
    (htr : transitiveFactors G) (hin : supportedInertia G) : G = ⊤ := by
  apply eq_top_iff.mpr
  intro g _
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro i
  obtain ⟨s, hs, hsingle⟩ := hin i
  apply Equiv.Perm.swap_induction_on (P := fun f => (Pi.mulSingle i f : I → SymThree) ∈ G) (g i)
  · simpa using G.one_mem
  · intro f x y hxy hf
    obtain ⟨a,b,hab⟩ := conjugate_swap s x y hs hxy
    obtain ⟨u,hu⟩ := htr i a b
    have he : (u : I → SymThree) * Pi.mulSingle i s * (u : I → SymThree)⁻¹ =
        Pi.mulSingle i (Equiv.swap x y) := by
      funext j
      by_cases hij : j = i
      · subst j
        simpa using Equiv.ext (hab ((u : I → SymThree) i) hu)
      · simp [Pi.mulSingle_eq_of_ne hij]
    rw [Pi.mulSingle_mul, ← he]
    exact G.mul_mem (G.mul_mem (G.mul_mem u.property hsingle) (G.inv_mem u.property)) hf

def value (w : Word I) (g : I → SymThree) : ℝ :=
  ∏ i, character (fixedRoots (g i)) (w i)

theorem sum_eq_zero (w : Word I) (hw : w ∈ nontrivialWords I) :
    ∑ g : I → SymThree, value w g = 0 := by
  classical
  have hn : w ≠ 0 := (Finset.mem_erase.mp hw).1
  obtain ⟨i,hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  unfold value
  have fac := Finset.prod_univ_sum (fun _ : I => (univ : Finset SymThree))
    (fun i g => character (fixedRoots g) (w i))
  simp only [Fintype.piFinset_univ] at fac
  rw [← fac]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [character_orthogonality,hi]

/-- Numerical Poincaré duality for the top compactly supported cohomology,
written using the average character of geometric monodromy. -/
def topMultiplicity (G : Subgroup (I → SymThree)) (w : Word I) (b : ℕ) : Prop := by
  classical
  exact (Fintype.card G : ℝ) * b = ∑ g : G, value w g

theorem top_eq_zero (G : Subgroup (I → SymThree)) (hfull : G = ⊤)
    {w : Word I} (hw : w ∈ nontrivialWords I) {b : ℕ} (hm : topMultiplicity G w b) :
    b = 0 := by
  classical
  subst G
  unfold topMultiplicity at hm
  let e : (⊤ : Subgroup (I → SymThree)) ≃* (I → SymThree) := Subgroup.topEquiv
  have he : (∑ g : (⊤ : Subgroup (I → SymThree)), value w g) =
      ∑ g : I → SymThree, value w g := e.toEquiv.sum_comp (value w)
  rw [he, sum_eq_zero w hw] at hm
  have hc : (0 : ℝ) < Fintype.card (⊤ : Subgroup (I → SymThree)) := by exact_mod_cast Fintype.card_pos
  exact_mod_cast (mul_eq_zero.mp hm).resolve_left hc.ne'

end BlockingCurves.CubicMonodromy
