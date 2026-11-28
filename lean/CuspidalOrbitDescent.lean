import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Dynamics.PeriodicPts
import Mathlib.Algebra.Field.Subfield

/-! An interpolation description of finite orbits in a field with an
automorphism. It works when the characteristic divides the orbit length. -/
namespace BlockingCurves.CuspidalDescent
open Polynomial Finset Function
noncomputable section
variable {E : Type*} [Field E]

def fixedField (τ : E ≃+* E) : Subfield E := τ.toRingHom.eqLocusField (RingHom.id E)

theorem mem_fixedField (τ : E ≃+* E) (x : E) : x ∈ fixedField τ ↔ τ x = x := Iff.rfl

/-- Interpolate the orbit of x at the orbit of a marker z of full period.
Uniqueness forces every coefficient of the interpolant to be invariant. -/
def orbitPolynomial (τ : E ≃+* E) (r : ℕ) (z x : E) : E[X] :=
  Lagrange.interpolate (univ : Finset (Fin r)) (fun i => (τ : E → E)^[i.val] z)
    (fun i => (τ : E → E)^[i.val] x)

theorem orbitPolynomial_fixed_eval (τ : E ≃+* E) {r : ℕ} (hr : 0 < r) {z x : E}
    (hz : IsPeriodicPt τ r z) (hx : IsPeriodicPt τ r x)
    (inj : Injective (fun i : Fin r => (τ : E → E)^[i.val] z)) :
    (orbitPolynomial τ r z x).map τ.toRingHom = orbitPolynomial τ r z x ∧
      (orbitPolynomial τ r z x).eval z = x := by
  classical
  let nodes (i : Fin r) := (τ : E → E)^[i.val] z
  let values (i : Fin r) := (τ : E → E)^[i.val] x
  let U : Finset (Fin r) := univ
  let P := Lagrange.interpolate U nodes values
  have distinct : Set.InjOn nodes U := inj.injOn _
  have evals (n : ℕ) : P.eval ((τ : E → E)^[n] z) = (τ : E → E)^[n] x := by
    let i : Fin r := ⟨n%r, Nat.mod_lt _ hr⟩
    rw [←hz.iterate_mod_apply n, ←hx.iterate_mod_apply n]
    exact Lagrange.eval_interpolate_at_node values distinct (mem_univ i)
  refine ⟨?_, evals 0⟩
  change P.map τ.toRingHom = P
  have deg : P.degree < U.card := Lagrange.degree_interpolate_lt values distinct
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq U distinct
    ((degree_map_le τ.toRingHom P).trans_lt deg) deg
  intro i _
  have next (n : ℕ) :
      (P.map τ.toRingHom).eval ((τ : E → E)^[n+1] z) = (τ : E → E)^[n+1] x := by
    rw [iterate_succ_apply', iterate_succ_apply', eval_map]
    exact (eval₂_at_apply τ.toRingHom _).trans (congrArg τ (evals n))
  change (P.map τ.toRingHom).eval ((τ : E → E)^[i.val] z) = P.eval ((τ : E → E)^[i.val] z)
  rw [evals]
  cases e : i.val with
  | succ n => exact next n
  | zero =>
    change (P.map τ.toRingHom).eval z = x
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    exact (congrArg (fun y => (P.map τ.toRingHom).eval y) hz.eq).symm.trans ((next n).trans hx.eq)

/-- Interpolation uses only differences of constants as denominators,
so integral orbit values give integral invariant coefficients. -/
theorem orbitPolynomial_coeff_mem (τ : E ≃+* E) (r : ℕ) (z x : E) (K : Subfield E)
    (A : Subring E) (hK : K.toSubring ≤ A)
    (nodes : ∀ i : Fin r, (τ : E → E)^[i.val] z ∈ K)
    (values : ∀ i : Fin r, (τ : E → E)^[i.val] x ∈ A) (n : ℕ) :
    (orbitPolynomial τ r z x).coeff n ∈ A := by
  classical
  let v (i : Fin r) : A := ⟨(τ : E → E)^[i.val] z, hK (nodes i)⟩
  let w (i : Fin r) : A := ⟨(τ : E → E)^[i.val] x, values i⟩
  let den (i j : Fin r) : A := ⟨((τ : E → E)^[i.val] z - (τ : E → E)^[j.val] z)⁻¹,
    hK (K.inv_mem (K.sub_mem (nodes i) (nodes j)))⟩
  let Q : A[X] := ∑ i : Fin r, C (w i) * ∏ j ∈ univ.erase i, C (den i j) * (X - C (v j))
  have he : Q.map A.subtype = orbitPolynomial τ r z x := by
    simp only [Q, orbitPolynomial, Lagrange.interpolate_apply, Lagrange.basis,
      Lagrange.basisDivisor, Polynomial.map_sum, Polynomial.map_prod, Polynomial.map_mul,
      Polynomial.map_sub, map_C, map_X]
    rfl
  rw [←he, coeff_map]
  exact (Q.coeff n).property

theorem periodic_mem_of_marker (τ : E ≃+* E) {r : ℕ} (hr : 0 < r) {z x : E}
    (hz : IsPeriodicPt τ r z) (hx : IsPeriodicPt τ r x)
    (inj : Injective (fun i : Fin r => (τ : E → E)^[i.val] z))
    (L : Subfield E) (contains : fixedField τ ≤ L) (marker : z ∈ L) : x ∈ L := by
  classical
  let P := orbitPolynomial τ r z x
  obtain ⟨hP,heval⟩ := orbitPolynomial_fixed_eval τ hr hz hx inj
  change P.map τ.toRingHom = P at hP
  change P.eval z = x at heval
  have coeff (n : ℕ) : P.coeff n ∈ fixedField τ := by
    exact (coeff_map τ.toRingHom n).symm.trans (congrArg (fun Q : E[X] => Q.coeff n) hP)
  rw [←heval, Polynomial.eval, eval₂_eq_sum, sum_def]
  exact L.sum_mem fun n _ => L.mul_mem (contains (coeff n)) (L.pow_mem marker n)

end
end BlockingCurves.CuspidalDescent
