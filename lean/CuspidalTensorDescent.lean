import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-! Linear independence of invariant vectors after extending the constants.
The proof normalizes a shortest possible dependence and subtracts its
Frobenius transform, so it applies to infinite extensions as well. -/
namespace BlockingCurves.CuspidalDescent
open Finset Function
open scoped TensorProduct
noncomputable section
variable {R K E D : Type*} [Field R] [Field K] [Field E] [Field D]
  [Algebra R K] [Algebra R E]

private theorem independent_over_constants [Algebra K E] [IsScalarTower R K E]
    (κ : K ≃+* K) (τ : E ≃+* E) (cfix : ∀ x, κ x = x → ∃ c : R, algebraMap R K c = x)
    (extendsOn : ∀ x, τ (algebraMap K E x) = algebraMap K E (κ x))
    {ι : Type*} (v : ι → E) (fixed : ∀ i, τ (v i) = v i) (indep : LinearIndependent R v) :
    LinearIndependent K v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro f rel
    by_cases hz : f i = 0
    · rw [sum_insert hi, hz, zero_smul, zero_add] at rel
      intro j hj
      rcases mem_insert.mp hj with rfl | h
      · exact hz
      · exact ih f rel j h
    · let u (j : ι) := (f i)⁻¹ * f j
      have ui : u i = 1 := inv_mul_cancel hz
      have zero : ∑ j ∈ insert i s, u j • v j = 0 := by
        simp only [u, mul_smul, ← Finset.smul_sum, rel, smul_zero]
      have transformed : ∑ j ∈ insert i s, κ (u j) • v j = 0 := by
        have h := congrArg τ zero
        simp only [Algebra.smul_def, map_sum, map_mul, extendsOn, fixed, map_zero] at h ⊢
        exact h
      have small : ∑ j ∈ s, (κ (u j)-u j) • v j = 0 := by
        have h : ∑ j ∈ insert i s, (κ (u j)-u j) • v j = 0 := by
          simp only [sub_smul, sum_sub_distrib, transformed, zero, sub_zero]
        simpa only [sum_insert hi, ui, map_one, sub_self, zero_smul, zero_add] using h
      have lift (j : ι) (hj : j ∈ insert i s) : ∃ c : R, algebraMap R K c = u j := by
        apply cfix
        rcases mem_insert.mp hj with rfl | hj
        · simp [ui]
        · exact sub_eq_zero.mp (ih _ small j hj)
      let w (j : ι) : R := if h : j ∈ insert i s then (lift j h).choose else 0
      have hw (j : ι) (hj : j ∈ insert i s) : algebraMap R K (w j) = u j := by
        simpa only [w, dif_pos hj] using (lift j hj).choose_spec
      have rzero : ∑ j ∈ insert i s, w j • v j = 0 := by
        rw [←zero]
        apply sum_congr rfl
        intro j hj
        rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R K E, hw j hj]
      have hi' := hw i (mem_insert_self i s)
      rw [linearIndependent_iff'.mp indep _ w rzero i (mem_insert_self i s), map_zero, ui] at hi'
      exact (zero_ne_one hi').elim

/-- Multiplication is injective on the tensor product whenever the two
fields map into the ambient field as a coefficient field with fixed field R
and a field of fixed elements. -/
theorem productMap_injective_of_frobenius [Algebra R D]
    (κ : K ≃+* K) (τ : E ≃+* E) (C : K →ₐ[R] E) (U : D →ₐ[R] E)
    (cfix : ∀ x, κ x = x → ∃ c : R, algebraMap R K c = x)
    (extendsOn : ∀ x, τ (C x) = C (κ x)) (fixed : ∀ x, τ (U x) = U x) :
    Function.Injective (Algebra.TensorProduct.productMap C U) := by
  classical
  letI : Algebra K E := C.toRingHom.toAlgebra
  letI : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq fun c => (C.commutes c).symm
  let f := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K E) U
  let b := Basis.ofVectorSpace R D
  let t := Algebra.TensorProduct.basis K b
  have independent := independent_over_constants κ τ cfix extendsOn (fun i => U (b i))
    (fun i => fixed (b i)) (b.linearIndependent.map' U.toLinearMap (LinearMap.ker_eq_bot_of_injective U.injective))
  have maps (i) : f (t i) = U (b i) := by
    rw [show t i = 1 ⊗ₜ[R] b i from Algebra.TensorProduct.basis_apply b i]
    change C 1 * U (b i) = _
    rw [map_one, one_mul]
  have inj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).2
    intro x hx
    let c := t.repr x
    have rep : ∑ i ∈ c.support, c i • t i = x := t.total_repr x
    have h := congrArg f rep
    simp only [map_sum, map_smul, maps, hx] at h
    have zero : ∀ i ∈ c.support, c i = 0 := linearIndependent_iff'.mp independent _ c h
    rw [←rep]
    exact sum_eq_zero fun i hi => by rw [zero i hi, zero_smul]
  exact inj

end
end BlockingCurves.CuspidalDescent
