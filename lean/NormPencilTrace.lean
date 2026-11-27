import NormPencilField
import Mathlib.RingTheory.Norm
import Mathlib.RingTheory.Trace

/-! Relative trace and norm of finite fields in the actual power coordinates. -/
namespace BlockingCurves.NormPencil

open scoped BigOperators
open FiniteDimensional

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  [FiniteDimensional F E]

theorem finite_galois (F E : Type*) [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] [FiniteDimensional F E] : IsGalois F E := by
  apply IsGalois.of_fixedField_eq_bot
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  have hf : σ x = x := hx ⟨σ, Subgroup.mem_top _⟩
  exact (pow_card_eq_iff_scalar F E x).1 ((hσ x).symm.trans hf)

private theorem frob_index (σ : E ≃ₐ[F] E) (hσ : ∀ x : E, σ x = x ^ Fintype.card F) :
    Function.Bijective (fun i : Fin (finrank F E) => σ ^ i.val) := by
  letI := finite_galois F E
  have ho := relative_order σ hσ
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j he
    exact Fin.ext (pow_injOn_Iio_orderOf (ho.symm ▸ i.isLt) (ho.symm ▸ j.isLt) he)
  · rw [Fintype.card_fin, IsGalois.card_aut_eq_finrank]

theorem norm_eq_power (x : E) :
    algebraMap F E (Algebra.norm F x) = x ^ normExponent (Fintype.card F) (finrank F E) := by
  classical
  letI := finite_galois F E
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let e := Equiv.ofBijective _ (frob_index σ hσ)
  have sum_exp (n : ℕ) : ∑ i ∈ Finset.range n, Fintype.card F ^ i = normExponent (Fintype.card F) n := by
    induction n with
    | zero => simp [normExponent]
    | succ n ih => simp only [Finset.sum_range_succ, ih, normExponent]
  rw [Algebra.norm_eq_prod_automorphisms]
  calc
    _ = ∏ i : Fin (finrank F E), x ^ Fintype.card F ^ (i:ℕ) :=
      (Fintype.prod_equiv e _ _ (fun i => (power_apply_formula σ hσ i x).symm)).symm
    _ = x ^ normExponent (Fintype.card F) (finrank F E) := by
      rw [Fin.prod_univ_eq_prod_range (fun i => x ^ Fintype.card F ^ i),
        Finset.prod_pow_eq_pow_sum, sum_exp]

theorem trace_eq_frobenius_sum (x : E) :
    algebraMap F E (Algebra.trace F E x) =
      ∑ i : Fin (finrank F E), x ^ Fintype.card F ^ (i:ℕ) := by
  classical
  letI := finite_galois F E
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let e := Equiv.ofBijective _ (frob_index σ hσ)
  rw [trace_eq_sum_automorphisms]
  exact (Fintype.sum_equiv e _ _ (fun i => (power_apply_formula σ hσ i x).symm)).symm

theorem trace_representative (L : E →ₗ[F] F) :
    ∃ c : E, ∀ x : E, Algebra.trace F E (c*x) = L x := by
  letI := finite_galois F E
  let B := Algebra.traceForm F E
  let e := B.toDual (traceForm_nondegenerate F E)
  exact ⟨e.symm L, fun x => LinearMap.congr_fun (e.apply_symm_apply L) x⟩

/-- Zero-trace norm surjectivity implies the kernel condition for *any* scalar projection. -/
theorem kernel_of_trace_zero_norm {m : ℕ}
    (ht : ∀ t : F, ∃ z : E, Algebra.trace F E z = 0 ∧ Algebra.norm F z = t)
    (π : E →ₗ[F] F) (a : E) (u : F) :
    ∃ x : E, π (a*x) = 0 ∧
      x ^ (m * normExponent (Fintype.card F) (finrank F E)) = algebraMap F E (u ^ m) := by
  obtain ⟨c,hc⟩ := trace_representative (π.comp (LinearMap.mulLeft F a))
  change ∀ x : E, Algebra.trace F E (c*x) = π (a*x) at hc
  by_cases hz : c = 0
  · obtain ⟨x,hx⟩ := norm_power_surjective finrank_pos (card_eq_pow_finrank (K := F) (V := E)) u
    exact ⟨x, by simpa [hz] using (hc x).symm, by rw [Nat.mul_comm, pow_mul, hx, map_pow]⟩
  obtain ⟨z,hz0,hzN⟩ := ht (Algebra.norm F c * u)
  have hn : Algebra.norm F c ≠ 0 := (Algebra.norm_ne_zero_iff_of_basis
    (FiniteDimensional.finBasis F E)).2 hz
  refine ⟨c⁻¹*z, ?_, ?_⟩
  · rw [← hc, ← mul_assoc, mul_inv_cancel hz, one_mul, hz0]
  · have hxN : Algebra.norm F (c⁻¹*z) = u := by
      apply mul_left_cancel₀ hn
      rw [← map_mul, ← mul_assoc, mul_inv_cancel hz, one_mul, hzN]
    rw [Nat.mul_comm, pow_mul, ← norm_eq_power (F := F), hxN, map_pow]

theorem minimum_of_trace_zero_norm {m : ℕ} (hn : 2 ≤ finrank F E) (hm : 0 < m)
    (ht : ∀ t : F, ∃ z : E, Algebra.trace F E z = 0 ∧ Algebra.norm F z = t) :
    AsgarliGhiocaYip.isPencilMinimum E (m * normExponent (Fintype.card F) (finrank F E))
      (Fintype.card F ^ (finrank F E - 1) * coverNumber F m) :=
  minimum_of_kernel hn hm card_eq_pow_finrank (kernel_of_trace_zero_norm ht)

end BlockingCurves.NormPencil
