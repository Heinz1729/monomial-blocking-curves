import NormSmall
import NormPencilQuadratic

/-! Transfer of the small scalar certificates to the actual quadratic norm pencil. -/
namespace BlockingCurves.NormPencil
open FiniteDimensional

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  [FiniteDimensional F E]

/-- A scalar quadratic witness prescribes a norm and a trace simultaneously.
The value u^m is chosen only after projecting the actual line intercept. -/
theorem quadratic_minimum_of_scalar_targets {m : ℕ} (hm : 0 < m) (hn : finrank F E=2)
    (hscalar : ScalarWitness F m) :
    AsgarliGhiocaYip.isPencilMinimum E (m*normExponent (Fintype.card F) 2)
      (Fintype.card F*coverNumber F m) := by
  have size : Fintype.card E = Fintype.card F ^ 2 := by rw [← hn, card_eq_pow_finrank (K := F)]
  have hd := (normExponent_two_le (s := Fintype.card F) Fintype.one_lt_card
    (by decide : 2 ≤ 2)).trans (Nat.le_mul_of_pos_left _ hm)
  apply (AGY_minimum_iff hd _).2
  obtain ⟨π,split⟩ := exists_projection F E
  obtain ⟨A,hcard,hA⟩ := coverNumber_attained F m
  constructor
  · refine ⟨lift π A, ?_,(projectiveBlocks_iff_graphHits hd _).2 ?_⟩
    · rw [card_lift π split,cap_count π (by decide : 0 < 2) split size,hcard]
      simp
    intro a b
    obtain ⟨u,hu⟩ := hA (π b)
    obtain ⟨c,hc⟩ := trace_representative (π.comp (LinearMap.mulLeft F a))
    change ∀ x : E, Algebra.trace F E (c*x) = π (a*x) at hc
    have hr (x : E) : x^(m*normExponent (Fintype.card F) 2) =
        algebraMap F E ((Algebra.norm F x)^m) := by
      rw [map_pow,norm_eq_power,hn,Nat.mul_comm,pow_mul]
    by_cases hc0 : c=0
    · obtain ⟨x,hx⟩ := norm_power_surjective (by decide : 0<2) size u
      refine ⟨x,(mem_lift π).2 ?_⟩
      change π (x^(m*normExponent (Fintype.card F) 2)-a*x-b) ∈ A
      have hp : π (a*x)=0 := by rw [← hc,hc0,zero_mul,map_zero]
      rw [map_sub,map_sub,hp,sub_zero,Nat.mul_comm,pow_mul,hx,← map_pow,split]
      exact hu
    · have hnc : Algebra.norm F c ≠ 0 := (Algebra.norm_ne_zero_iff_of_basis
          (FiniteDimensional.finBasis F E)).2 hc0
      obtain ⟨v,hv⟩ := hscalar (u^m) (Algebra.norm F c) hnc
      obtain ⟨z,htr,hnz⟩ := quadratic_trace_norm_of_unique hn (v^m-u^m) (Algebra.norm F c*v) (fun x y hx hy =>
        hv x y (by linear_combination hx) (by linear_combination hy))
      let x := c⁻¹*z
      have hn' : Algebra.norm F x=v := by
        apply mul_left_cancel₀ hnc
        dsimp [x]; rw [← map_mul,← mul_assoc,mul_inv_cancel hc0,one_mul,hnz]
      have ht' : π (a*x)=v^m-u^m := by
        rw [← hc]; dsimp [x]; rw [← mul_assoc,mul_inv_cancel hc0,one_mul,htr]
      refine ⟨x,(mem_lift π).2 ?_⟩
      change π (x^(m*normExponent (Fintype.card F) 2)-a*x-b) ∈ A
      rw [map_sub,map_sub,hr,split,hn',ht',sub_sub_cancel]
      exact hu
  · rintro _ ⟨S,rfl,hS⟩
    have hh : ∀ b : E, ∃ x, x ^ (m*normExponent (Fintype.card F) 2) - b ∈ S := by
      intro b
      simpa using (projectiveBlocks_iff_graphHits hd _).1 hS 0 b
    simpa using norm_horizontal_lower (by decide : 0 < 2) size S hh

end BlockingCurves.NormPencil
