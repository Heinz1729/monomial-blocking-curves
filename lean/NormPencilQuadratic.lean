import NormPencilTrace
import NormCubicTrace

/-! For a quadratic extension the polar form of the norm absorbs every linear
functional. The kernel of a scalar projection therefore attains the horizontal
lower bound for the norm pencil in every characteristic. -/

namespace BlockingCurves.NormPencil

open FiniteDimensional
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  [FiniteDimensional F E]
attribute [local instance] Classical.propDecidable

private theorem quadratic_power (hn : finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.norm F x) = x * x ^ Fintype.card F := by
  rw [norm_eq_power, hn]
  simp [normExponent, pow_add]

private theorem quadratic_trace (hn : finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + x ^ Fintype.card F := by
  rw [trace_eq_frobenius_sum, hn, Fin.sum_univ_two]
  simp

/-- Completing the quadratic norm by translation works in characteristic two as well. -/
theorem quadratic_complete {σ : E ≃ₐ[F] E} (hσ : ∀ x : E, σ x = x ^ Fintype.card F)
    (hn : finrank F E = 2) (x c : E) :
    Algebra.norm F (x - σ c) = Algebra.norm F x - Algebra.trace F E (c*x) + Algebra.norm F c := by
  have hcc : σ (σ c) = c := by
    rw [hσ, hσ, ← pow_mul, ← pow_two, ← hn, ← card_eq_pow_finrank (K := F) (V := E)]
    exact FiniteField.pow_card c
  apply (algebraMap F E).injective
  rw [map_add (algebraMap F E), map_sub (algebraMap F E), quadratic_trace hn, quadratic_power hn, quadratic_power hn, quadratic_power hn]
  simp only [← hσ, map_sub, map_mul, hcc]
  ring

theorem quadratic_projection_blocks (hn : finrank F E = 2) (π : E →ₗ[F] F)
    (split : ∀ c : F, π (algebraMap F E c) = c) :
    GraphHits (fun x : E => x ^ (Fintype.card F + 1)) (lift π {0} : Set E) := by
  intro a b
  obtain ⟨c,hc⟩ := trace_representative (π.comp (LinearMap.mulLeft F a))
  change ∀ x : E, Algebra.trace F E (c*x) = π (a*x) at hc
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  obtain ⟨y,hy⟩ := norm_power_surjective (show 0 < finrank F E from finrank_pos)
    (card_eq_pow_finrank (K := F) (V := E)) (π b + Algebra.norm F c)
  have hN : Algebra.norm F y = π b + Algebra.norm F c := by
    apply (algebraMap F E).injective
    rw [norm_eq_power, hy]
  let x := y + σ c
  have he := quadratic_complete hσ hn x c
  have hxy : x - σ c = y := add_sub_cancel_right _ _
  rw [hxy, hN, hc] at he
  refine ⟨x, (mem_lift π).2 ?_⟩
  change π (x ^ (Fintype.card F + 1) - a*x - b) ∈ ({0} : Finset F)
  rw [Finset.mem_singleton, map_sub, map_sub, show x ^ (Fintype.card F + 1) =
    algebraMap F E (Algebra.norm F x) by rw [quadratic_power hn, pow_succ, mul_comm], split]
  linear_combination -he

/-- The exact, nontrivial norm pencil in every quadratic extension, including odd order. -/
theorem quadratic_norm_minimum (hn : finrank F E = 2) :
    AsgarliGhiocaYip.isPencilMinimum E (Fintype.card F + 1) (Fintype.card F) := by
  have hs : 1 < Fintype.card F := Fintype.one_lt_card
  have hd : 2 ≤ Fintype.card F + 1 := by omega
  have size : Fintype.card E = Fintype.card F ^ 2 := by rw [← hn, card_eq_pow_finrank (K := F)]
  obtain ⟨π,split⟩ := exists_projection F E
  apply (AGY_minimum_iff hd _).2
  constructor
  · refine ⟨lift π {0}, ?_, (projectiveBlocks_iff_graphHits hd _).2
      (quadratic_projection_blocks hn π split)⟩
    rw [card_lift π split, cap_count π (by decide : 0 < 2) split size]
    simp
  · rintro _ ⟨S,rfl,hS⟩
    have h := (projectiveBlocks_iff_graphHits hd _).1 hS
    have hD : normExponent (Fintype.card F) 2 = Fintype.card F + 1 := by
      simp [normExponent, Nat.add_comm]
    have hh : ∀ b : E, ∃ x, x ^ (1 * normExponent (Fintype.card F) 2) - b ∈ S := by
      intro b
      simpa only [hD, one_mul, zero_mul, sub_zero] using h 0 b
    simpa [coverNumber_one] using norm_horizontal_lower (by decide : 0 < 2) size S hh

/-- Realization of prescribed trace and norm. A separable split quadratic has two
distinct roots; every other monic quadratic is either irreducible or a square. -/
theorem quadratic_trace_norm_of_unique (hn : finrank F E = 2) (t u : F)
    (uniq : ∀ x y : F, x^2-t*x+u=0 → y^2-t*y+u=0 → x=y) :
    ∃ z : E, Algebra.trace F E z = t ∧ Algebra.norm F z = u := by
  classical
  by_cases h : ∃ x : F, x^2-t*x+u=0
  · obtain ⟨x,hx⟩ := h
    have hxx := uniq x (t-x) hx (by linear_combination hx)
    refine ⟨algebraMap F E x, ?_, ?_⟩
    · rw [Algebra.trace_algebraMap, hn, two_nsmul]
      linear_combination hxx
    · rw [Algebra.norm_algebraMap, hn]
      linear_combination x*hxx - hx
  · let P : Polynomial F := Polynomial.X^2 + (Polynomial.C (-t)*Polynomial.X+Polynomial.C u)
    have hd : P.natDegree = 2 := by dsimp [P]; compute_degree <;> norm_num
    have hm : P.Monic := by
      apply Polynomial.monic_X_pow_add
      compute_degree
      norm_num
    have hi : Irreducible P := by
      apply (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (p := P) (by omega) (by omega)).2
      apply Multiset.eq_zero_iff_forall_not_mem.2
      intro x hx
      apply h
      refine ⟨x, ?_⟩
      have he := (Polynomial.mem_roots (p := P) (fun hz => by simp [hz] at hd)).1 hx
      change P.eval x = 0 at he
      simpa [P,sub_eq_add_neg,add_assoc] using he
    obtain ⟨z,hzT,hzN⟩ := realize_monic F E P hi hm (hd.trans hn.symm)
    refine ⟨z, ?_, ?_⟩
    · rw [hzT, Polynomial.nextCoeff_of_natDegree_pos (by omega), hd]
      simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    · rw [hzN, hn]
      norm_num [P, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X]

end BlockingCurves.NormPencil
