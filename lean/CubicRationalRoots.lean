import Mathlib.FieldTheory.Finite.Basic

/-! For any finite field, q-power-fixed geometric roots are exactly rational roots.
The extension may be an algebraic closure; no finiteness assumption on it is used. -/
namespace BlockingCurves.CubicRationalRoots

open Polynomial
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]

theorem pow_card_fixed_iff (z : K) :
    z ^ Fintype.card F = z ↔ ∃ x : F, algebraMap F K x = z := by
  classical
  constructor
  · intro hz
    let P : F[X] := X ^ Fintype.card F - X
    have hroots : P.roots = Finset.univ.val := FiniteField.roots_X_pow_card_sub_X F
    have hd : Multiset.card P.roots = P.natDegree := by
      rw [hroots, show P.natDegree = Fintype.card F from
        FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
      rfl
    have hm := roots_map_of_injective_of_card_eq_natDegree (algebraMap F K).injective hd
    have hmem : z ∈ (P.map (algebraMap F K)).roots := by
      rw [show P.map (algebraMap F K) = X ^ Fintype.card F - X by simp [P]]
      rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card)]
      simpa [IsRoot.def] using sub_eq_zero.mpr hz
    rw [← hm, Multiset.mem_map] at hmem
    obtain ⟨x,_,hx⟩ := hmem
    exact ⟨x,hx⟩
  · rintro ⟨x,rfl⟩
    rw [← map_pow, FiniteField.pow_card]

/-- The embedding of roots gives an equivalence with the Frobenius fixed locus. -/
noncomputable def rationalRootEquiv (f : F[X]) :
    {x : F // f.eval x = 0} ≃
    {z : K // (f.map (algebraMap F K)).eval z = 0 ∧ z ^ Fintype.card F = z} := by
  let lift (x : {x : F // f.eval x = 0}) :
      {z : K // (f.map (algebraMap F K)).eval z = 0 ∧ z ^ Fintype.card F = z} :=
    ⟨algebraMap F K x.1, by rw [eval_map, eval₂_at_apply, x.2, map_zero],
      (pow_card_fixed_iff _).2 ⟨x.1,rfl⟩⟩
  apply Equiv.ofBijective lift
  constructor
  · intro x y h
    exact Subtype.ext ((algebraMap F K).injective (congrArg Subtype.val h))
  · rintro ⟨z,hz,hfixed⟩
    obtain ⟨x,rfl⟩ := (pow_card_fixed_iff z).1 hfixed
    rw [eval_map, eval₂_at_apply, ← map_zero (algebraMap F K)] at hz
    exact ⟨⟨x,(algebraMap F K).injective hz⟩,rfl⟩

/-- Counting distinct roots also works when the polynomial has repeated roots. -/
theorem fixed_root_count [DecidableEq F] [DecidableEq K] (f : F[X]) :
    ((f.map (algebraMap F K)).roots.toFinset.filter (fun z => z ^ Fintype.card F = z)).card =
      f.roots.toFinset.card := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  have hfm := (Polynomial.map_ne_zero_iff (algebraMap F K).injective).2 hf
  have hset : (f.map (algebraMap F K)).roots.toFinset.filter (fun z => z ^ Fintype.card F = z) =
      f.roots.toFinset.image (algebraMap F K) := by
    ext z
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hf, mem_roots hfm,
      IsRoot.def, Finset.mem_image, pow_card_fixed_iff]
    constructor
    · rintro ⟨hz,x,rfl⟩
      rw [eval_map, eval₂_at_apply, ← map_zero (algebraMap F K)] at hz
      exact ⟨x,(algebraMap F K).injective hz,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨by rw [eval_map, eval₂_at_apply, hx, map_zero], x, rfl⟩
  rw [hset, Finset.card_image_of_injective _ (algebraMap F K).injective]

/-- In the depressed cubic used in both trace counts, the count on the right is
the literal finite-field equation checked by the blocking predicate. -/
theorem cubic_fixed_count [DecidableEq F] [DecidableEq K] (m t : F) :
    (((X^3-C m*X-C t : F[X]).map (algebraMap F K)).roots.toFinset.filter
      (fun z => z ^ Fintype.card F = z)).card =
      (Finset.univ.filter (fun x : F => x^3-m*x=t)).card := by
  rw [fixed_root_count]
  congr 1
  have hP : (X^3-C m*X-C t : F[X]) ≠ 0 := by
    intro he
    have hc := congrArg (fun g : F[X] => g.coeff 3) he
    simp [coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at hc
  ext x
  simp [mem_roots hP, IsRoot.def, sub_eq_zero]

end BlockingCurves.CubicRationalRoots
