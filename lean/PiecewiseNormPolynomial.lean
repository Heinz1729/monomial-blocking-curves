import PiecewiseNormSlice

namespace BlockingCurves.PiecewiseNormSlice

open Polynomial Finset NormPencil

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

private noncomputable def conjugateFactor (σ : E ≃ₐ[F] E) (x y : E) (j : ℕ) : E[X] :=
  C ((σ^j) x) + C ((σ^j) y) * X

private theorem frob_factor (σ : E ≃ₐ[F] E) (x y : E) (j : ℕ) :
    (conjugateFactor σ x y j).map σ.toRingEquiv.toRingHom = conjugateFactor σ x y (j+1) := by
  simp [conjugateFactor, pow_succ', AlgEquiv.mul_apply]

/-- On a ground-field line the norm of an affine function is a genuine
ground-field polynomial. Its displayed factorization retains all conjugate roots. -/
theorem norm_polynomial (σ : E ≃ₐ[F] E) (frob : ∀ x : E, σ x=x^Fintype.card F)
    {n : ℕ} (period : σ^n=1) (x y : E) (hy : y≠0) :
    ∃ P : F[X], P.map (algebraMap F E) =
      ∏ j : Fin n, (C ((σ^j.val) x) + C ((σ^j.val) y)*X) ∧
      P.natDegree = n ∧ ∀ t : F, algebraMap F E (P.eval t) =
        (x+algebraMap F E t*y)^normExponent (Fintype.card F) n := by
  classical
  let f := conjugateFactor σ x y
  let Q := ∏ j ∈ range n, f j
  have fixed : Q.map σ.toRingEquiv.toRingHom = Q := by
    change (∏ j ∈ range n, f j).map _ = _
    rw [Polynomial.map_prod]
    calc
      _ = ∏ j ∈ range n, f (j+1) :=
        prod_congr rfl (fun j _ => frob_factor σ x y j)
      _ = Q := by
        have nz : f 0 ≠ 0 := by
          intro h
          have eq := congrArg (fun p : E[X] => p.coeff 1) h
          simp [f,conjugateFactor,hy] at eq
        apply mul_right_cancel₀ nz
        rw [← prod_range_succ',show Q*(f 0)=(∏ j ∈ range n, f j)*f n by simp [Q,f,conjugateFactor,period]]
        exact prod_range_succ f n
  have descend : Q ∈ (mapRingHom (algebraMap F E)).range := by
    apply (mem_map_range _).2
    intro k
    apply (pow_card_eq_iff_scalar F E _).1
    have h := congrArg (fun p : E[X] => p.coeff k) fixed
    simpa [coeff_map,← frob] using h
  obtain ⟨P,he⟩ := descend
  change P.map (algebraMap F E) = Q at he
  refine ⟨P,he.trans ?_,?_,?_⟩
  · exact (Fin.prod_univ_eq_prod_range f n).symm
  · have deg (j : ℕ) : (f j).natDegree = 1 := by
      rw [show f j = C ((σ^j) y)*X + C ((σ^j) x) by simp [f,conjugateFactor,add_comm]]
      exact natDegree_linear (by simpa using hy)
    rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap F E).injective,he]
    dsimp only [Q]
    rw [Polynomial.natDegree_prod _ _ fun j _ h => by simpa [h] using deg j]
    simp [deg]
  · intro t
    rw [← Polynomial.eval₂_hom (algebraMap F E), Polynomial.eval₂_eq_eval_map,he]
    change (∏ j ∈ range n, f j).eval _ = _
    rw [Polynomial.eval_prod]
    have val (j : ℕ) : (f j).eval (algebraMap F E t) = (x+algebraMap F E t*y)^(Fintype.card F^j) := by
      have iterate (v : E) : (σ^j) v = v^(Fintype.card F^j) := by
        induction j with
        | zero => simp
        | succ j ih => rw [pow_succ' σ,AlgEquiv.mul_apply,frob,ih,← pow_mul,pow_succ]
      rw [← iterate]
      simp only [f,conjugateFactor,eval_add,eval_C,eval_mul,eval_X,map_add,map_mul,
        AlgEquiv.commutes]
      rw [mul_comm]
    simp_rw [val]
    rw [Finset.prod_pow_eq_pow_sum]
    have sum : ∀ k, ∑ j ∈ range k, Fintype.card F^j=normExponent (Fintype.card F) k := by
      intro k
      induction k with
      | zero => simp [normExponent]
      | succ k ih => rw [sum_range_succ,ih,normExponent]
    rw [sum]

end BlockingCurves.PiecewiseNormSlice
