import PiecewiseFibres
import PiecewiseCandidates
import PhaseEigenFibres
import PhaseRootMultiplicity
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The actual common-variable candidate polynomials, including every point of
a possibly singular rational branch fibre. -/
namespace BlockingCurves.PiecewiseLargeEscape

open Polynomial Finset PiecewiseFibres PhaseCommonVariable
open scoped BigOperators

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Algebra F E]

/-- Compose the normalized operators c a⁻¹ X^s − X. -/
noncomputable def listPoly (a : E) : List F → E[X]
  | [] => X
  | c :: cs => C (algebraMap F E c * a⁻¹) * (listPoly a cs)^Fintype.card F - listPoly a cs

theorem listPoly_degree (a : E) (cs : List F) :
    (listPoly a cs).natDegree ≤ Fintype.card F ^ cs.length := by
  induction cs with
  | nil => simp [listPoly]
  | cons c cs ih =>
    let s := Fintype.card F
    have hs : 1 ≤ s := Fintype.card_pos
    have hpow : ((listPoly a cs)^s).natDegree ≤ (listPoly a cs).natDegree*s :=
      (Polynomial.natDegree_pow_le).trans (le_of_eq (mul_comm ..))
    have h := (Polynomial.natDegree_C_mul_le (algebraMap F E c*a⁻¹) _).trans hpow
    change (_ - listPoly a cs).natDegree ≤ s^(cs.length+1)
    refine (Polynomial.natDegree_sub_le ..).trans (max_le ?_ ?_)
    · exact h.trans ((Nat.mul_le_mul_right s ih).trans (le_of_eq (pow_succ _ _).symm))
    · exact ih.trans ((Nat.le_mul_of_pos_right _ (by omega : 0 < s)).trans (le_of_eq (pow_succ _ _).symm))

theorem listPoly_derivative (a : E) (cs : List F) :
    derivative (listPoly a cs) = C ((-1:E)^cs.length) := by
  have hs : ((Fintype.card F : ℕ) : E) = 0 := by
    simpa only [map_natCast,map_zero] using
      congrArg (algebraMap F E) (FiniteField.cast_card_eq_zero F)
  induction cs with
  | nil => simp [listPoly]
  | cons c cs ih =>
    simp [listPoly,derivative_pow,hs,ih,pow_succ]

/-- The relative Frobenius extends to the algebraic closure with its actual
s-power formula. Its surjectivity follows from existence of s-th roots. -/
theorem closed_frobenius (F H : Type*) [Field F] [Fintype F] [Field H] [Algebra F H]
    [IsAlgClosed H] : ∃ σ : H ≃ₐ[F] H, ∀ t, σ t = t ^ Fintype.card F := by
  obtain ⟨n,hp,hn⟩ := FiniteField.card F (ringChar F)
  letI : CharP H (ringChar F) := charP_of_injective_algebraMap' F H _
  letI : ExpChar H (ringChar F) := ExpChar.prime hp
  let f : H →ₐ[F] H :=
    { toRingHom := iterateFrobenius H (ringChar F) n
      commutes' := by
        intro c
        change (algebraMap F H c)^(ringChar F)^(n:ℕ) = algebraMap F H c
        rw [← hn, ← map_pow, FiniteField.pow_card] }
  have eq (x : H) : f x = x^Fintype.card F := by
    change x^(ringChar F)^(n:ℕ) = x^Fintype.card F
    rw [hn]
  have surj : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := IsAlgClosed.exists_pow_nat_eq y (Fintype.card_pos (α:=F))
    exact ⟨x,(eq x).trans hx⟩
  exact ⟨AlgEquiv.ofBijective f ⟨f.injective,surj⟩,eq⟩

variable [DecidableEq F]

/-- Evaluation commutes with extending the coefficient field and with composing
the normalized Frobenius operators, also on the algebraic closure. -/
theorem listPoly_eval₂ {H : Type*} [Field H] [Algebra F H] (ι : E →+* H)
    (compat : ∀ c : F, ι (algebraMap F E c) = algebraMap F H c)
    (σ : H ≃ₐ[F] H) (hσ : ∀ x : H, σ x = x^Fintype.card F)
    (a : E) (cs : List F) (hd : cs.Nodup) (t : H) :
    (listPoly a cs).eval₂ ι t = productEnd (normalized σ (ι a)) cs.toFinset t := by
  classical
  induction cs with
  | nil => simp [listPoly,productEnd]
  | cons c cs ih =>
    have hh := List.nodup_cons.mp hd
    have hn : c ∉ cs.toFinset := by simpa using hh.1
    have tail := ih hh.2
    rw [listPoly,Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,
      tail, List.toFinset_cons]
    simp only [productEnd,Finset.prod_insert hn,map_mul,map_sub,aeval_C,aeval_X,map_one,
      LinearMap.mul_apply,LinearMap.sub_apply,Module.algebraMap_end_apply,LinearMap.one_apply]
    simp [normalized,Algebra.smul_def,hσ,compat,mul_assoc]

variable [Fintype E]

noncomputable def candidatePolynomial (Cfs : Finset F) (a : E) (S : Finset E)
    (j : Candidate Cfs a S) : E[X] :=
  listPoly a (Cfs.erase j.2.1.val).toList + C j.2.2.val

theorem candidate_degree (Cfs : Finset F) (a : E) (S : Finset E) (j : Candidate Cfs a S) :
    (candidatePolynomial Cfs a S j).natDegree ≤ Fintype.card F^(Cfs.card-1) := by
  unfold candidatePolynomial
  refine (Polynomial.natDegree_add_le ..).trans (max_le ?_ ?_)
  · simpa only [Finset.length_toList,Finset.card_erase_of_mem j.2.1.property] using
      listPoly_degree a (Cfs.erase j.2.1.val).toList
  · simp

theorem candidate_separable (Cfs : Finset F) (a : E) (S : Finset E) (j : Candidate Cfs a S) :
    (candidatePolynomial Cfs a S j).Separable := by
  rw [Polynomial.separable_def',candidatePolynomial,derivative_add,derivative_C,add_zero,listPoly_derivative]
  let w := (-1:E) ^ (Cfs.erase j.2.1.val).toList.length
  have hw : w ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  refine ⟨0,C w⁻¹,?_⟩
  change 0*_ + Polynomial.C w⁻¹ * Polynomial.C w = 1
  rw [zero_mul,zero_add,← map_mul,inv_mul_cancel hw,map_one]

theorem candidate_evaluation (Cfs : Finset F) (a : E) (S : Finset E) (j : Candidate Cfs a S)
    (σ : E ≃ₐ[F] E) (hσ : ∀ x : E, σ x = x^Fintype.card F) (t : E) :
    (candidatePolynomial Cfs a S j).eval t =
      productEnd (normalized σ a) (Cfs.erase j.2.1.val) t + j.2.2.val := by
  let B := Cfs.erase j.2.1.val
  have h := listPoly_eval₂ (F:=F) (RingHom.id E) (fun _ => rfl) σ hσ a B.toList B.nodup_toList t
  simpa [candidatePolynomial,B,Polynomial.eval,Finset.toList_toFinset] using congrArg (·+j.2.2.val) h

end BlockingCurves.PiecewiseLargeEscape
