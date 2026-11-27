import PhaseCharacterBudget
import PhaseEigenFibres
import Mathlib.FieldTheory.Separable
import Mathlib.Data.ZMod.Basic

/-! Kummer independence on split geometric fibres. The polynomials may be
over an algebraic closure; multiplicities are ordinary polynomial root
multiplicities, including at intersections of different branch loci. -/
namespace BlockingCurves.PhaseCharacter

open Polynomial Finset
open scoped BigOperators

variable {E J : Type*} [Field E] [Fintype J]

private theorem multiplicity_power (x : E) (f : E[X]) (e : ℕ) :
    rootMultiplicity x (f^e) = e * rootMultiplicity x f := by
  classical
  simp only [← Polynomial.count_roots, Polynomial.roots_pow, Multiset.count_nsmul]

private theorem multiplicity_product (x : E) (p : J → E[X]) (hp : ∀ j, p j ≠ 0)
    (e : J → ℕ) (S : Finset J) :
    rootMultiplicity x (∏ j ∈ S, (p j)^(e j)) =
      ∑ j ∈ S, e j * rootMultiplicity x (p j) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty,Finset.sum_empty,← Polynomial.count_roots,Polynomial.roots_one]; rfl
  | @insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Polynomial.rootMultiplicity_mul,
      multiplicity_power, ih]
    exact mul_ne_zero (pow_ne_zero _ (hp _))
      (Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hp k)))

/-- A power identity forces a genuine root-multiplicity congruence at every point. -/
theorem power_multiplicities_vanish {m : ℕ} (p : J → E[X]) (hp : ∀ j, p j ≠ 0)
    (e : J → ℕ) (g : E[X]) (power : ∏ j, (p j)^(e j) = g^m) (x : E) :
    ∑ j, (e j : ZMod m) * (rootMultiplicity x (p j) : ZMod m) = 0 := by
  have h := (multiplicity_product x p hp e Finset.univ).symm
  rw [power, multiplicity_power] at h
  have hz := congrArg (fun a : ℕ => (a : ZMod m)) h
  simpa only [Nat.cast_sum,Nat.cast_mul,ZMod.natCast_self,zero_mul] using hz

/-- Distinct labelled candidate polynomials give their coordinate residues.
For each shift a product of eigencoordinates indexes points of its fibre.
A candidate vanishes exactly on its own shift and its one named coordinate.
All branches except the distinguished one have an unused coordinate value. -/
theorem not_power_of_coordinate_roots {A I K : Type*} [Fintype I] {m : ℕ}
    (p : J → E[X]) (sep : ∀ j, (p j).Separable)
    (shift : J → A) (branch : J → I) (label : J → K)
    (distinct : ∀ i j, shift i = shift j → branch i = branch j → label i = label j → i=j)
    (point : A → (I → K) → E)
    (roots : ∀ a v j, (p j).IsRoot (point a v) ↔
      shift j = a ∧ v (branch j) = label j)
    (full : A → I) (unused : ∀ a i, i ≠ full a → ∃ u, ∀ j,
      shift j = a → branch j = i → label j ≠ u)
    (e : J → ℕ) (small : ∀ j, e j < m) (active : ∃ j, e j ≠ 0) (g : E[X]) :
    ∏ j, (p j)^(e j) ≠ g^m := by
  classical
  intro hg
  obtain ⟨j₀,h₀⟩ := active
  let a := shift j₀
  let weight (i : I) (u : K) : ZMod m :=
    ∑ j, if shift j = a ∧ branch j = i ∧ label j = u then (e j : ZMod m) else 0
  have zeroSum (v : I → K) : ∑ i, weight i (v i) = 0 := by
    rw [show (∑ i, weight i (v i)) =
        ∑ j, (e j : ZMod m) * (rootMultiplicity (point a v) (p j) : ZMod m) by
      dsimp only [weight]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single (branch j)]
      · by_cases h : (p j).IsRoot (point a v)
        · obtain ⟨hs,hl⟩ := (roots a v j).mp h
          have hle := rootMultiplicity_le_one_of_separable (sep j) (point a v)
          have hpos := (Polynomial.rootMultiplicity_pos (sep j).ne_zero).mpr h
          have one : rootMultiplicity (point a v) (p j) = 1 := by omega
          simp [hs,hl,one]
        · have hm := Polynomial.rootMultiplicity_eq_zero h
          have hn : ¬(shift j = a ∧ label j = v (branch j)) := by
            rintro ⟨hs,he⟩
            exact h ((roots a v j).mpr ⟨hs,he.symm⟩)
          simp only [eq_self, true_and, if_neg hn, hm, Nat.cast_zero, mul_zero]
      · intro i _ hi
        simp [Ne.symm hi]
      · simp]
    exact power_multiplicities_vanish p (fun j => (sep j).ne_zero) e g hg _
  have holes (i : I) (hi : i ≠ full a) : ∃ t, weight i t = 0 := by
    obtain ⟨t,ht⟩ := unused a i hi
    refine ⟨t,Finset.sum_eq_zero fun j _ => if_neg ?_⟩
    rintro ⟨ha,hb,hl⟩
    exact ht j ha hb hl
  have hz := weights_vanish_with_one_full_branch weight (full a) holes zeroSum
    (branch j₀) (label j₀)
  have hw : weight (branch j₀) (label j₀) = (e j₀ : ZMod m) := by
    dsimp only [weight]
    rw [Finset.sum_eq_single j₀]
    · simp [a]
    · intro j _ hj
      exact if_neg fun ⟨hs,hb,hl⟩ => hj (distinct j j₀ hs hb hl)
    · simp
  rw [hw] at hz
  exact h₀ (Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hz) (small _))

end BlockingCurves.PhaseCharacter

namespace BlockingCurves.PhaseCommonVariable
open Polynomial Finset
open scoped BigOperators

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Ordinary univariate polynomial obtained by composing the normalized
Frobenius factors; the empty product acts as the identity polynomial. -/
noncomputable def linearizedFactors (s : ℕ) (a : E) : List F → E[X]
  | [] => X
  | z :: l => C (algebraMap F E z * a⁻¹) * linearizedFactors s a l ^ s -
      linearizedFactors s a l

private theorem eval_linearizedFactors [DecidableEq F] (σ : E ≃ₐ[F] E)
    (s : ℕ) (frob : ∀ x, σ x = x^s) (a x : E) (l : List F) (nodup : l.Nodup) :
    (linearizedFactors s a l).eval x = productEnd (normalized σ a) l.toFinset x := by
  induction l with
  | nil => simp [linearizedFactors,productEnd]
  | cons z l ih =>
    have hn := List.nodup_cons.mp nodup
    have hz : z ∉ l.toFinset := by simpa using hn.1
    rw [linearizedFactors, eval_sub, eval_mul, eval_C, eval_pow, ih hn.2, List.toFinset_cons]
    unfold productEnd
    rw [Finset.prod_insert hz,map_mul,LinearMap.mul_apply]
    let y := productEnd (normalized σ a) l.toFinset x
    change (algebraMap F E z * a⁻¹) * y^s - y =
      (aeval (normalized σ a) (C z*X-1)) y
    simp only [map_sub,map_mul,aeval_C,aeval_X,map_one,LinearMap.sub_apply,
      LinearMap.mul_apply,Module.algebraMap_end_apply,LinearMap.one_apply]
    simp only [normalized,LinearMap.smul_apply,LinearEquiv.coe_coe,AlgEquiv.toLinearEquiv_apply,
      Algebra.smul_def,Algebra.id.map_eq_self,frob,mul_assoc]

private theorem derivative_linearizedFactors (s : ℕ) (hs : (s:E) = 0) (a : E) (l : List F) :
    derivative (linearizedFactors s a l) = C ((-1:E)^l.length) := by
  induction l with
  | nil => simp [linearizedFactors]
  | cons z l ih =>
    simp [linearizedFactors,derivative_mul,derivative_pow,hs,ih,pow_succ]

/-- The candidate Q_z(X)+c of the common substitution, as a polynomial. -/
noncomputable def candidatePolynomial [Fintype F] [DecidableEq F]
    (a : E) (Z : Finset F) (z : F) (c : E) : E[X] :=
  linearizedFactors (Fintype.card F) a (Z.erase z).toList + C c

/-- Its derivative is a nonzero constant in every characteristic, even when
the omitted branch has a nontrivial rational kernel. -/
theorem candidatePolynomial_separable [Fintype F] [DecidableEq F]
    (a : E) (Z : Finset F) (z : F) (c : E) : (candidatePolynomial a Z z c).Separable := by
  have hs : (Fintype.card F : E) = 0 := by
    simpa only [map_natCast,map_zero] using congrArg (algebraMap F E) (FiniteField.cast_card_eq_zero F)
  let b : E := (-1)^((Z.erase z).toList.length)
  have hb : b ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  refine ⟨0, C b⁻¹, ?_⟩
  rw [candidatePolynomial,derivative_add,derivative_C,add_zero,zero_mul,zero_add,
    derivative_linearizedFactors _ hs]
  change C b⁻¹ * C b = 1
  rw [← C_mul,inv_mul_cancel hb,C_1]

theorem eval_candidatePolynomial [Fintype F] [DecidableEq F] (σ : E ≃ₐ[F] E)
    (frob : ∀ x : E, σ x = x ^ Fintype.card F) (a : E) (Z : Finset F) (z : F) (c x : E) :
    (candidatePolynomial a Z z c).eval x =
      productEnd (normalized σ a) (Z.erase z) x + c := by
  simp only [candidatePolynomial,eval_add,eval_C,
    eval_linearizedFactors σ _ frob a x _ (Finset.nodup_toList _),Finset.toList_toFinset]

/-- The root of the actual separable polynomial singles out the labelled
eigen-coordinate of the geometric fibre. -/
theorem candidatePolynomial_root_on_box [Fintype F] [DecidableEq F] (σ : E ≃ₐ[F] E)
    (frob : ∀ x : E, σ x = x ^ Fintype.card F) (a : E) (Z : Finset F) {z : F}
    (hz : z ∈ Z) (nonzero : ∀ u ∈ Z, u ≠ 0) (t c : E) (v : F → E)
    (hv : ∀ u ∈ Z, normalized σ a (v u) = u⁻¹ • v u) :
    (candidatePolynomial a Z z c).IsRoot (t + ∑ u ∈ Z, v u) ↔
      v z = (∏ u ∈ Z.erase z, (u*z⁻¹-1))⁻¹ • (-(productEnd (normalized σ a) (Z.erase z) t+c)) := by
  rw [Polynomial.IsRoot,eval_candidatePolynomial σ frob]
  exact (candidate_on_eigen_box (normalized σ a) Z hz nonzero t c v hv).2

end BlockingCurves.PhaseCommonVariable
