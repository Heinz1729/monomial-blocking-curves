import PhaseCharacterOrthogonality
import PhaseRootMultiplicity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Complex.ExponentialBounds

/-! Uniform character prescriptions for a finite family of actual univariate
polynomials. Multiplicities in a Fourier exponent do not increase the number
of distinct geometric roots charged in the Weil bound. -/
namespace BlockingCurves.PiecewiseWeil

open Finset Polynomial
open scoped BigOperators

variable {E J : Type*} [Field E] [Fintype J]

noncomputable def rootCount (g : E[X]) : ℕ :=
  open Classical in ((g.map (algebraMap E (AlgebraicClosure E))).roots.toFinset).card

/-- A standard weakening of the multiplicative, one-variable Weil estimate:
the number of distinct geometric roots times the square root of the field size.
The nonpower condition is geometric and therefore excludes constant multiples
of powers as well. -/
def PolynomialWeilBound [Fintype E] (m : ℕ) (χ : MulChar E ℂ) : Prop :=
  ∀ g : E[X], (∀ h : (AlgebraicClosure E)[X],
    g.map (algebraMap E (AlgebraicClosure E)) ≠ h^m) →
      ‖∑ x : E, χ (g.eval x)‖ ≤ rootCount g * Real.sqrt (Fintype.card E)

private theorem union_root_count (P : J → E[X]) {D : ℕ}
    (degree : ∀ j, (P j).natDegree ≤ D) :
    open Classical in (univ.biUnion (fun j => (P j).roots.toFinset)).card ≤ Fintype.card J*D := by
  classical
  refine Finset.card_biUnion_le.trans ?_
  simpa only [Finset.sum_const,card_univ,smul_eq_mul] using
    (Finset.sum_le_sum (s := univ) (g := fun _ => D) fun j _ =>
      ((P j).roots.toFinset_card_le.trans (Polynomial.card_roots' _)).trans (degree j))

/-- Root support of a Fourier product is bounded by the sum of the original
degrees, without an exponent factor or any coprimality assumption on factors. -/
theorem geometric_roots_le (P : J → E[X]) (hnz : ∀ j, P j ≠ 0) {D : ℕ}
    (degree : ∀ j, (P j).natDegree ≤ D) (e : J → ℕ) :
    rootCount (∏ j, (P j)^(e j)) ≤ Fintype.card J * D := by
  classical
  let Q (j : J) := (P j).map (algebraMap E (AlgebraicClosure E))
  have nz (j : J) : Q j ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap E _).injective).2 (hnz j)
  simp only [rootCount,Polynomial.map_prod,Polynomial.map_pow]
  refine (Finset.card_le_card (t := univ.biUnion (fun j => (Q j).roots.toFinset)) ?_).trans
    (union_root_count Q (fun j => by simpa [Q] using degree j))
  intro x hx
  have hz := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
  change (∏ j, (Q j)^(e j)).eval x = 0 at hz
  simp only [Polynomial.eval_prod,Polynomial.eval_pow] at hz
  obtain ⟨j,hj,h⟩ := Finset.prod_eq_zero_iff.mp hz
  have hzero : (Q j).eval x = 0 := by
    by_contra hne
    exact pow_ne_zero _ hne h
  exact Finset.mem_biUnion.mpr ⟨j,hj,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (nz j)).2 hzero)⟩

theorem extension_degree_scale {s n k : ℕ} (hs : 0 < s) (hk : 4*k ≤ n) :
    ((s^k : ℕ) : ℝ) ≤ Real.exp (Real.log ((s^n : ℕ) : ℝ)/4) := by
  have hp : (0:ℝ) < s := by exact_mod_cast hs
  have hl : 0 ≤ Real.log (s:ℝ) := Real.log_nonneg (by exact_mod_cast hs)
  push_cast
  rw [Real.log_pow, ← Real.exp_log hp, ← Real.exp_nat_mul, Real.log_exp, Real.exp_le_exp]
  have hk' : 4*(k:ℝ) ≤ n := by exact_mod_cast hk
  nlinarith only [mul_le_mul_of_nonneg_right hk' hl]

/-- The slice degrees are at most n ≤ 4m; the same fourth-root bound used
for the large-extension Fourier estimate follows from the stated threshold. -/
theorem bounded_degree_scale {D m : ℕ} {X L : ℝ} (hm : 2 ≤ m)
    (cap : D ≤ 4*m) (fieldSize : 16384*(m:ℝ)^5 ≤ L) (scale : L ≤ 4*m*X) :
    (D:ℝ) ≤ Real.exp (X/4) := by
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have threshold := (PhaseCharacter.explicit_field_threshold hm' fieldSize scale).1
  have cap' : (D:ℝ) ≤ 4*m := by exact_mod_cast cap
  have h : (D:ℝ) ≤ X/4+1 := by
    nlinarith only [threshold,cap',hm',sq_nonneg ((m:ℝ)-1)]
  exact h.trans (Real.add_one_le_exp _)

/-- A simultaneous splitting with pairwise distinct roots, including across
different coordinates, forces every nonzero Fourier product to be a nonpower.
The auxiliary splitting field can already be the algebraic closure. -/
theorem nonpower_of_split_roots {H I : Type*} [Field H] [Fintype I] [Nonempty I]
    {m : ℕ} [NeZero m] (P : J → H[X]) (A : J → H) (r : J → I → H) (hA : ∀ j, A j ≠ 0)
    (split : ∀ j, P j = C (A j) * ∏ i, (X - C (r j i)))
    (distinct : Function.Injective (fun ji : J × I => r ji.1 ji.2))
    (e : J → Fin m) (active : e ≠ 0) (g : H[X]) :
    ∏ j, (P j)^(e j : ℕ) ≠ g^m := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, e j ≠ 0 := by
    by_contra! h
    apply active
    funext j
    exact h j
  let i : I := Classical.choice ‹Nonempty I›
  let x := r j i
  have unit (k : J) : P k ≠ 0 := by
    rw [split]
    exact mul_ne_zero (C_ne_zero.mpr (hA _)) (Finset.prod_ne_zero_iff.mpr
      (fun t _ => X_sub_C_ne_zero _))
  have res (k : J) : rootMultiplicity x (P k) = if k=j then 1 else 0 := by
    by_cases hk : k=j
    · subst k
      let T := C (A j) * ∏ t ∈ univ.erase i, (X-C (r j t))
      have val : T.eval x ≠ 0 := by
        rw [show T.eval x = A j * ∏ t ∈ univ.erase i, (x-r j t) by simp [T,Polynomial.eval_prod]]
        apply mul_ne_zero (hA j) (Finset.prod_ne_zero_iff.mpr ?_)
        intro t ht eq
        exact (Finset.mem_erase.mp ht).1 (congrArg Prod.snd
          (distinct (a₁:=(j,t)) (a₂:=(j,i)) (sub_eq_zero.mp eq).symm))
      have fac : P j = T*(X-C x) := by
        rw [split j,← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        dsimp [T,x]
        ring
      rw [fac,Polynomial.rootMultiplicity_mul (by rw [← fac]; exact unit _),
        Polynomial.rootMultiplicity_eq_zero val,Polynomial.rootMultiplicity_X_sub_C_self,if_pos rfl]
    · apply Eq.trans (Polynomial.rootMultiplicity_eq_zero ?_) (if_neg hk).symm
      rw [Polynomial.IsRoot.def,split,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_prod]
      apply mul_ne_zero (hA k) (Finset.prod_ne_zero_iff.mpr ?_)
      intro t _ h
      have hh : x = r k t := sub_eq_zero.mp (by simpa using h)
      exact hk (congrArg Prod.fst (distinct (a₁:=(j,i)) (a₂:=(k,t)) hh)).symm
  intro power
  have z := PhaseCharacter.power_multiplicities_vanish P unit (fun j => (e j:ℕ)) g power x
  simp only [res] at z
  have z' : ((e j:ℕ) : ZMod m) = 0 := by simpa using z
  apply hj
  apply Fin.ext
  exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp z') (e j).isLt

/-- From the ordinary one-variable Weil estimate and independence of these
specific polynomials to simultaneous nonzero prescribed values. The index
type may be a dependent sum of actual rational fibres of unequal sizes. -/
theorem logarithmic_polynomial_witness [Fintype E] {m l D : ℕ} [NeZero m]
    (hm : 2 ≤ m) (χ : MulChar E ℂ) (order : χ^m = 1) (P : J → E[X])
    (hnz : ∀ j, P j ≠ 0) (degree : ∀ j, (P j).natDegree ≤ D)
    (target : J → ℂ) (ht : ∀ j, target j^m = 1)
    (indep : ∀ e : J → Fin m, e ≠ 0 → ∀ g : (AlgebraicClosure E)[X],
      (∏ j, (P j)^(e j:ℕ)).map (algebraMap E (AlgebraicClosure E)) ≠ g^m)
    (weil : PolynomialWeilBound m χ) {L : ℝ}
    (threshold : 16384*(m:ℝ)^5 ≤ L)
    (budget : (l:ℝ)*(32*(m:ℝ)^2*Real.log m) ≤ L)
    (regime : (Fintype.card J ≤ 2*m*l ∧ L = Real.log (Fintype.card E)) ∨
      (Fintype.card J ≤ m*l ∧ L ≤ 4*m*Real.log (Fintype.card E)))
    (degreeScale : (D:ℝ) ≤ Real.exp (Real.log (Fintype.card E)/4)) :
    ∃ x : E, ∀ j, (P j).eval x ≠ 0 ∧ χ ((P j).eval x) = target j := by
  classical
  let M := Fintype.card J
  let X := Real.log (Fintype.card E)
  let b := Fintype.equivFin J
  let roots := univ.biUnion (fun j => (P j).roots.toFinset)
  let good : Finset E := univ \ roots
  have gsize : Fintype.card E - good.card ≤ M*D := by
    have eq : good.card = Fintype.card E - roots.card := Finset.card_sdiff (subset_univ roots)
    have le := Finset.card_le_univ roots
    have h : roots.card ≤ M*D := union_root_count P degree
    omega
  have regular (x : E) (hx : x ∈ good) (j : J) : (P j).eval x ≠ 0 := by
    intro h
    exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr
      ⟨j,mem_univ j, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hnz j)).2 h)⟩)
  let W := (M*D:ℕ)*Real.sqrt (Fintype.card E)
  have term (e : Fin M → Fin m) (he : e ≠ 0) :
      ‖∑ x : E, χ (∏ i, ((P (b.symm i)).eval x)^(e i:ℕ))‖ ≤ W := by
    let v (j : J) := e (b j)
    have hv : v ≠ 0 := by
      intro hv
      apply he
      funext i
      simpa [v] using congrFun hv (b.symm i)
    let g := ∏ j, (P j)^(v j:ℕ)
    have eq (x : E) : g.eval x = ∏ i, ((P (b.symm i)).eval x)^(e i:ℕ) := by
      dsimp only [g]
      rw [Polynomial.eval_prod]
      simp only [Polynomial.eval_pow]
      simpa [v] using (b.prod_comp (fun i => ((P (b.symm i)).eval x)^(e i:ℕ)))
    simp_rw [← eq]
    exact (weil g (indep v hv)).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast geometric_roots_le P hnz degree (fun j => (v j:ℕ))) (Real.sqrt_nonneg _))
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hq : (0:ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos (α := E)
  have x0 : 0 ≤ X := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := E))
  have scale : L ≤ 4*m*X := by
    rcases regime with ⟨_,h⟩ | ⟨_,h⟩
    · change L=X at h
      rw [h]
      nlinarith only [mul_nonneg (show 0 ≤ 4*(m:ℝ)-1 by linarith) x0]
    · exact h
  have fieldSize := (PhaseCharacter.explicit_field_threshold hm' threshold scale).1
  have Mlog := PhaseCharacter.pattern_budget hm budget regime x0
  have lm : (1:ℝ)/2 ≤ Real.log (m:ℝ) :=
    ((show (1:ℝ)/2 ≤ 0.6931471803 by norm_num).trans Real.log_two_gt_d9.le).trans
      (Real.log_le_log (by norm_num) hm')
  have msmall : (M:ℝ) ≤ X := by
    change (M:ℝ)*Real.log m ≤ X/8 at Mlog
    nlinarith only [Mlog,mul_le_mul_of_nonneg_left lm (Nat.cast_nonneg M),x0]
  have sq : Real.exp (X/2) = Real.sqrt (Fintype.card E) := by
    have hh : Real.exp (X/2)*Real.exp (X/2) = Fintype.card E := by
      rw [← Real.exp_add,show X/2+X/2=X by ring,Real.exp_log hq]
    nlinarith only [hh,Real.sq_sqrt hq.le,Real.exp_pos (X/2),Real.sqrt_nonneg (Fintype.card E:ℝ)]
  have es : (1:ℝ) ≤ Real.exp (X/2) := Real.one_le_exp (by linarith)
  have hs : Real.exp (X/4) * Real.exp (X/2) = Real.exp (3*X/4) := by
    rw [← Real.exp_add]; congr 1; ring
  have md : ((M*D:ℕ):ℝ) ≤ X*Real.exp (X/4) := by
    push_cast
    exact mul_le_mul msmall degreeScale (Nat.cast_nonneg _) x0
  have exc : ((Fintype.card E-good.card : ℕ):ℝ) ≤ ((M*D:ℕ):ℝ) := by exact_mod_cast gsize
  have total : W + 2*(Fintype.card E-good.card : ℕ) ≤
      8*(m:ℝ)^2*(1+X)*Real.exp (3*X/4) := by
    have h1 := mul_le_mul_of_nonneg_right md (Real.exp_pos (X/2)).le
    rw [mul_assoc X,hs] at h1
    have h2 := le_mul_of_one_le_right (Nat.cast_nonneg (M*D) : 0 ≤ ((M*D:ℕ):ℝ)) es
    have h3 : 3*X ≤ 8*(m:ℝ)^2*(1+X) := by
      have h4 : 3 ≤ 8*(m:ℝ)^2 := by nlinarith only [hm',sq_nonneg ((m:ℝ)-2)]
      nlinarith only [h4,mul_le_mul_of_nonneg_right h4 x0]
    dsimp only [W]
    rw [← sq]
    apply le_trans (b := 3*X*Real.exp (3*X/4))
    · linarith only [exc,h1,h2]
    · exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  obtain ⟨x,hx,pat⟩ := PhaseCharacter.logarithmic_character_witness hm χ order
    (fun (i : Fin M) x => (P (b.symm i)).eval x) (fun i => target (b.symm i))
    (fun i => ht _) good (fun x hx i => regular x hx _) (show 0 ≤ W by dsimp [W]; positivity)
    (show 0 ≤ 8*(m:ℝ)^2 by positivity) term total fieldSize budget regime
  exact ⟨x,fun j => ⟨regular x hx j, by simpa using pat (b j)⟩⟩

end BlockingCurves.PiecewiseWeil
