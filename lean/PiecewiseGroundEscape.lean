import PiecewiseWeil
import PiecewiseCharacter
import PiecewiseFrobenius

/-! On the ground field the Frobenius is the identity. A slope equal to
the coefficient of the identity label loses a whole multiplicative coset.
The polynomials prescribing that missing class have distinct simple roots. -/
namespace BlockingCurves.PiecewiseGroundEscape

open Finset Polynomial PiecewiseWeil
open scoped BigOperators Polynomial

variable {E : Type*} [Field E] [Fintype E]

/-- Some realized power label is absent from all nonzero outputs on this
slope. The coefficient table need not be injective or a permutation. -/
theorem exists_missing_label (table : E → E) (e : ℕ) :
    ∃ v : Eˣ, ∀ x : E, (table (x^e)-table 1)*x ≠ 0 →
      ((table (x^e)-table 1)*x)^e ≠ (v:E)^e := by
  classical
  let U := (univ : Finset Eˣ).image (fun v : Eˣ => (v:E)^e)
  have one : 1 ∈ U := mem_image.mpr ⟨1,mem_univ _,by simp⟩
  let g (z:E) := (table z-table 1)^e*z
  have smaller : ((U.erase 1).image g).card < U.card :=
    card_image_le.trans_lt (card_erase_lt_of_mem one)
  have omitted : ¬ U ⊆ (U.erase 1).image g := fun h => (Nat.not_le_of_lt smaller) (card_le_card h)
  obtain ⟨label,realized,missing⟩ := Finset.not_subset.mp omitted
  obtain ⟨v,_,rfl⟩ := mem_image.mp realized
  refine ⟨v,fun x nz eq => missing ?_⟩
  have hx : x ≠ 0 := fun h => nz (by simp [h])
  have hlabel : x^e ≠ 1 := fun h => nz (by simp [h])
  have present : x^e ∈ U := mem_image.mpr ⟨Units.mk0 x hx,mem_univ _,rfl⟩
  exact mem_image.mpr ⟨x^e,mem_erase.mpr ⟨hlabel,present⟩,
    (mul_pow (table (x^e)-table 1) x e).symm.trans eq⟩

/-- A finite inequality, valid for every field size and every parameter set.
The nonzero frequencies have at most one geometric root per translate. -/
theorem ground_table_escape_of_gap {m : ℕ} (hm : 2 ≤ m) (dvd : m ∣ Fintype.card E-1)
    (table : E → E) (S : Finset E)
    (gap : (S.card:ℝ)*(Real.sqrt (Fintype.card E)+2) < Fintype.card E/(m:ℝ)^S.card)
    (weil : ∀ χ : MulChar E ℂ, orderOf χ=m → PolynomialWeilBound m χ) :
    let e := (Fintype.card E-1)/m
    ∃ b : E, ∀ x : E, table (x^e)*x-table 1*x-b ∉ S := by
  classical
  letI : NeZero m := ⟨by omega⟩
  intro e
  obtain ⟨v,missing⟩ := exists_missing_label table e
  obtain ⟨χ,order,label⟩ := PiecewiseCharacter.exists_power_label_character (by omega : 0<m) dvd
  have powEq : χ^m=1 := order ▸ pow_orderOf_eq_one χ
  let P (j:S) : E[X] := X-C (-(j:E))
  let H := AlgebraicClosure E
  let embed := algebraMap E H
  let r (j:S) (_i:Unit) : H := embed (-(j:E))
  have distinct : Function.Injective (fun ji : S × Unit => r ji.1 ji.2) := by
    intro i j h
    exact Prod.ext (Subtype.ext (neg_injective (embed.injective h))) (Subsingleton.elim _ _)
  have noPower (a : S → Fin m) (ha : a ≠ 0) (g : H[X]) :
      (∏ j, (P j)^(a j:ℕ)).map embed ≠ g^m := by
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_pow]
    exact nonpower_of_split_roots (fun j => (P j).map embed) (fun _ => 1) r
      (fun _ => one_ne_zero) (fun j => by simp [r,P]) distinct a ha g
  have target : (χ (v:E))^m=1 := by
    rw [← χ.pow_apply' (NeZero.ne m),powEq,MulChar.one_apply v.isUnit]
  let M := Fintype.card S
  let labelAt := (Fintype.equivFin S).symm
  let D := (S.image (fun z => -z))ᶜ
  have exc : Fintype.card E - D.card = S.card := by
    rw [show D.card = Fintype.card E-(S.image (fun z => -z)).card from card_compl _,
      card_image_of_injective _ neg_injective,Nat.sub_sub_self (card_le_univ _)]
  have regular (b : E) (hb : b ∈ D) (i : Fin M) : (P (labelAt i)).eval b ≠ 0 := by
    simp only [P,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_eq_zero]
    intro eq
    exact (mem_compl.mp hb) (mem_image.mpr ⟨_,(labelAt i).property,(sub_eq_zero.mp eq).symm⟩)
  have bound (a : Fin M → Fin m) (ha : a ≠ 0) :
      ‖∑ b : E, χ (∏ i, ((P (labelAt i)).eval b)^(a i : ℕ))‖ ≤
      (S.card:ℝ)*Real.sqrt (Fintype.card E) := by
    let freq (j:S) := a (labelAt.symm j)
    have nz : freq ≠ 0 := fun h => ha (by funext i; simpa [freq] using congrFun h (labelAt i))
    let G := ∏ j, (P j)^(freq j:ℕ)
    have ev (b:E) : G.eval b = ∏ i, ((P (labelAt i)).eval b)^(a i:ℕ) := by
      dsimp only [G]
      rw [Polynomial.eval_prod]
      simp only [Polynomial.eval_pow]
      simpa [freq] using labelAt.symm.prod_comp (fun i => ((P (labelAt i)).eval b)^(a i:ℕ))
    simp_rw [← ev]
    have roots : rootCount G ≤ S.card := by
      simpa only [Fintype.card_coe,Nat.mul_one] using geometric_roots_le P
        (fun _ => X_sub_C_ne_zero _) (D:=1) (fun j => by simp [P]) (fun j => (freq j : ℕ))
    exact (weil χ order G (noPower freq nz)).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast roots) (Real.sqrt_nonneg _))
  obtain ⟨b,hb,values⟩ := PhaseCharacter.character_pattern_exists χ powEq
    (fun (i:Fin M) b => (P (labelAt i)).eval b) (fun _ => χ (v:E)) (fun _ => target)
    D regular (by positivity) bound (by
      rw [exc]
      change _ < _/(m:ℝ)^(Fintype.card S)
      rw [Fintype.card_coe]
      linarith only [gap])
  have witness (j:S) : (P j).eval b ≠ 0 ∧ χ ((P j).eval b) = χ (v:E) := by
    simpa using And.intro (regular b hb (labelAt.symm j)) (values (labelAt.symm j))
  refine ⟨b,fun x hit => ?_⟩
  let z := (table (x^e)-table 1)*x
  have hz : z-b ∈ S := by simpa only [z,sub_mul] using hit
  obtain ⟨nz,hχ⟩ := witness ⟨z-b,hz⟩
  have val : (P ⟨z-b,hz⟩).eval b = z := by simp [P]
  rw [val] at nz hχ
  exact missing x nz ((label z (v:E)).1 hχ)

/-- The uniform logarithmic budget used throughout the coefficient-period
theorem implies the finite linear-factor inequality. -/
theorem ground_table_escape {m : ℕ} (hm : 2 ≤ m) (dvd : m ∣ Fintype.card E-1)
    (table : E → E) (S : Finset E)
    (threshold : 16384*(m:ℝ)^5 ≤ Real.log (Fintype.card E))
    (budget : (S.card:ℝ)*(32*(m:ℝ)^2*Real.log m) ≤ Real.log (Fintype.card E))
    (weil : ∀ χ : MulChar E ℂ, orderOf χ=m → PolynomialWeilBound m χ) :
    let e := (Fintype.card E-1)/m
    ∃ b : E, ∀ x : E, table (x^e)*x-table 1*x-b ∉ S := by
  let q : ℝ := Fintype.card E
  let L := Real.log q
  have hp : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α:=E)
  have hl : 0 ≤ L := Real.log_nonneg (by dsimp [q]; exact_mod_cast Fintype.card_pos (α:=E))
  have hmR : 2 ≤ (m:ℝ) := by exact_mod_cast hm
  have mlog := PhaseCharacter.pattern_budget (M:=S.card) hm budget
    (Or.inl ⟨Nat.le_mul_of_pos_left _ (by positivity),rfl⟩) hl
  have logmin : (1:ℝ)/2 ≤ Real.log m :=
    ((by norm_num : (1:ℝ)/2 ≤ 0.6931471803).trans Real.log_two_gt_d9.le).trans
      (Real.log_le_log (by norm_num) hmR)
  have ell : (S.card:ℝ) ≤ L := by
    nlinarith only [mlog,mul_le_mul_of_nonneg_left logmin (Nat.cast_nonneg S.card),hl]
  have threshold' := (PhaseCharacter.explicit_field_threshold hmR threshold (show L ≤ 4*m*L by
    nlinarith only [mul_nonneg (show 0 ≤ 4*(m:ℝ)-1 by linarith) hl])).1
  have upper : 3 ≤ 8*(m:ℝ)^2 := by nlinarith only [sq_nonneg ((m:ℝ)-2),hmR]
  have sqrtEq : Real.sqrt q=Real.exp (L/2) := by
    have h : Real.exp (L/2)*Real.exp (L/2)=q := by
      rw [← Real.exp_add,show L/2+L/2=L by ring, Real.exp_log hp]
    nlinarith only [h,Real.sq_sqrt hp.le,Real.exp_pos (L/2),Real.sqrt_nonneg q]
  have sqle : Real.sqrt q ≤ Real.exp (3*L/4) := sqrtEq ▸ Real.exp_le_exp.mpr (by linarith)
  have exp1 : 1 ≤ Real.exp (3*L/4) := Real.one_le_exp (by linarith)
  apply ground_table_escape_of_gap hm dvd table S _ weil
  calc
    (S.card:ℝ)*(Real.sqrt q+2) ≤ L*(3*Real.exp (3*L/4)) :=
      mul_le_mul ell (by linarith only [sqle,exp1]) (by positivity) hl
    _ ≤ 8*(m:ℝ)^2*(1+L)*Real.exp (3*L/4) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith only [mul_le_mul_of_nonneg_right upper hl,upper]
    _ < _ := PhaseCharacter.main_term_dominates hp hm (by positivity) threshold' mlog

/-- The sharper necessary condition before applying the common logarithmic
budget. It applies to extensions of relative degree one on arbitrary models. -/
theorem ground_table_finite_lower {F : Type*} [Field F] [Fintype F] [Algebra F E]
    {m : ℕ} (hm : 2 ≤ m) (dvd : m ∣ Fintype.card E-1) (size : Fintype.card E=Fintype.card F)
    (table : E → F) (S : Finset E)
    (weil : ∀ χ : MulChar E ℂ, orderOf χ=m → PolynomialWeilBound m χ) :
    let e := (Fintype.card E-1)/m
    GraphHits (PiecewiseFrobenius.branchMap (fun x:E => table (x^e))) (S:Set E) →
      Fintype.card E/(m:ℝ)^S.card ≤ (S.card:ℝ)*(Real.sqrt (Fintype.card E)+2) := by
  intro e blocks
  by_contra! gap
  obtain ⟨b,escape⟩ := ground_table_escape_of_gap hm dvd (fun z => algebraMap F E (table z)) S gap weil
  obtain ⟨x,hx⟩ := blocks (algebraMap F E (table 1)) b
  exact escape x (by simpa only [PiecewiseFrobenius.branchMap,← size,FiniteField.pow_card] using hx)

theorem ground_table_card_lower {F : Type*} [Field F] [Fintype F] [Algebra F E]
    {m : ℕ} (hm : 2 ≤ m) (dvd : m ∣ Fintype.card E-1) (size : Fintype.card E=Fintype.card F)
    (table : E → F) (S : Finset E)
    (threshold : 16384*(m:ℝ)^5 ≤ Real.log (Fintype.card E))
    (weil : ∀ χ : MulChar E ℂ, orderOf χ=m → PolynomialWeilBound m χ) :
    let e := (Fintype.card E-1)/m
    GraphHits (PiecewiseFrobenius.branchMap (fun x:E => table (x^e))) (S:Set E) →
      Real.log (Fintype.card E) < (S.card:ℝ)*(32*(m:ℝ)^2*Real.log m) := by
  intro e blocks
  by_contra! budget
  obtain ⟨b,escape⟩ := ground_table_escape hm dvd (fun z => algebraMap F E (table z)) S threshold budget weil
  obtain ⟨x,hx⟩ := blocks (algebraMap F E (table 1)) b
  apply escape x
  simpa only [PiecewiseFrobenius.branchMap,← size,FiniteField.pow_card] using hx

/-- Taking logarithms retains the coefficient 1/(2 log m), with an explicit
log-log loss and no lower threshold on the field size. -/
theorem half_log_of_finite_lower {q : ℝ} {m l : ℕ} (hq : 1 ≤ q) (hm : 2 ≤ m)
    (bound : q/(m:ℝ)^l ≤ (l:ℝ)*(Real.sqrt q+2)) :
    Real.log q/2-Real.log (3*(1+Real.log q)) ≤ (l:ℝ)*Real.log m := by
  have pos : 0 < q := by linarith
  have logq := Real.log_nonneg hq
  have mpos : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have sqrtpos := Real.sqrt_pos.mpr pos
  have sqrtone : 1 ≤ Real.sqrt q := by nlinarith only [Real.sq_sqrt pos.le,sqrtpos,hq]
  by_cases small : (l:ℝ) ≤ Real.log q
  · have b := (div_le_iff (pow_pos mpos l)).1 bound
    have aux : (l:ℝ)*(Real.sqrt q+2) ≤ (1+Real.log q)*(3*Real.sqrt q) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    have scaled := b.trans (mul_le_mul_of_nonneg_right aux (pow_pos mpos l).le)
    have cancel : Real.sqrt q ≤ (3*(1+Real.log q))*(m:ℝ)^l := by
      apply le_of_mul_le_mul_right (a:=Real.sqrt q) _ sqrtpos
      rw [← sq,Real.sq_sqrt pos.le]
      linarith only [scaled]
    have logged := Real.log_le_log sqrtpos cancel
    rw [Real.log_sqrt pos.le,Real.log_mul (by positivity) (pow_pos mpos l).ne',Real.log_pow] at logged
    linarith only [logged]
  · have logmin : (1:ℝ)/2 ≤ Real.log m :=
      ((by norm_num : (1:ℝ)/2 ≤ 0.6931471803).trans Real.log_two_gt_d9.le).trans
        (Real.log_le_log (by norm_num) hmR)
    have lognonneg : 0 ≤ Real.log (3*(1+Real.log q)) := Real.log_nonneg (by linarith)
    linarith only [not_le.mp small,lognonneg,mul_le_mul_of_nonneg_left logmin (Nat.cast_nonneg l)]

end BlockingCurves.PiecewiseGroundEscape
