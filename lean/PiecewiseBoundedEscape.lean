import PiecewiseCharacter
import PiecewiseNormPolynomial
import PiecewiseWeil
import PiecewiseFrobenius

namespace BlockingCurves.PiecewiseBoundedEscape

open Polynomial Finset NormPencil PiecewiseFrobenius
open scoped BigOperators
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  [FiniteDimensional F E]

private theorem nonpower_of_affine_factors {J I : Type*} [Fintype J] [Fintype I] [Nonempty I]
    {m : ℕ} [NeZero m] (P : J → F[X]) (v w : J → I → E) (nw : ∀ j i, w j i ≠ 0)
    (factor : ∀ j, (P j).map (algebraMap F E)=∏ i, (C (v j i)+C (w j i)*X))
    (distinct : Function.Injective (fun k : J×I => -(v k.1 k.2/w k.1 k.2)))
    (e : J → Fin m) (active : e ≠ 0) (g : (AlgebraicClosure F)[X]) :
    (∏ j, (P j)^(e j:ℕ)).map (algebraMap F (AlgebraicClosure F)) ≠ g^m := by
  classical
  let b : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let root (j : J) (i : I) := b (-(v j i / w j i))
  let k (j : J) := ∏ i, b (w j i)
  have hn (j : J) : k j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (map_ne_zero b).2 (nw j i))
  have mapEq : b.toRingHom.comp (algebraMap F E)=algebraMap F (AlgebraicClosure F) :=
    RingHom.ext (fun x => b.commutes x)
  have split (j : J) : (P j).map (algebraMap F (AlgebraicClosure F))=
      C (k j) * ∏ i, (X-C (root j i)) := by
    rw [← mapEq,← Polynomial.map_map,factor,Polynomial.map_prod]
    dsimp only [k]
    rw [map_prod,← Finset.prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    simp only [Polynomial.map_add,Polynomial.map_mul,map_C,map_X,root,map_neg,_root_.map_div,
      map_neg,sub_neg_eq_add,mul_add,← map_mul]
    rw [mul_div_cancel₀ _ (nw j i),add_comm]
    rfl
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_pow]
  exact PiecewiseWeil.nonpower_of_split_roots _ k root hn split
    (fun _ _ eq => distinct (b.injective eq)) e active g

private theorem slice_room {s n m l r : ℕ} (hm : 2 ≤ m) (hr : r ≤ m) (hn : n < 4*m)
    (hs : 1<s) {L : ℝ} (scale : L ≤ 4*m*Real.log s)
    (fieldSize : 16384*(m:ℝ)^5 ≤ L) (budget : (l:ℝ)*(32*(m:ℝ)^2*Real.log m) ≤ L) :
    r+r^2<s-1 ∧ (r*n*l)^2<s := by
  let X := Real.log s
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hX,big⟩ := PhaseCharacter.explicit_field_threshold hm' fieldSize scale
  have ex := Real.exp_log (by exact_mod_cast (Nat.zero_lt_of_lt hs) : (0:ℝ)<s)
  rw [ex] at big
  have lm : (1:ℝ)/2 ≤ Real.log m := ((show (1:ℝ)/2 ≤ 0.6931471803 by norm_num).trans
    Real.log_two_gt_d9.le).trans (Real.log_le_log (by norm_num) hm')
  have K : 4*(m:ℝ) ≤ 32*(m:ℝ)^2*Real.log m := by
    nlinarith only [mul_le_mul_of_nonneg_left lm (sq_nonneg (m:ℝ)),hm',sq_nonneg ((m:ℝ)-1)]
  have leL : (l:ℝ) ≤ X := by
    apply le_of_mul_le_mul_left (a:=4*(m:ℝ)) _ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left K (Nat.cast_nonneg l),scale,budget]
  have len : ((r*n*l:ℕ):ℝ) ≤ 4*(m:ℝ)^2*X := by
    push_cast
    calc
      _ ≤ (m:ℝ)*(4*m)*X := mul_le_mul (mul_le_mul
        (by exact_mod_cast hr) (by exact_mod_cast hn.le) (Nat.cast_nonneg n) (Nat.cast_nonneg m))
        leL (Nat.cast_nonneg l) (by positivity)
      _ = _ := by ring
  have hs' : Real.log (s:ℝ) ≤ s := (Real.log_le_sub_one_of_pos
    (by exact_mod_cast (Nat.zero_lt_of_lt hs))).trans (by linarith)
  have prelim : m+m^2+1 < s := by
    have h : (m:ℝ)+(m:ℝ)^2+1<s := by nlinarith only [hs',hX,hm',sq_nonneg ((m:ℝ)-1)]
    exact_mod_cast h
  constructor
  · have small := Nat.add_le_add hr (Nat.pow_le_pow_left hr 2)
    omega
  · exact_mod_cast (pow_le_pow_left (Nat.cast_nonneg (r*n*l) : (0:ℝ) ≤ _) len 2).trans_lt big

/-- For 2 ≤ n < 4m, the sole analytic input is a standard Weil bound over F.
The slope, slice, character, norm polynomials, and nonpower check are constructed here. -/
theorem bounded_table_escape {m : ℕ} (hm : 2 ≤ m)
    (hn : 2 ≤ FiniteDimensional.finrank F E) (short : FiniteDimensional.finrank F E < 4*m)
    (divides : m ∣ Fintype.card F-1) (table : E → Fˣ) (Cfs : Finset Fˣ)
    (labels : ∀ u : Eˣ, table ((u:E)^((Fintype.card E-1)/m)) ∈ Cfs)
    (two : ∃ u v : Eˣ, table ((u:E)^((Fintype.card E-1)/m)) ≠ table ((v:E)^((Fintype.card E-1)/m)))
    (few : Cfs.card ≤ m) (S : Finset E)
    (weil : ∀ χ : MulChar F ℂ, orderOf χ=m → PiecewiseWeil.PolynomialWeilBound m χ)
    (threshold : 16384*(m:ℝ)^5 ≤ Real.log (Fintype.card E))
    (budget : (S.card:ℝ)*(32*(m:ℝ)^2*Real.log m) ≤ Real.log (Fintype.card E)) :
    ¬ GraphHits (branchMap (fun x : E => (table (x^((Fintype.card E-1)/m)):F))) (S:Set E) := by
  classical
  let n := FiniteDimensional.finrank F E
  let N := normExponent (Fintype.card F) n
  let e := (Fintype.card E-1)/m
  let k := (Fintype.card F-1)/m
  have dim : Fintype.card E = Fintype.card F^n := card_eq_pow_finrank
  have hN : 0 < N := normExponent_pos Fintype.card_pos (by omega : 0<n)
  have label_exp : e=N*k := by
    dsimp only [e,k,N]
    rw [dim,← normExponent_mul (Fintype.card F) n Fintype.card_pos,Nat.add_sub_cancel,
      Nat.mul_div_assoc _ divides]
  have scale : Real.log (Fintype.card E) ≤ 4*m*Real.log (Fintype.card F) := by
    rw [dim,Nat.cast_pow,Real.log_pow]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast short.le)
      (Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α:=F)))
  obtain ⟨scope,room⟩ := slice_room hm few short Fintype.one_lt_card scale threshold budget
  obtain ⟨a,σ,A,u,frob,inv,inj⟩ := PiecewiseNormSlice.separated_inverse_slice Cfs S hn scope room
  have period : σ^n=1 := by
    change σ ^ FiniteDimensional.finrank F E = 1
    rw [← relative_order σ frob]
    exact pow_orderOf_eq_one σ
  let J := Cfs × S
  let x (j : J) := A j.1 (u+j.2.val)
  let y (j : J) := A j.1 1
  have ny (j : J) : y j≠0 := (A j.1).map_ne_zero_iff.mpr one_ne_zero
  choose P factor degree value using
    (fun j : J => PiecewiseNormSlice.norm_polynomial σ frob period (x j) (y j) (ny j))
  let vv (j:J) (i:Fin n) := (σ^i.val) (x j)
  let ww (j:J) (i:Fin n) := (σ^i.val) (y j)
  have sep : Function.Injective (fun z:J×Fin n => -(vv z.1 z.2 / ww z.1 z.2)) := by
    rintro ⟨⟨c,α⟩,i⟩ ⟨⟨d,γ⟩,j⟩ eq
    have same := inj (a₁:=((c,i),α)) (a₂:=((d,j),γ)) eq
    cases same
    rfl
  letI : NeZero m := ⟨by omega⟩
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have np := nonpower_of_affine_factors P vv ww (fun j i => (_root_.map_ne_zero _).2 (ny j)) factor sep
    (m:=m)
  obtain ⟨χ,order,lab⟩ := PiecewiseCharacter.exists_power_label_character (E:=F) (by omega : 0<m) divides
  have χm : χ^m=1 := order ▸ pow_orderOf_eq_one χ
  obtain ⟨v,w,hvw⟩ := two
  let sel (c : Cfs) := if table ((v:E)^e)=c.val then w else v
  have wrong (c : Cfs) : table ((sel c:E)^e) ≠ c.val := by
    dsimp only [sel]
    split_ifs with h
    · exact fun eq => hvw (h.trans eq.symm)
    · exact h
  choose z hz using (fun c : Cfs => norm_in_ground (by omega : 0<n) dim (sel c:E))
  have nz (c : Cfs) : z c ≠ 0 := by
    intro h
    have eq := hz c
    rw [h,map_zero] at eq
    exact pow_ne_zero _ (sel c).ne_zero eq.symm
  have ht (j:J) : (χ (z j.1))^m=1 := by
    rw [← MulChar.pow_apply' χ (NeZero.ne m),χm,MulChar.one_apply (isUnit_iff_ne_zero.2 (nz _))]
  have count : Fintype.card J ≤ m*S.card := by
    simpa only [J,Fintype.card_prod,Fintype.card_coe] using Nat.mul_le_mul_right S.card few
  obtain ⟨t,pat⟩ := PiecewiseWeil.logarithmic_polynomial_witness hm χ χm P
    (fun j h => by have d := degree j; simp [h] at d; omega) (fun j => (degree j).le)
    (fun j => χ (z j.1)) ht np (weil χ order) threshold budget (Or.inr ⟨count,scale⟩)
    (PiecewiseWeil.bounded_degree_scale hm short.le threshold scale)
  intro hit
  let b := u+algebraMap F E t
  obtain ⟨v₀,hα⟩ := hit a b
  let c : Cfs := if h : v₀=0 then ⟨_,labels v⟩ else ⟨_,labels (Units.mk0 v₀ h)⟩
  let α : S := ⟨_,hα⟩
  let j : J := (c,α)
  have eq : algebraMap F E (c.val:F)*σ v₀-(a:E)*v₀=b+α.val := by
    dsimp only [α,branchMap]
    rw [frob]
    by_cases h : v₀=0
    · simp [h,zero_pow Fintype.card_pos.ne']
    · simp [c,h]
  obtain ⟨v₁,hv₁⟩ := (A c).surjective v₀
  have eqk : v₁=b+α.val := by simpa [← hv₁,inv] using eq
  have hx : x j + algebraMap F E t * y j = v₀ := by
    rw [← hv₁,eqk]
    have hs : algebraMap F E t = t • (1:E) := by simp [Algebra.smul_def]
    change A c (u+α.val) + algebraMap F E t * A c 1 = A c (u+algebraMap F E t+α.val)
    rw [show u+algebraMap F E t+α.val = (u+α.val)+t • (1:E) by rw [←hs]; abel]
    rw [(A c).map_add (u+α.val) _, (A c).map_smul,Algebra.smul_def]
  have norm := value j t
  rw [hx] at norm
  have vne : v₀ ≠ 0 := by
    intro zero
    rw [zero,zero_pow hN.ne'] at norm
    exact (pat j).1 (((algebraMap F E).injective) (norm.trans (map_zero _).symm))
  have labelEq := (lab _ _).mp (pat j).2
  have same := congrArg (algebraMap F E) labelEq
  rw [map_pow,map_pow,norm,hz,← pow_mul,← pow_mul,← label_exp] at same
  apply wrong c
  change table ((sel c:E)^e)=_
  rw [← same]
  simp [c,vne,e]

end BlockingCurves.PiecewiseBoundedEscape
