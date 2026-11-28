import NormCubicTrace
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.Tactic.LinearCombination

/-! Three prescribed points in a cubic extension lie on a common sphere of
nonzero norm.  The auxiliary norm pair is realized by an irreducible cubic
whose quadratic coefficient can avoid one additional prescribed value. -/
namespace BlockingCurves.CuspidalCubicSphere
noncomputable section
open Polynomial
open scoped Polynomial

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
  [Algebra F E] [FiniteDimensional F E]

private def cubic (A B k : F) : F[X] :=
  X^3 + (C k * X^2 + C (k+B-A-1) * X - C A)

private theorem cubic_degree (A B k : F) : (cubic A B k).natDegree = 3 := by
  unfold cubic
  compute_degree <;> norm_num

private theorem cubic_monic (A B k : F) : (cubic A B k).Monic := by
  apply monic_X_pow_add
  compute_degree
  norm_num
  exact le_rfl

private theorem cubic_coeff (A B k : F) : (cubic A B k).coeff 2 = k := by
  simp [cubic, coeff_X_pow, coeff_C_mul, coeff_C, coeff_one]

private theorem choose_cubic (A B forbidden : F) (ha : A ≠ 0) (hb : B ≠ 0) :
    ∃ k ≠ forbidden, Irreducible (cubic A B k) := by
  classical
  let bad : Fˣ → F := fun w => if (w:F) = -1 then forbidden else
    (A-(w:F)^3-(B-A-1)*(w:F))/((w:F)^2+(w:F))
  obtain ⟨k,hk⟩ : ∃ k, ∀ w, bad w ≠ k := by
    by_contra! h
    have hh := Fintype.card_le_of_surjective bad h
    rw [Fintype.card_units] at hh
    have := Fintype.card_pos (α := F)
    omega
  have avoid := hk (-1)
  have hkf : k ≠ forbidden := by simpa [bad, ne_comm] using avoid
  have hd := cubic_degree A B k
  refine ⟨k,hkf,(irreducible_iff_roots_eq_zero_of_degree_le_three (p := cubic A B k)
    (by omega) (by omega)).2 (Multiset.eq_zero_iff_forall_not_mem.2 ?_)⟩
  intro x hx
  have ev := (mem_roots (p := cubic A B k) (fun he => by simp [he] at hd)).1 hx
  change (cubic A B k).eval x = 0 at ev
  simp [cubic] at ev
  by_cases h0 : x = 0
  · simp [h0,ha] at ev
  by_cases h1 : x = -1
  · subst x
    apply hb
    linear_combination -ev
  apply hk (Units.mk0 x h0)
  change (if x = -1 then forbidden else _) = k
  rw [if_neg h1]
  change (A-x^3-(B-A-1)*x)/(x^2+x)=k
  apply (div_eq_iff ?_).2
  · linear_combination -ev
  · rw [show x^2+x=x*(x+1) by ring]
    exact mul_ne_zero h0 (fun h => h1 (eq_neg_of_add_eq_zero_left h))

/-- In a cubic extension two consecutive norms can be prescribed while
avoiding a specified point of the extension, including in characteristics
two and three. -/
theorem norm_pair_avoiding (rank : FiniteDimensional.finrank F E = 3)
    (A B : F) (ha : A ≠ 0) (hb : B ≠ 0) (u : E) :
    ∃ y : E, y ≠ u ∧ Algebra.norm F y = A ∧ Algebra.norm F (y+1) = B := by
  classical
  obtain ⟨k,hk,hi⟩ := choose_cubic A B ((minpoly F u).coeff 2) ha hb
  let P := cubic A B k
  have hm := cubic_monic A B k
  letI : Fact (Irreducible P) := ⟨hi⟩
  let pb := AdjoinRoot.powerBasis hm.ne_zero
  letI : FiniteDimensional F (AdjoinRoot P) := FiniteDimensional.of_fintype_basis pb.basis
  letI : Fintype (AdjoinRoot P) := FiniteDimensional.fintypeOfFintype F _
  have dim : pb.dim = 3 := cubic_degree A B k
  have card : Fintype.card (AdjoinRoot P) = Fintype.card E := by
    rw [card_eq_pow_finrank (K := F), card_eq_pow_finrank (K := F) (V := E),
      FiniteDimensional.finrank_eq_card_basis pb.basis, Fintype.card_fin, dim, rank]
  let e := NormPencil.sameCardEquiv F (AdjoinRoot P) E card
  let basis := pb.map e
  have minp : minpoly F basis.gen = P := by
    rw [show basis.gen = e pb.gen from rfl, minpoly.algEquiv_eq,
      AdjoinRoot.minpoly_powerBasis_gen_of_monic hm]
  have shifted : basis.gen ∈ Algebra.adjoin F ({basis.gen+1} : Set E) := by
    have h : basis.gen+1 ∈ Algebra.adjoin F ({basis.gen+1} : Set E) :=
      Algebra.subset_adjoin (Set.mem_singleton _)
    simpa using (Algebra.adjoin F ({basis.gen+1} : Set E)).sub_mem h
      (Algebra.adjoin F _).one_mem
  have hint := Algebra.IsIntegral.isIntegral (R := F) (basis.gen+1)
  let basis' := basis.ofGenMemAdjoin hint shifted
  have mp : minpoly F (basis.gen+1) = P.comp (X-C 1) := by
    simpa [minp] using minpoly.add_algebraMap (Algebra.IsIntegral.isIntegral (R := F) basis.gen) 1
  have hdim : basis'.dim = 3 := basis'.finrank.symm.trans rank
  refine ⟨basis.gen,?_,?_,?_⟩
  · intro eq
    apply hk
    rw [← eq,minp]
    exact (cubic_coeff A B k).symm
  · rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,minp,show basis.dim=3 from dim]
    norm_num [P,cubic,coeff_X_pow,coeff_C_mul,coeff_C]
  · have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly basis'
    rw [show basis'.gen=basis.gen+1 from rfl,
      hdim,mp,coeff_zero_eq_eval_zero,eval_comp] at h
    rw [h]
    simp [P,cubic]
    ring

private theorem three_norms (rank : FiniteDimensional.finrank F E = 3)
    (a b c : E) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ z : E, ∃ R : F, R ≠ 0 ∧ Algebra.norm F (z+a) = R ∧
      Algebra.norm F (z+b) = R ∧ Algebra.norm F (z+c) = R := by
  let u := (b-c)/(a-b)
  have hab' := sub_ne_zero.mpr hab
  have hac' := sub_ne_zero.mpr hac
  have hbc' := sub_ne_zero.mpr hbc
  have hu : u ≠ 0 := div_ne_zero hbc' hab'
  have shift : u+1 = (a-c)/(a-b) := by
    dsimp [u]; field_simp [hab']
  have hu1 : u+1 ≠ 0 := shift ▸ div_ne_zero hac' hab'
  have Nu : Algebra.norm F u ≠ 0 := Algebra.norm_ne_zero_iff.mpr hu
  have Nu1 : Algebra.norm F (u+1) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hu1
  obtain ⟨y,hy,hy0,hy1⟩ := norm_pair_avoiding rank _ _ Nu Nu1 u
  let w := u*(a-c)/(y-u)
  have hw : w ≠ 0 := div_ne_zero (mul_ne_zero hu hac') (sub_ne_zero.mpr hy)
  have eqA : w-c+a = w*(y/u) := by
    dsimp [w]; field_simp [sub_ne_zero.mpr hy,hu]; ring
  have eqB : w-c+b = w*((y+1)/(u+1)) := by
    have rel : (b-c)*(u+1) = u*(a-c) := by
      dsimp [u]; field_simp [hab']
    have clearDen : w*(y-u) = u*(a-c) := div_mul_cancel₀ _ (sub_ne_zero.mpr hy)
    rw [← mul_div_assoc, eq_div_iff hu1]
    calc
      _ = w*(u+1)+(b-c)*(u+1) := by ring
      _ = w*(u+1)+w*(y-u) := by rw [rel,clearDen]
      _ = _ := by ring
  have ratio (x v : E) (hv : v ≠ 0) (same : Algebra.norm F x = Algebra.norm F v) :
      Algebra.norm F (x/v) = 1 := by
    apply mul_right_cancel₀ (Algebra.norm_ne_zero_iff.mpr hv)
    rw [← map_mul, div_mul_cancel₀ _ hv, one_mul,same]
  refine ⟨w-c,Algebra.norm F w,Algebra.norm_ne_zero_iff.mpr hw,?_,?_,?_⟩
  · rw [eqA,map_mul,ratio y u hu hy0,mul_one]
  · rw [eqB,map_mul,ratio (y+1) (u+1) hu1 hy1,mul_one]
  · simp

/-- Every set of at most three points lies on a nonzero norm sphere in a
cubic extension of finite fields. -/
theorem sphere_through_three (rank : FiniteDimensional.finrank F E = 3)
    (S : Finset E) (small : S.card ≤ 3) :
    ∃ z : E, ∃ R : F, R ≠ 0 ∧ ∀ a ∈ S, Algebra.norm F (z+a) = R := by
  classical
  have q : 3 ≤ Fintype.card E := by
    rw [card_eq_pow_finrank (K := F),rank]
    have pos : 1 < Fintype.card F := Fintype.one_lt_card
    exact (by decide : 3 ≤ 2^3).trans (Nat.pow_le_pow_left pos 3)
  obtain ⟨T,sub,_,card⟩ := Finset.exists_intermediate_set (3-S.card)
    (A := (Finset.univ : Finset E)) (B := S)
    (by rw [Nat.sub_add_cancel small, Finset.card_univ]; exact q) (Finset.subset_univ _)
  rw [Nat.sub_add_cancel small] at card
  obtain ⟨a,b,c,hab,hac,hbc,hT⟩ := Finset.card_eq_three.mp card
  obtain ⟨z,R,hR,ha,hb,hc⟩ := three_norms rank a b c hab hac hbc
  refine ⟨z,R,hR,fun v hv => ?_⟩
  have mem := sub hv
  rw [hT] at mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl <;> assumption

end
end BlockingCurves.CuspidalCubicSphere
