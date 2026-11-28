import CuspidalNorm
import CuspidalNontrivial
import CuspidalCubicSphere
import StatementComparison

namespace BlockingCurves.CuspidalNorm

open Finset Polynomial FiniteDimensional NormPencil
open scoped BigOperators

variable (F : Type*) {E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
  [Algebra F E] [FiniteDimensional F E]

/-- The actual cusp-pencil minimum is attained by S of the indicated cardinality. -/
def IsMinimum (d k : ℕ) (E : Type*) [Field E] : Prop :=
  IsLeast {j : ℕ | ∃ S : Finset E, S.card=j ∧ CuspidalGeneral.Blocks d (S : Set E)} k

theorem blocks_iff_no_sphere (S : Finset E) (small : S.card < Fintype.card F) :
    CuspidalGeneral.Blocks (Fintype.card F) (S : Set E) ↔ ¬ OnSphere F S :=
  (CuspidalGeneral.blocks_iff (by have := Fintype.one_lt_card (α:=F); omega) _).trans
    (hits_iff_no_sphere F S small)

/-- Any two points of an extension of degree at least two lie on a norm sphere. -/
theorem pair_on_sphere (hd : 2 ≤ finrank F E) (S : Finset E) (hs : S.card ≤ 2) :
    OnSphere F S := by
  classical
  by_cases h : S.card ≤ 1
  · obtain ⟨x,hx⟩ := card_le_one_iff_subset_singleton.mp h
    refine ⟨1-x,1,one_ne_zero,?_⟩
    intro y hy
    have := mem_singleton.mp (hx hy)
    subst y
    simp
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp (by omega : S.card=2)
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  obtain ⟨z,hz⟩ : ∃ z:E, σ z ≠ z := by
    by_contra! fixed
    have ho := relative_order σ hσ
    rw [show σ=1 from AlgEquiv.ext fixed,orderOf_one] at ho
    omega
  have z0 : z≠0 := by rintro rfl; simp at hz
  let w := σ z / z
  have wne : w≠1 := fun eq => hz ((div_eq_one_iff_eq z0).mp eq)
  have nzNorm : Algebra.norm F z ≠ 0 := by simpa [Algebra.norm_eq_zero_iff] using z0
  have norm1 : Algebra.norm F w=1 := by
    apply mul_right_cancel₀ nzNorm
    rw [← map_mul,show w*z=σ z from div_mul_cancel₀ _ z0,Algebra.norm_eq_of_algEquiv,one_mul]
  let v := (y-x)/(w-1)
  have vn : v≠0 := div_ne_zero (sub_ne_zero.mpr hxy.symm) (sub_ne_zero.mpr wne)
  have relation : v-x+y = w*v := by
    have eq : v*(w-1)=y-x := div_mul_cancel₀ _ (sub_ne_zero.mpr wne)
    linear_combination -eq
  refine ⟨v-x,Algebra.norm F v,(Algebra.norm_eq_zero_iff).not.mpr vn,?_⟩
  intro α hα
  simp only [mem_insert,mem_singleton] at hα
  rcases hα with rfl|rfl
  · simp
  · rw [relation,map_mul,norm1,one_mul]

/-- Restriction to a ground-field line has norm polynomial of exact degree n.
Any n+1 distinct scalar parameters therefore block the projective cusp. -/
theorem ground_line_blocks (T : Finset F) (ht : finrank F E < T.card) :
    open Classical in
    CuspidalGeneral.Blocks (Fintype.card F) (T.image (algebraMap F E) : Set E) := by
  classical
  apply (CuspidalGeneral.blocks_iff (by have := Fintype.one_lt_card (α:=F); omega) _).2
  apply hits_of_no_sphere F
  rintro ⟨b,R,_,same⟩
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  have per : σ^(finrank F E)=1 := (relative_order σ hσ) ▸ pow_orderOf_eq_one σ
  obtain ⟨P,_,deg,ev⟩ := PiecewiseNormSlice.norm_polynomial σ hσ per b 1 one_ne_zero
  let Q := P-C R
  have dq : Q.natDegree=finrank F E := natDegree_sub_C.trans deg
  have rankPos : 0 < finrank F E := finrank_pos
  have ne : Q≠0 := fun eq => rankPos.ne' (by simpa [eq] using dq.symm)
  have inc : T.val ⊆ Q.roots := by
    intro t ht'
    apply (mem_roots ne).2
    change Q.eval t=0
    rw [show Q=P-C R from rfl, eval_sub,eval_C,sub_eq_zero]
    apply (algebraMap F E).injective
    rw [ev,mul_one,← norm_eq_power, same (algebraMap F E t) (mem_image_of_mem _ ht')]
  have bound := Polynomial.card_le_degree_of_subset_roots inc
  omega

theorem upper_attained (room : finrank F E + 1 ≤ Fintype.card F) :
    ∃ S : Finset E, S.card=finrank F E+1 ∧ CuspidalGeneral.Blocks (Fintype.card F) (S : Set E) := by
  classical
  obtain ⟨T,_,ht⟩ := (le_card_iff_exists_subset_card (s:=(univ : Finset F))).1
    (by simpa only [card_univ] using room)
  refine ⟨T.image (algebraMap F E),?_,ground_line_blocks F T (by omega)⟩
  rw [card_image_of_injective _ (algebraMap F E).injective,ht]

theorem quadratic_cusp_minimum (dim : finrank F E=2) :
    IsMinimum (Fintype.card F) 3 E := by
  by_cases room : 3 ≤ Fintype.card F
  swap
  · have two : Fintype.card F=2 := by
      have := Fintype.one_lt_card (α:=F)
      omega
    have graph := CuspidalGeneral.relative_graph_minimum (E:=E) F
    simpa [IsMinimum,two,dim,CuspidalGeneral.degree_two_iff_graph] using graph
  obtain ⟨S,sz,hit⟩ := upper_attained F (E:=E) (by omega)
  refine ⟨⟨S,by omega,hit⟩,?_⟩
  rintro j ⟨T,rfl,blocks⟩
  by_contra! h
  apply ((blocks_iff_no_sphere F T (by omega)).mp blocks)
  exact pair_on_sphere F (by omega) T (by omega)

/-- Every three shifts lie on a common norm sphere, while four chosen on the
ground-field line form an optimal blocking family. -/
theorem cubic_cusp_minimum (dim : finrank F E=3) (room : 4 ≤ Fintype.card F) :
    IsMinimum (Fintype.card F) 4 E := by
  obtain ⟨S,sz,hit⟩ := upper_attained F (E:=E) (by omega)
  refine ⟨⟨S,by omega,hit⟩,?_⟩
  rintro j ⟨T,rfl,blocks⟩
  by_contra! h
  exact (blocks_iff_no_sphere F T (by omega)).mp blocks
    (CuspidalCubicSphere.sphere_through_three dim T (by omega))

private theorem graph_minimum :
    AsgarliGhiocaYip.isPencilMinimum E (Fintype.card F)
      ((Fintype.card F-1)*finrank F E+1) := by
  have hd : 2 ≤ Fintype.card F := Fintype.one_lt_card
  apply (AGY_minimum_iff hd _).2
  exact CuspidalGeneral.relative_graph_minimum F

/-- Comparison of the two projective pencils over the same quadratic extension. -/
theorem quadratic_comparison (dim : finrank F E=2) :
    IsMinimum (Fintype.card F) 3 E ∧
      AsgarliGhiocaYip.isPencilMinimum E (Fintype.card F) (2*Fintype.card F-1) := by
  refine ⟨quadratic_cusp_minimum F dim,?_⟩
  have h := graph_minimum F (E:=E)
  rw [dim] at h
  convert h using 1
  have := Fintype.one_lt_card (α:=F)
  omega

/-- Comparison of the two projective pencils over the same cubic extension. -/
theorem cubic_comparison (dim : finrank F E=3) (room : 4 ≤ Fintype.card F) :
    IsMinimum (Fintype.card F) 4 E ∧
      AsgarliGhiocaYip.isPencilMinimum E (Fintype.card F) (3*Fintype.card F-2) := by
  refine ⟨cubic_cusp_minimum F dim room,?_⟩
  have h := graph_minimum F (E:=E)
  rw [dim] at h
  convert h using 1
  omega

end BlockingCurves.CuspidalNorm
