import CuspidalGeneral
import PiecewiseFrobenius

namespace BlockingCurves.CuspidalGeneral

open Finset Polynomial

variable {F : Type*} [Field F] [Fintype F]
attribute [local instance] Classical.propDecidable

/-- The polynomial defining any slope and translate has at most d roots,
even when its derivative vanishes identically at the horizontal slope. -/
theorem fibre_card {d : ℕ} (hd : 2 ≤ d) (m b y : F) :
    (univ.filter (fun t : F => t^d-m*t^(d-1)-b=y)).card ≤ d := by
  classical
  let A : F[X] := C m*X^(d-1)+C (b+y)
  let P : F[X] := X^d-A
  have degreeA : A.natDegree ≤ d-1 := by
    apply natDegree_add_le_of_degree_le
    · simpa using natDegree_C_mul_le m ((X:F[X])^(d-1))
    · simp
  have degreeP : P.natDegree=d := by
    rw [show P=X^d-A from rfl,natDegree_sub_eq_left_of_natDegree_lt,natDegree_X_pow]
    rw [natDegree_X_pow]
    omega
  have hP : P≠0 := by
    intro h
    simp [h] at degreeP
    omega
  apply le_trans _ degreeP.le
  apply Polynomial.card_le_degree_of_subset_roots
  intro t ht
  have h := (mem_filter.mp (show t ∈ univ.filter (fun t : F => t^d-m*t^(d-1)-b=y) from ht)).2
  apply (Polynomial.mem_roots hP).2
  simp only [P,A,Polynomial.IsRoot,eval_sub,eval_pow,eval_X,eval_add,eval_mul,eval_C]
  linear_combination h

/-- Uniform over all finite fields, including both sorts of bad characteristic. -/
theorem logarithmic_upper {d : ℕ} (hd : 2 ≤ d) :
    ∃ S : Finset F, Blocks d (S:Set F) ∧
      (S.card:ℝ) ≤ 2*d*Real.log (2*Fintype.card F)+1 := by
  classical
  let row (l : F×F) := univ.image (fun t : F => t^d-l.1*t^(d-1)-l.2)
  have share (l : F×F) : Fintype.card F ≤ d*(row l).card := by
    simpa only [card_univ] using card_le_mul_card_image
      (f:=fun t : F => t^d-l.1*t^(d-1)-l.2) univ d (fun y _ => fibre_card hd l.1 l.2 y)
  obtain ⟨S,all,size⟩ := PiecewiseFrobenius.rows_upper_of_share (by omega : 0<d) row share
  refine ⟨S,(blocks_iff hd _).2 ?_,size⟩
  intro m b
  obtain ⟨α,hS,hrow⟩ := all (m,b)
  obtain ⟨t,_,ht⟩ := mem_image.mp hrow
  exact ⟨t,ht ▸ hS⟩

end BlockingCurves.CuspidalGeneral
