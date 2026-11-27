import PiecewisePolynomials
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Split geometric fibres for the actual common-variable candidate polynomials. -/
namespace BlockingCurves.PiecewiseGeometric

open Finset Polynomial PiecewiseLargeEscape PiecewiseFibres PhaseCommonVariable
open scoped BigOperators

variable {F H : Type*} [Field F] [Fintype F] [Field H] [Algebra F H] [IsAlgClosed H]

/-- The eigenspace with any prescribed nonzero scalar has an explicit
ground-field coordinate. This is over the algebraic closure, even when
the corresponding rational branch is invertible. -/
private theorem eigen_line (σ : H ≃ₐ[F] H) (hσ : ∀ x, σ x = x^Fintype.card F)
    (a : H) (ha : a ≠ 0) (z : F) (hz : z ≠ 0) :
    ∃ v : H, v ≠ 0 ∧ normalized σ a v = z⁻¹ • v ∧
      ∀ x : H, normalized σ a x = z⁻¹ • x → ∃ k : F, k • v = x := by
  let s := Fintype.card F
  have hs : 1 < s := Fintype.one_lt_card
  let d := a * algebraMap F H z⁻¹
  have hd : d ≠ 0 := mul_ne_zero ha ((_root_.map_ne_zero _).mpr (inv_ne_zero hz))
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq d (show 0<s-1 by omega)
  have vn : v ≠ 0 := by
    intro he
    rw [he,zero_pow (by omega : s-1 ≠ 0)] at hv
    exact hd hv.symm
  have vp : v^s = d*v := by
    simp only [← hv,← pow_succ,Nat.sub_add_cancel hs.le]
  have eq (x : H) : normalized σ a x = z⁻¹ • x ↔ x^s = d*x := by
    change a⁻¹ * σ x = _ ↔ _
    rw [hσ,Algebra.smul_def]
    dsimp only [d,s]
    constructor <;> intro h <;> field_simp [ha] at h ⊢ <;> linear_combination h
  refine ⟨v,vn,(eq v).2 vp,?_⟩
  intro x hx
  have ratio : (x/v)^Fintype.card F = x/v := by
    rw [div_pow,(eq x).1 hx,vp,mul_div_mul_left x v hd]
  obtain ⟨k,hk⟩ := (pow_card_eq_iff_scalar F H (x/v)).1 ratio
  refine ⟨k,?_⟩
  rwa [Algebra.smul_def,← eq_div_iff vn]

private theorem product_surjective [DecidableEq F] (σ : H ≃ₐ[F] H)
    (hσ : ∀ x, σ x = x^Fintype.card F) (a : H) (Cfs : Finset F) :
    Function.Surjective (productEnd (normalized σ a) Cfs) := by
  intro y
  let G := listPoly a Cfs.toList - C y
  have nd : G.degree ≠ 0 := by
    intro he
    have hz := derivative_of_natDegree_zero (show G.natDegree = 0 from natDegree_eq_of_degree_eq_some he)
    change derivative G = 0 at hz
    simp [G,derivative_sub,listPoly_derivative] at hz
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_root G nd
  change (listPoly a Cfs.toList - C y).eval t = 0 at ht
  rw [Polynomial.eval_sub,Polynomial.eval_C,sub_eq_zero] at ht
  have eq := listPoly_eval₂ (F:=F) (RingHom.id H) (fun _ => rfl) σ hσ a
    Cfs.toList Cfs.nodup_toList t
  simp only [Finset.toList_toFinset] at eq
  exact ⟨t,eq.symm.trans ht⟩

variable {E : Type*} [Field E] [Fintype E] [Algebra F E] [DecidableEq F]

/-- Each shift has a full box over the algebraic closure. A candidate has
one coordinate hyperplane of simple roots in its own box and none in the
other boxes. The index retains all rational preimages. -/
private theorem chart_over_closed (ι : E →+* H) (compat : ∀ c : F, ι (algebraMap F E c) = algebraMap F H c) (Cfs : Finset F) (nonzero : ∀ c ∈ Cfs, c ≠ 0)
    (a : E) (ha : a ≠ 0) (S : Finset E) :
    ∃ (point : S → (Cfs → F) → H) (coord : Candidate Cfs a S → F),
    ∀ α v j, ((PiecewiseLargeEscape.candidatePolynomial Cfs a S j).map ι).IsRoot
      (point α v) ↔ j.1=α ∧ v j.2.1 = coord j := by
  classical
  obtain ⟨σ,hσ⟩ := closed_frobenius F H
  let T := normalized σ (ι a)
  have ha' : ι a ≠ 0 := (_root_.map_ne_zero _).mpr ha
  choose w wne weigen span using fun c : Cfs =>
    eigen_line σ hσ (ι a) ha' c.val (nonzero _ c.property)
  choose t ht using fun α : S =>
    product_surjective σ hσ (ι a) Cfs (-(ι α.val)/(ι a))
  have base (α : S) : ι a*productEnd T Cfs (t α) = -(ι α.val) := by
    rw [ht]
    field_simp
    ring
  let piece (v : Cfs → F) (c : F) : H :=
    if hc : c ∈ Cfs then v ⟨c,hc⟩ • w ⟨c,hc⟩ else 0
  have eig (v : Cfs → F) (c : F) (hc : c ∈ Cfs) :
      T (piece v c) = c⁻¹ • piece v c := by
    simp only [piece,dif_pos hc,LinearMap.map_smul, T,weigen ⟨c,hc⟩]
    exact smul_comm ..
  let point (α : S) (v : Cfs → F) := t α + ∑ c ∈ Cfs, piece v c
  have fibre (α : S) (v : Cfs → F) : ι a*productEnd T Cfs (point α v) = -(ι α.val) := by
    have hk := (ker_productEnd_iff T Cfs nonzero _).2 ⟨piece v,eig v,rfl⟩
    dsimp only [point]
    rw [map_add,hk,add_zero,base]
  let offset (j : Candidate Cfs a S) := productEnd T (Cfs.erase j.2.1.val) (t j.1) + ι j.2.2.val
  have bj (j : Candidate Cfs a S) :
      algebraMap F H j.2.1.val*σ (ι j.2.2.val)-ι a*ι j.2.2.val = ι j.1.val := by
    have eq := congrArg ι j.2.2.property
    simpa only [branch,map_sub,map_mul,map_pow,compat,hσ] using eq
  have killed (j : Candidate Cfs a S) : T (offset j) = j.2.1.val⁻¹ • offset j := by
    have eq := (candidate_iff σ ha' Cfs j.2.1.property (t j.1) (ι j.1.val) (offset j)).2
      ⟨ι j.2.2.val,bj j,rfl⟩
    rw [base,neg_add_self] at eq
    have eq' := sub_eq_zero.mp eq
    have cn := (_root_.map_ne_zero (algebraMap F H)).mpr (nonzero _ j.2.1.property)
    change (ι a)⁻¹ * σ (offset j) = _
    rw [Algebra.smul_def,map_inv₀]
    field_simp [ha',cn]
    linear_combination eq'
  let weight (j : Candidate Cfs a S) := ∏ c ∈ Cfs.erase j.2.1.val, (c*j.2.1.val⁻¹-1)
  let y (j : Candidate Cfs a S) := (weight j)⁻¹ • (-(offset j))
  have yEigen (j : Candidate Cfs a S) : T (y j) = j.2.1.val⁻¹ • y j := by
    simp only [y,LinearMap.map_smul,map_neg,killed,smul_neg]
    rw [smul_comm]
  choose coord hcoord using fun j : Candidate Cfs a S => span j.2.1 (y j) (yEigen j)
  have val (j : Candidate Cfs a S) (x : H) :
      ((candidatePolynomial Cfs a S j).map ι).IsRoot x ↔
      productEnd T (Cfs.erase j.2.1.val) x + ι j.2.2.val = 0 := by
    rw [Polynomial.IsRoot.def,Polynomial.eval_map,PiecewiseLargeEscape.candidatePolynomial,
      Polynomial.eval₂_add,Polynomial.eval₂_C,listPoly_eval₂ ι compat σ hσ _ _ (Finset.nodup_toList _) _,
      Finset.toList_toFinset]
  refine ⟨point,coord,fun α v j => ?_⟩
  rw [val]
  have rootAt : productEnd T (Cfs.erase j.2.1.val) (point j.1 v) + ι j.2.2.val = 0 ↔
      v j.2.1 = coord j := by
    have eq := (candidate_on_eigen_box T Cfs j.2.1.property nonzero (t j.1) (ι j.2.2.val) (piece v) (eig v)).2
    change _ ↔ piece v j.2.1.val = y j at eq
    rw [eq,← hcoord]
    simp only [piece,dif_pos j.2.1.property,Algebra.smul_def]
    exact (mul_left_inj' (wne _)).trans (algebraMap F H).injective.eq_iff
  constructor
  · intro hr
    have same := root_determines_shift σ ha' Cfs j.2.1.property (bj j) hr
    rw [fibre] at same
    have he : j.1=α := Subtype.ext (ι.injective (neg_inj.mp same).symm)
    exact ⟨he,rootAt.mp (he.symm ▸ hr)⟩
  · rintro ⟨rfl,h⟩
    exact rootAt.mpr h

theorem exists_geometric_chart (Cfs : Finset F) (nonzero : ∀ c ∈ Cfs, c ≠ 0)
    (a : E) (ha : a ≠ 0) (S : Finset E) :
    ∃ (point : S → (Cfs → F) → AlgebraicClosure E) (coord : Candidate Cfs a S → F),
    ∀ α v j, ((PiecewiseLargeEscape.candidatePolynomial Cfs a S j).map (algebraMap E (AlgebraicClosure E))).IsRoot
      (point α v) ↔ j.1=α ∧ v j.2.1 = coord j := by
  let ι := algebraMap E (AlgebraicClosure E)
  letI : Algebra F (AlgebraicClosure E) := (ι.comp (algebraMap F E)).toAlgebra
  exact chart_over_closed (F:=F) ι (fun _ => rfl) Cfs nonzero a ha S

end BlockingCurves.PiecewiseGeometric
