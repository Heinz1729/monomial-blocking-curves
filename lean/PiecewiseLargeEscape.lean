import PiecewisePolynomials
import PiecewiseGeometric
import PiecewiseCharacter
import PiecewiseWeil

/-! Univariate Weil estimates for the actual rational preimage indices,
with the exceptional branch retained and target labels constructed from the table. -/
namespace BlockingCurves.PiecewiseLargeEscape

open Polynomial Finset PiecewiseFibres PhaseCommonVariable
open scoped BigOperators

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
variable [DecidableEq F] [DecidableEq E]

/-- On its geometric fibre distinct candidates in the same branch differ
only in their constant terms. All coordinates away from the exceptional
branch have at most one prescribed value and hence a hole. -/
theorem not_power_from_chart {m : ℕ}
    (Cfs : Finset F) (nonempty : Cfs.Nonempty) (a : Eˣ) (S : Finset E)
    (choice : (∀ c ∈ Cfs, Function.Injective (branch (a:E) c)) ∨
      (Fintype.card F = m+1 ∧ ∃ d ∈ Cfs, ¬Function.Injective (branch (a:E) d) ∧
        ∀ c ∈ Cfs, c ≠ d → Function.Injective (branch (a:E) c)))
    (point : S → (Cfs → F) → AlgebraicClosure E)
    (coord : Candidate Cfs (a:E) S → F)
    (roots : ∀ α v j, ((candidatePolynomial Cfs (a:E) S j).map
      (algebraMap E (AlgebraicClosure E))).IsRoot (point α v) ↔ j.1=α ∧ v j.2.1=coord j)
    (e : Candidate Cfs (a:E) S → Fin m) (active : ∃ j, (e j:ℕ) ≠ 0)
    (g : (AlgebraicClosure E)[X]) :
    (∏ j, (candidatePolynomial Cfs (a:E) S j)^(e j:ℕ)).map
        (algebraMap E (AlgebraicClosure E)) ≠ g^m := by
  classical
  let ι := algebraMap E (AlgebraicClosure E)
  let p (j : Candidate Cfs (a:E) S) := (candidatePolynomial Cfs (a:E) S j).map ι
  have d : ∃ d : Cfs, ∀ c : Cfs, c ≠ d → Function.Injective (branch (a:E) c.val) := by
    rcases choice with all | ⟨_,d,hd,_,other⟩
    · obtain ⟨d,hd⟩ := nonempty
      exact ⟨⟨d,hd⟩,fun c _ => all c.val c.property⟩
    · exact ⟨⟨d,hd⟩,fun c h => other c.val c.property (fun he => h (Subtype.ext he))⟩
  obtain ⟨d,other⟩ := d
  have row {j k : Candidate Cfs (a:E) S} (hα : j.1=k.1) (hc : j.2.1=k.2.1)
      (hcoord : coord j=coord k) : j=k := by
    let v := fun _ : Cfs => coord j
    let t := point j.1 v
    have rj : (p j).IsRoot t := (roots j.1 v j).2 ⟨rfl,rfl⟩
    have rk : (p k).IsRoot t := (roots j.1 v k).2 ⟨hα.symm,hcoord⟩
    have first (i : Candidate Cfs (a:E) S) :
        (p i).eval t = ((listPoly (a:E) (Cfs.erase i.2.1.val).toList).map ι).eval t + ι i.2.2.val := by
      simp [p,candidatePolynomial]
    change (p j).eval t=0 at rj
    change (p k).eval t=0 at rk
    have he := congrArg (fun c : Cfs => ((listPoly (a:E) (Cfs.erase c.val).toList).map ι).eval t) hc
    dsimp only at he
    rw [first, he] at rj
    rw [first] at rk
    have hu : j.2.2.val = k.2.2.val := ι.injective (add_left_cancel (rj.trans rk.symm))
    obtain ⟨α,c,u⟩ := j
    obtain ⟨β,b,w⟩ := k
    dsimp only at hα hc hu
    subst β; subst b
    congr 2
    exact Subtype.ext hu
  have unused (α : S) (c : Cfs) (ne : c ≠ d) :
      ∃ u : F, ∀ j : Candidate Cfs (a:E) S, j.1=α → j.2.1=c → coord j ≠ u := by
    by_cases ex : ∃ j : Candidate Cfs (a:E) S, j.1=α ∧ j.2.1=c
    · obtain ⟨⟨β,b,w⟩,rfl,rfl⟩ := ex
      let k : Candidate Cfs (a:E) S := ⟨β,b,w⟩
      refine ⟨coord k + 1,?_⟩
      rintro ⟨γ,z,u⟩ heα hec
      change γ=β at heα
      change z=b at hec
      subst γ; subst z
      have eu : u=w := Subtype.ext (other b ne (u.2.trans w.2.symm))
      subst u
      exact fun h => (one_ne_zero : (1:F) ≠ 0) (add_right_eq_self.mp h.symm)
    · exact ⟨0,fun j hα hc => (ex ⟨j,hα,hc⟩).elim⟩
  have sep (j) : (p j).Separable := (candidate_separable Cfs (a:E) S j).map
  have res := PhaseCharacter.not_power_of_coordinate_roots p sep (fun j => j.1)
    (fun j => j.2.1) coord (fun _ _ hα hc hl => row hα hc hl) point roots
    (fun _ => d) unused (fun j => (e j : ℕ)) (fun j => (e j).isLt) active g
  simpa only [Polynomial.map_prod,Polynomial.map_pow,p,ι] using res

/-- Use an actual power-label character and a wrong label for every distinct
coefficient. Its target is chosen from an existing nonzero class, and equality
of characters is equivalent to equality of algebraic power labels. -/
theorem large_escape_at_slope {m n : ℕ} (hm : 2 ≤ m) (large : 4*m ≤ n)
    (size : Fintype.card E = Fintype.card F^n) (dvd : m ∣ Fintype.card E-1)
    (table : E → F) (Cfs : Finset F)
    (labels : ∀ u : Eˣ, table ((u:E)^((Fintype.card E-1)/m)) ∈ Cfs)
    (two : ∃ u v : Eˣ, table ((u:E)^((Fintype.card E-1)/m)) ≠ table ((v:E)^((Fintype.card E-1)/m)))
    (nonzero : ∀ c ∈ Cfs, c ≠ 0) (few : Cfs.card ≤ m) (a : Eˣ)
    (choice : (∀ c ∈ Cfs, Function.Injective (branch (a:E) c)) ∨
      (Fintype.card F = m+1 ∧ ∃ d ∈ Cfs, ¬Function.Injective (branch (a:E) d) ∧
        ∀ c ∈ Cfs, c ≠ d → Function.Injective (branch (a:E) c)))
    (S : Finset E)
    (indep : ∀ e : Candidate Cfs (a:E) S → Fin m, (∃ j, (e j:ℕ) ≠ 0) →
      ∀ g : (AlgebraicClosure E)[X], (∏ j, (candidatePolynomial Cfs (a:E) S j)^(e j:ℕ)).map
        (algebraMap E (AlgebraicClosure E)) ≠ g^m)
    (weil : ∀ χ : MulChar E ℂ, orderOf χ = m → PiecewiseWeil.PolynomialWeilBound m χ)
    (threshold : 16384*(m:ℝ)^5 ≤ Real.log (Fintype.card E))
    (budget : (S.card:ℝ)*(32*(m:ℝ)^2*Real.log m) ≤ Real.log (Fintype.card E)) :
    ¬ GraphHits (fun x : E => algebraMap F E (table (x^((Fintype.card E-1)/m))) * x^Fintype.card F) (S:Set E) := by
  classical
  let k := (Fintype.card E-1)/m
  obtain ⟨u,v,uv⟩ := two
  let sel (c : F) : Eˣ := if table ((u:E)^k) = c then v else u
  have avoid (c:F) : table (((sel c):E)^k) ≠ c := by
    dsimp only [sel]
    split_ifs with h
    · exact fun he => uv (h.trans he.symm)
    · exact h
  obtain ⟨χ,order,lab⟩ := PiecewiseCharacter.exists_power_label_character (E:=E) (by omega : 0<m) dvd
  let P := candidatePolynomial Cfs (a:E) S
  let J := Candidate Cfs (a:E) S
  let target (j:J) := χ (sel j.2.1.val : E)
  have χm : χ^m = 1 := order ▸ pow_orderOf_eq_one χ
  have ht (j:J) : (target j)^m=1 := by
    dsimp only [target]
    rw [← χ.pow_apply' (by omega : m≠0),χm,MulChar.one_apply (sel j.2.1.val).isUnit]
  letI : NeZero m := ⟨by omega⟩
  have rb : Fintype.card J ≤ 2*m*S.card := by
    simpa only [Nat.card_eq_fintype_card] using budget_at_slope (by omega : 0<n) size Cfs nonzero few a choice S
  have ds := PiecewiseWeil.extension_degree_scale (Fintype.card_pos (α:=F))
    (show 4*(Cfs.card-1) ≤ n by omega)
  rw [← size] at ds
  have hw := PiecewiseWeil.logarithmic_polynomial_witness hm χ χm P
    (fun j => (candidate_separable Cfs (a:E) S j).ne_zero) (candidate_degree Cfs (a:E) S) target ht
    (fun e ne => indep e (by
      by_contra none
      apply ne
      funext j
      apply Fin.ext
      exact not_not.mp (fun neq => none ⟨j,neq⟩))) (weil χ order) threshold budget (Or.inl ⟨rb,rfl⟩) ds
  obtain ⟨t,good⟩ := hw
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let label (x:E) : Eˣ := if hx : x=0 then 1 else Units.mk0 x hx
  let β (w:Eˣ) := table ((w:E)^k)
  have miss := PiecewiseCandidates.wrong_classes_miss σ label β Cfs labels a.ne_zero t (S:Set E)
  have excluded : ¬GraphHits (fun x => algebraMap F E (β (label x))*σ x) (S:Set E) := by
    apply miss
    intro z hz α hα w hw
    have wrow : branch (a:E) z w = α := by simpa only [branch,hσ] using hw
    let j : J := ⟨⟨α,hα⟩,⟨z,hz⟩,⟨w,wrow⟩⟩
    have ee := candidate_evaluation Cfs (a:E) S j σ hσ t
    have hj := good j
    change (P j).eval t = productEnd (normalized σ (a:E)) (Cfs.erase z) t + w at ee
    rw [ee] at hj
    let x := productEnd (normalized σ (a:E)) (Cfs.erase z) t + w
    have xe : x^k = (sel z:E)^k := (lab _ _).mp hj.2
    refine ⟨hj.1,?_⟩
    change table (((label x):E)^k) ≠ z
    have lx : (label x:E) = x := by simp [label,hj.1, x]
    rw [lx,xe]
    exact avoid z
  convert excluded using 2
  funext x
  rw [hσ]
  by_cases hx : x=0
  · simp [hx,zero_pow Fintype.card_pos.ne']
  · simp [β,label,hx,k]

/-- Section 7 in the large-extension regime. The only analytic input is the
usual one-variable multiplicative Weil inequality over E. Branch geometry,
the full singular fibre, repeated coefficients, and both logarithmic constants
are accounted for in the proof. -/
theorem large_table_escape {m n : ℕ} (hm : 2 ≤ m) (large : 4*m ≤ n)
    (divides : m ∣ Fintype.card F-1) (size : Fintype.card E = Fintype.card F^n)
    (table : E → F)
    (nonzero : ∀ x : Eˣ, table ((x:E)^((Fintype.card E-1)/m)) ≠ 0)
    (two : ∃ u v : Eˣ, table ((u:E)^((Fintype.card E-1)/m)) ≠ table ((v:E)^((Fintype.card E-1)/m)))
    (S : Finset E) (threshold : 16384*(m:ℝ)^5 ≤ Real.log (Fintype.card E))
    (budget : (S.card:ℝ)*(32*(m:ℝ)^2*Real.log m) ≤ Real.log (Fintype.card E))
    (weil : ∀ χ : MulChar E ℂ, orderOf χ=m → PiecewiseWeil.PolynomialWeilBound m χ) :
    ¬ GraphHits (fun x : E => algebraMap F E (table (x^((Fintype.card E-1)/m))) * x^Fintype.card F) (S:Set E) := by
  classical
  let Cfs := coefficients table m
  let D := NormPencil.normExponent (Fintype.card F) n
  have hs : 1 < Fintype.card F := Fintype.one_lt_card
  have mult := NormPencil.normExponent_mul (Fintype.card F) n hs.le
  have hD : (Fintype.card F-1)*D = Fintype.card E-1 := by rw [size, ← mult, Nat.add_sub_cancel, mul_comm]
  have dvd : m ∣ Fintype.card E-1 := hD ▸ dvd_mul_of_dvd_left divides D
  have few : Cfs.card ≤ m := coefficients_card (by omega) dvd table
  have members := mem_coefficients table m
  have nz (c:F) (hc : c ∈ Cfs) : c ≠ 0 := by
    obtain ⟨u,_,rfl⟩ := mem_image.mp (show c ∈ coefficients table m from hc)
    exact nonzero u
  obtain ⟨a,choice⟩ := good_slope (by omega : 0<n) size Cfs nz few
    (Nat.le_of_dvd (Nat.sub_pos_of_lt hs) divides)
  obtain ⟨point,coord,roots⟩ := PiecewiseGeometric.exists_geometric_chart Cfs nz (a:E) a.ne_zero S
  apply large_escape_at_slope hm large size dvd table Cfs members two nz few a choice S
    (fun e active g => not_power_from_chart Cfs ⟨_,members 1⟩ a S choice point coord roots e active g) weil threshold budget

end BlockingCurves.PiecewiseLargeEscape
