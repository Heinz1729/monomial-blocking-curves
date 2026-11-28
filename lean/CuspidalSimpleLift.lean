import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.Separable

/-! Simple sheets at a finite place lifted in the coefficientwise complete
power series ring. The argument uses no bound on the residue characteristic. -/
namespace BlockingCurves.CuspidalLocal
open Polynomial

variable {K : Type*} [Field K]

private abbrev parameterIdeal (K : Type*) [Field K] :=
  Ideal.span ({PowerSeries.X} : Set (PowerSeries K))

private theorem congr_iff (f g : PowerSeries K) (n : ℕ) :
    f ≡ g [SMOD (parameterIdeal K)^n • (⊤ : Submodule (PowerSeries K) (PowerSeries K))] ↔
    ∀ j, j<n → PowerSeries.coeff K j f = PowerSeries.coeff K j g := by
  rw [SModEq.sub_mem, Algebra.id.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  simp only [map_sub, sub_eq_zero]

private theorem series_complete : IsAdicComplete (parameterIdeal K) (PowerSeries K) where
  haus' := by
    intro f hf
    ext j
    exact (congr_iff _ _ (j+1)).mp (hf (j+1)) j (Nat.lt_succ_self j)
  prec' := by
    intro f cauchy
    refine ⟨PowerSeries.mk (fun j => PowerSeries.coeff K j (f (j+1))),?_⟩
    intro n
    apply (congr_iff _ _ _).mpr
    intro j hj
    rw [PowerSeries.coeff_mk]
    exact ((congr_iff _ _ _).mp (cauchy hj) j (Nat.lt_succ_self j)).symm

/-- Every simple residue root of a monic polynomial lifts to an actual
root in K[[u]], with the specified constant term. -/
theorem lift_simple_sheet (P : (PowerSeries K)[X]) (monic : P.Monic) (r : K)
    (root : (P.map (PowerSeries.constantCoeff K)).eval r = 0)
    (simple : (P.map (PowerSeries.constantCoeff K)).derivative.eval r ≠ 0) :
    ∃ y : PowerSeries K, P.IsRoot y ∧ PowerSeries.constantCoeff K y = r := by
  let I := parameterIdeal K
  letI : IsAdicComplete I (PowerSeries K) := series_complete
  have inI (y : PowerSeries K) : y ∈ I ↔ PowerSeries.constantCoeff K y = 0 :=
    Ideal.mem_span_singleton.trans PowerSeries.X_dvd_iff
  let R := PowerSeries.C K r
  have evaluate (Q : (PowerSeries K)[X]) :
      PowerSeries.constantCoeff K (Q.eval R) = (Q.map (PowerSeries.constantCoeff K)).eval r := by
    have e := eval₂_hom (p:=Q) (PowerSeries.constantCoeff K) R
    simpa [eval_map, R] using e.symm
  have ismax : I.IsMaximal := by
    change (Ideal.span ({PowerSeries.X}:Set (PowerSeries K))).IsMaximal
    rw [←PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  letI : I.IsMaximal := ismax
  letI := Ideal.Quotient.field I
  have unit : IsUnit (Ideal.Quotient.mk I (P.derivative.eval R)) := by
    apply isUnit_iff_ne_zero.mpr
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, inI, evaluate, ←derivative_map]
  obtain ⟨y,hy,hr⟩ := HenselianRing.is_henselian (I:=I) P monic R
    ((inI _).mpr ((evaluate _).trans root)) unit
  exact ⟨y,hy,by simpa [R, sub_eq_zero] using (inI _).mp hr⟩

end BlockingCurves.CuspidalLocal
