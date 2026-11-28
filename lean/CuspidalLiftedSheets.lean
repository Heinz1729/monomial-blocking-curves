import CuspidalSimpleLift
import CuspidalRootInertia
import Mathlib.RingTheory.LaurentSeries

/-! The separated coordinates of the cuspidal pencil split already in the
Laurent base field. This uses only the residue critical-value test and
simple-sheet lifting; the characteristic can divide either d or d−1. -/
namespace BlockingCurves.CuspidalLocal

open Polynomial CuspidalGeneral

variable {K : Type*} [Field K]

/-- A monic power-series polynomial with split simple residue roots has
all its roots in the base ring, and hence splits in its fraction field. -/
theorem splits_over_laurent_of_simple_reduction (P : (PowerSeries K)[X]) (monic : P.Monic)
    (split : (P.map (PowerSeries.constantCoeff K)).Splits (RingHom.id K))
    (simple : ∀ x : K, (P.map (PowerSeries.constantCoeff K)).eval x=0 →
      (P.map (PowerSeries.constantCoeff K)).derivative.eval x≠0) :
    (P.map (algebraMap (PowerSeries K) (LaurentSeries K))).Splits (RingHom.id _) := by
  classical
  let Q := P.map (PowerSeries.constantCoeff K)
  have qne : Q ≠ 0 := (monic.map _).ne_zero
  have distinct : Q.roots.Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro x
    rw [count_roots]
    by_contra! mult
    obtain ⟨h,eq⟩ := (le_rootMultiplicity_iff qne).mp (show 2 ≤ rootMultiplicity x Q by omega)
    have rt : Q.eval x=0 := by simp [eq]
    exact simple x rt (by change Q.derivative.eval x=0; simp [eq,pow_two,derivative_mul])
  have lift (x : Q.roots.toFinset) : ∃ z : PowerSeries K, P.IsRoot z ∧
      PowerSeries.constantCoeff K z=x.val := by
    have rt : Q.eval x.val=0 := (mem_roots qne).mp (Multiset.mem_toFinset.mp x.property)
    exact lift_simple_sheet P monic x.val rt (simple _ rt)
  choose z root cc using lift
  let toRoots (x : Q.roots.toFinset) : P.roots.toFinset := ⟨z x,
    Multiset.mem_toFinset.mpr ((mem_roots monic.ne_zero).mpr (root x))⟩
  have inj : Function.Injective toRoots := by
    intro x y e
    apply Subtype.ext
    rw [←cc x,←cc y]
    exact congrArg (PowerSeries.constantCoeff K) (congrArg Subtype.val e)
  have bound := Fintype.card_le_of_injective toRoots inj
  simp only [Fintype.card_coe, Multiset.toFinset_card_of_nodup distinct] at bound
  have qr : Q.natDegree = P.natDegree := monic.natDegree_map _
  rw [splits_iff_card_roots.mp split,qr] at bound
  apply splits_iff_card_roots.mpr
  apply le_antisymm (card_roots' _)
  rw [monic.natDegree_map]
  exact (bound.trans (Multiset.toFinset_card_le _)).trans
    (card_roots_le_map_of_injective (p:=P) (IsFractionRing.injective (PowerSeries K) (LaurentSeries K)))

/-- Every coordinate having residue intercept outside the two critical values
splits over K((u)). The chosen uniformizer can have arbitrary higher terms in
the intercept; this applies in particular after b = u (a+u)^(d−1). -/
theorem separated_local_coordinate_splits [IsAlgClosed K] {d : ℕ} (hd : 3 ≤ d) (a : K)
    (ha : a≠0) (b : PowerSeries K) (nonzero : PowerSeries.constantCoeff K b≠0)
    (avoid : let c := ((d-1:ℕ):K)/(d:K)
             PowerSeries.constantCoeff K b ≠ (c^d-c^(d-1))*a^d) :
    ((integralFibre d (PowerSeries.C K a) b).map
      (algebraMap (PowerSeries K) (LaurentSeries K))).Splits (RingHom.id _) := by
  apply splits_over_laurent_of_simple_reduction _ (integralFibre_monic (by omega) _ _)
    (IsAlgClosed.splits _)
  let v := PowerSeries.constantCoeff K b
  have red : (integralFibre d (PowerSeries.C K a) b).map (PowerSeries.constantCoeff K) =
      X^d-(C a*X^(d-1)+C v) := by simp [integralFibre,v]
  rw [red]
  intro x rt crit
  have rt' : x^d-a*x^(d-1)=v := by
    simp only [eval_sub,eval_add,eval_mul,eval_pow,eval_X,eval_C] at rt
    linear_combination rt
  have crit' : ((X^d-C a*X^(d-1)):K[X]).derivative.eval x=0 := by
    simpa only [derivative_sub,derivative_add,derivative_C,add_zero] using crit
  rcases critical_value_cases hd a x ha crit' with h|h
  · exact nonzero (rt'.symm.trans h)
  · exact avoid (rt'.symm.trans h)

end BlockingCurves.CuspidalLocal
