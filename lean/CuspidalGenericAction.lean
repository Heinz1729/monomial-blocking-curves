import CuspidalRootInertia
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-! Generic monodromy on one coordinate of the actual joint splitting
field. The rational-function parameter is an independent variable. -/
namespace BlockingCurves.CuspidalGeneral
open Polynomial

variable {k : Type*} [Field k]

private noncomputable def exchange : (k[X])[X] →+* (k[X])[X] :=
  eval₂RingHom (mapRingHom C) (C X)

private theorem exchange_C (p : k[X]) : exchange (C p)=p.map C := eval₂_C _ _
private theorem exchange_X : exchange (X:(k[X])[X])=C X := eval₂_X _ _

private theorem exchange_mapped (p : k[X]) : exchange (p.map C) = C p := by
  have h : exchange.comp (mapRingHom (C : k →+* k[X])) = C := by
    apply Polynomial.ringHom_ext
    · intro a
      change exchange ((C a).map C) = C (C a)
      rw [map_C,exchange_C,map_C]
    · change exchange ((X:k[X]).map C) = C X
      rw [map_X,exchange_X]
  exact RingHom.congr_fun h p

private theorem exchange_twice (p : (k[X])[X]) : exchange (exchange p) = p := by
  have h : (exchange (k:=k)).comp exchange = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a
      change exchange (exchange (C a)) = C a
      rw [exchange_C,exchange_mapped]
    · change exchange (exchange X) = X
      rw [exchange_X,exchange_C,map_X]
  exact RingHom.congr_fun h p

/-- The generic coordinate is irreducible over k(b) in every characteristic.
Interchanging the two variables makes the integral model linear in b. -/
theorem cuspCoordinate_irreducible {d : ℕ} (hd : 2 ≤ d) (a u : k) :
    Irreducible (cuspCoordinate d a u) := by
  let P := integralFibre d (C a) (X+C u)
  let r : k[X] := X^d-C a*X^(d-1)-C u
  have form : exchange P = (X-C r)*(-1) := by
    simp only [P,integralFibre,r,map_pow,map_add,map_mul,map_sub,exchange_X,exchange_C,
      map_C,map_X,Polynomial.map_add,C_sub,C_mul,C_pow]
    ring
  have linear : Irreducible (exchange P) := by
    rw [form,irreducible_mul_isUnit (show IsUnit (-1 : (k[X])[X]) from isUnit_iff_dvd_one.mpr ⟨-1,by ring⟩)]
    exact irreducible_X_sub_C r
  have irr : Irreducible P := by
    constructor
    · exact fun h => linear.not_unit (h.map exchange)
    · intro g h e
      have eqn : exchange P=exchange g*exchange h := by rw [e,map_mul]
      exact (linear.isUnit_or_isUnit eqn).imp
        (fun h => by simpa only [exchange_twice] using h.map exchange)
        (fun h => by simpa only [exchange_twice] using h.map exchange)
  have result := ((integralFibre_monic hd (C a) (X+C u)).irreducible_iff_irreducible_map_fraction_map
    (K:=RatFunc k)).mp irr
  simpa only [P,integralFibre,cuspCoordinate,lineFibre,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_add,map_X,map_C,RatFunc.algebraMap_X,RatFunc.algebraMap_C,
    map_add] using result

/-- Its derivative at the slope is nonzero, including when the
characteristic divides d or d−1. -/
theorem cuspCoordinate_separable {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a≠0) (u : k) :
    (cuspCoordinate d a u).Separable := by
  apply (separable_iff_derivative_ne_zero (cuspCoordinate_irreducible (by omega : 2≤d) a u)).mpr
  intro der
  let a' : RatFunc k := RatFunc.C a
  have nonzero : a'≠0 := (_root_.map_ne_zero RatFunc.C).mpr ha
  have value := congrArg (eval a') der
  change ((X^d-(C a'*X^(d-1)+C (RatFunc.X+RatFunc.C u))): (RatFunc k)[X]).derivative.eval a' =
    (0 : (RatFunc k)[X]).eval a' at value
  simp only [derivative_sub,derivative_add,derivative_C,add_zero,eval_zero] at value
  have crit : ((X^d-C a'*X^(d-1)): (RatFunc k)[X]).derivative.eval a'=0 := by
    simpa only [derivative_sub] using value
  rcases (critical_point_iff hd a' a').mp crit with h|h
  · exact nonzero h
  · have eq := mul_right_cancel₀ nonzero h
    rw [Nat.cast_sub (by omega : 1≤d),Nat.cast_one] at eq
    exact one_ne_zero (by linear_combination eq)

/-- The automorphism group of the joint splitting field acts transitively
on the actual roots of each coordinate polynomial. -/
theorem compositum_coordinate_transitive {d : ℕ} (hd : 2 ≤ d) (a u : k) (S : Finset k)
    (x y : (cuspCoordinate d a u).rootSet (cuspCompositum d a S)) :
    ∃ g : cuspCompositum d a S ≃ₐ[RatFunc k] cuspCompositum d a S,
      g x.val = y.val := by
  let E := cuspCompositum d a S
  have irr := cuspCoordinate_irreducible hd a u
  have hx := (mem_rootSet_of_ne irr.ne_zero).mp x.property
  have hy := (mem_rootSet_of_ne irr.ne_zero).mp y.property
  exact (Normal.minpoly_eq_iff_mem_orbit E).mp
    ((minpoly.eq_of_irreducible irr hy).symm.trans (minpoly.eq_of_irreducible irr hx))

/-- Distinct translated coordinates differ by a nonzero scalar, so their
product is separable even over the imperfect rational function field. -/
theorem cusp_product_separable {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a≠0) (S : Finset k) :
    (∏ u ∈ S, cuspCoordinate d a u).Separable := by
  apply separable_prod' _ (fun u _ => cuspCoordinate_separable hd ha u)
  intro u _ v _ huv
  let c : RatFunc k := RatFunc.C (v-u)
  have cn : c ≠ 0 := (_root_.map_ne_zero RatFunc.C).mpr (sub_ne_zero.mpr huv.symm)
  have diff : cuspCoordinate d a u - cuspCoordinate d a v = C c := by
    simp only [cuspCoordinate,lineFibre,c,map_sub,map_add]
    ring
  refine ⟨C c⁻¹,-C c⁻¹,?_⟩
  calc
    _ = C c⁻¹ * (cuspCoordinate d a u - cuspCoordinate d a v) := by ring
    _ = 1 := by rw [diff,←C_mul,inv_mul_cancel cn,C_1]

theorem cuspCompositum_isGalois {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a≠0) (S : Finset k) :
    IsGalois (RatFunc k) (cuspCompositum d a S) :=
  IsGalois.of_separable_splitting_field (cusp_product_separable hd ha S)

/-- The leading monic term retains its prescribed degree in the function field. -/
theorem cuspCoordinate_natDegree {d : ℕ} (hd : 2 ≤ d) (a u : k) :
    (cuspCoordinate d a u).natDegree=d := by
  unfold cuspCoordinate lineFibre
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow d
  · rw [natDegree_X_pow]
    apply lt_of_le_of_lt (b:=d-1) _ (by omega)
    apply natDegree_add_le_of_degree_le
    · simpa using natDegree_C_mul_le (RatFunc.C a) ((X:(RatFunc k)[X])^(d-1))
    · simp

end BlockingCurves.CuspidalGeneral
