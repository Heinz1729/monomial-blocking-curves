import CuspidalGenericAction
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Over

/-! A place above a finite rational intercept in any finite separable
extension of the rational function field. The residue field upstairs may
be larger than the constant field of the base. -/

namespace BlockingCurves.CuspidalGeneral

open Polynomial

variable {k : Type*} [Field k] (M : Type*) [Field M] [Algebra (RatFunc k) M]
  [FiniteDimensional (RatFunc k) M] [IsSeparable (RatFunc k) M]

/-- Lying over the prime of evaluation at -u, followed by the height-one
valuation on the integral closure, supplies the required valuation ring. -/
theorem exists_cuspPlace (u : k) : ∃ A : ValuationSubring M, Nonempty (CuspPlace A u) := by
  classical
  letI : Algebra k[X] M := ((algebraMap (RatFunc k) M).comp (algebraMap k[X] (RatFunc k))).toAlgebra
  letI : IsScalarTower k[X] (RatFunc k) M := IsScalarTower.of_algebraMap_eq' rfl
  let D := integralClosure k[X] M
  letI : IsDedekindDomain D := integralClosure.isDedekindDomain k[X] (RatFunc k) M
  letI : IsFractionRing D M := IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) M D
  let P : Ideal k[X] := RingHom.ker (evalRingHom (-u))
  letI : P.IsPrime := RingHom.ker_isPrime _
  have inject : Function.Injective (algebraMap k[X] D) := by
    intro f g h
    apply (IsFractionRing.injective k[X] (RatFunc k))
    apply (algebraMap (RatFunc k) M).injective
    exact congrArg Subtype.val h
  obtain ⟨Q,hQ,over⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S:=D) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp inject]; exact bot_le)
  let t : k[X] := X + C u
  have ht : t ∈ P := by
    change ((X + C u) : k[X]).eval (-u) = 0
    simp
  have tQ : algebraMap k[X] D t ∈ Q := by
    change t ∈ Q.comap (algebraMap k[X] D)
    rwa [over]
  have tn : t ≠ 0 := by
    change X + C u ≠ 0
    intro h
    have := congrArg (fun f : k[X] => f.coeff 1) h
    simp at this
  have nQ : Q ≠ ⊥ := by
    rintro rfl
    exact tn (inject (by simpa using tQ))
  let w : IsDedekindDomain.HeightOneSpectrum D := ⟨Q,hQ,nQ⟩
  let val := w.valuation (K := M)
  let A := val.valuationSubring
  let embed := (algebraMap D M).codRestrict A (fun z => w.valuation_le_one z)
  let lift := embed.comp (algebraMap k[X] D)
  have lift_eq (f : k[X]) : (lift f : M) =
      algebraMap (RatFunc k) M (algebraMap k[X] (RatFunc k) f) := rfl
  have vanishes : LocalRing.residue A (lift t) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (A.valuation_lt_one_iff (lift t)).mpr
    apply ((Valuation.isEquiv_iff_val_lt_one val A.valuation).mp val.isEquiv_valuation_valuationSubring).mp
    exact (w.valuation_lt_one_iff_dvd _).mpr (Ideal.dvd_span_singleton.mpr tQ)
  refine ⟨A,⟨⟨lift.comp C,?_,lift X,?_,?_⟩⟩⟩
  · intro c
    rw [RingHom.comp_apply,lift_eq,RatFunc.algebraMap_C]
  · exact lift_eq X
  · apply eq_neg_of_add_eq_zero_left
    simpa [t,map_add] using vanishes

/-- The joint splitting field has a place above every specified zero fibre,
also when the ramification there is wild. -/
theorem exists_compositum_place {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0)
    (S : Finset k) (u : k) :
    ∃ A : ValuationSubring (cuspCompositum d a S), Nonempty (CuspPlace A u) := by
  letI := cuspCompositum_isGalois hd ha S
  exact exists_cuspPlace (cuspCompositum d a S) u

/-- For each separated zero branch there exists an actual place in the
compositum whose full inertia acts trivially on the other root sets. -/
theorem exists_supported_inertia_place {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0)
    (S : Finset k) (separated : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      Disjoint ({-u,extraCritical d a-u} : Set k) {-v,extraCritical d a-v})
    {u : k} (hu : u ∈ S) :
    ∃ A : ValuationSubring (cuspCompositum d a S), Nonempty (CuspPlace A u) ∧
      ∀ g : A.inertiaSubgroup (RatFunc k), ∀ v ∈ S, v ≠ u →
      ∀ x ∈ (cuspCoordinate d a v).rootSet (cuspCompositum d a S), g.val.val x = x := by
  obtain ⟨A,⟨place⟩⟩ := exists_compositum_place hd ha S u
  exact ⟨A,⟨place⟩,fun g => compositum_inertia_support hd ha S separated hu A place g⟩

/-- With sufficient room for the finite critical-value avoidance, a single
slope works for every indicated zero fibre in the actual splitting field. -/
theorem exists_slope_supported_inertia [Fintype k] [DecidableEq k] {d : ℕ} (hd : 3 ≤ d) (S : Finset k)
    (room : 1+S.offDiag.card*d < Fintype.card k) :
    ∃ a : k, a ≠ 0 ∧ ∀ u ∈ S, ∃ A : ValuationSubring (cuspCompositum d a S),
      Nonempty (CuspPlace A u) ∧ ∀ g : A.inertiaSubgroup (RatFunc k),
      ∀ v ∈ S, v ≠ u → ∀ x ∈ (cuspCoordinate d a v).rootSet (cuspCompositum d a S),
      g.val.val x = x := by
  classical
  let c := ((d-1:ℕ):k)/(d:k)
  obtain ⟨a,ha,apart⟩ := exists_separating_slope (by omega : 0 < d) S (c^d-c^(d-1)) room
  exact ⟨a,ha,fun _ hu => exists_supported_inertia_place hd ha S apart hu⟩

/-- A slope chosen over the finite field still supports the full inertia
at each zero branch after extending constants, in particular to an
algebraic closure as required for geometric monodromy. -/
theorem exists_geometric_supported_inertia [Fintype k] [DecidableEq k]
    {d : ℕ} (hd : 3 ≤ d) (S : Finset k) (room : 1+S.offDiag.card*d < Fintype.card k) :
    ∃ a : k, a ≠ 0 ∧ ∀ {E : Type*} [Field E] (f : k →+* E),
      let T := S.map ⟨f,f.injective⟩
      ∀ u ∈ T, ∃ A : ValuationSubring (cuspCompositum d (f a) T),
        Nonempty (CuspPlace A u) ∧ ∀ g : A.inertiaSubgroup (RatFunc E),
        ∀ v ∈ T, v ≠ u → ∀ x ∈ (cuspCoordinate d (f a) v).rootSet (cuspCompositum d (f a) T),
        g.val.val x = x := by
  classical
  let c := ((d-1:ℕ):k)/(d:k)
  obtain ⟨a,ha,apart⟩ := exists_separating_slope (by omega : 0 < d) S (c^d-c^(d-1)) room
  refine ⟨a,ha,?_⟩
  intro E inst f
  let T := S.map (⟨f,f.injective⟩ : k ↪ E)
  have sep (u : E) (hu : u ∈ T) (v : E) (hv : v ∈ T) (ne : u ≠ v) :
      Disjoint ({-u,extraCritical d (f a)-u} : Set E) {-v,extraCritical d (f a)-v} := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hv
    have ij : i ≠ j := fun e => ne (congrArg f e)
    have src := Set.disjoint_image_of_injective f.injective (apart i hi j hj ij)
    simpa only [extraCritical,c,Set.image_insert_eq,Set.image_singleton,map_neg,map_sub,
      map_mul,map_pow,map_div₀,map_natCast,Function.Embedding.coeFn_mk] using src
  exact fun _ hu => exists_supported_inertia_place hd ((map_ne_zero f).mpr ha) T sep hu

end BlockingCurves.CuspidalGeneral
