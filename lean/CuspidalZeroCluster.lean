import CuspidalRootInertia

/-! Reduction of all roots in the valuation ring of a splitting field.
A repeated residue root is counted with multiplicity. No tameness or
invertibility of the ramification index is used. -/

namespace BlockingCurves.CuspidalGeneral

open Polynomial

variable {L : Type*} [Field L]

/-- A monic polynomial over a valuation subring has exactly the same roots,
including multiplicities, as its image in the ambient field. -/
theorem valuation_roots_map (A : ValuationSubring L) (P : A[X]) (hm : P.Monic) :
    P.roots.map (algebraMap A L) = (P.map (algebraMap A L)).roots := by
  classical
  let f := algebraMap A L
  have inj : Function.Injective f := IsFractionRing.injective A L
  ext x
  by_cases h : ∃ r : A, f r = x
  · obtain ⟨r,rfl⟩ := h
    rw [Multiset.count_map_eq_count' f _ inj, count_roots, count_roots]
    exact eq_rootMultiplicity_map inj r
  · have left : x ∉ P.roots.map f := fun hx =>
      let ⟨r,_,hr⟩ := Multiset.mem_map.mp hx
      h ⟨r,hr⟩
    have right : x ∉ (P.map f).roots := fun hx =>
      h (IsIntegrallyClosed.algebraMap_eq_of_integral (roots_mem_integralClosure hm hx))
    rw [Multiset.count_eq_zero_of_not_mem left,Multiset.count_eq_zero_of_not_mem right]

/-- Even for inseparable reduction, reducing the actual integral roots of
a split monic polynomial gives the full residue-root multiset. -/
theorem valuation_residue_roots (A : ValuationSubring L) (P : A[X]) (hm : P.Monic)
    (split : (P.map (algebraMap A L)).Splits (RingHom.id L)) :
    P.roots.map (LocalRing.residue A) = (P.map (LocalRing.residue A)).roots := by
  classical
  have card := natDegree_eq_card_roots split
  rw [map_id, ← valuation_roots_map A P hm, Multiset.card_map,
    natDegree_map_eq_of_injective (IsFractionRing.injective A L)] at card
  apply Multiset.eq_of_le_of_card_le (map_roots_le (hm.map _).ne_zero)
  rw [Multiset.card_map,←card]
  exact (card_roots' _).trans (natDegree_map_le _ _)

/-- At any place above the zero fibre the sheet residues are 0, occurring
d−1 times, and the slope residue, occurring once. The roots used here are
the actual ambient-field roots by `valuation_roots_map`. -/
theorem zero_place_sheet_residues (A : ValuationSubring L) {d : ℕ} (hd : 2 ≤ d)
    (a b : A) (hb : LocalRing.residue A b=0)
    (split : ((integralFibre d a b).map (algebraMap A L)).Splits (RingHom.id L)) :
    (integralFibre d a b).roots.map (LocalRing.residue A) =
      (d-1) • ({0} : Multiset (LocalRing.ResidueField A)) + {LocalRing.residue A a} := by
  rw [valuation_residue_roots A _ (integralFibre_monic hd a b) split]
  simpa [integralFibre,hb] using zero_fibre_roots hd (LocalRing.residue A a)

/-- The zero-residue cluster has length d−1; the unique other residue
has a single geometric sheet above it. These are counts with multiplicity. -/
theorem zero_place_cluster_counts (A : ValuationSubring L) {d : ℕ} (hd : 2 ≤ d)
    (a b : A) (ha : LocalRing.residue A a≠0) (hb : LocalRing.residue A b=0)
    (split : ((integralFibre d a b).map (algebraMap A L)).Splits (RingHom.id L)) :
    open Classical in
    let roots := (integralFibre d a b).roots
    let ρ := LocalRing.residue A
    Multiset.card (roots.filter (fun t => 0 = ρ t)) = d-1 ∧
      Multiset.card (roots.filter (fun t => ρ a = ρ t)) = 1 := by
  classical
  dsimp only
  have red := zero_place_sheet_residues A hd a b hb split
  constructor
  · rw [←Multiset.count_map (LocalRing.residue A) _ 0,red,Multiset.nsmul_singleton]
    simp [Multiset.count_singleton,Ne.symm ha,ha]
  · rw [←Multiset.count_map (LocalRing.residue A) _ (LocalRing.residue A a),red,Multiset.nsmul_singleton]
    simp [Multiset.count_replicate,ha]

/-- The unique simple sheet of the zero fibre is fixed by every element
of the actual inertia subgroup. Slope and intercept belong to the base field. -/
theorem inertia_fixes_unique_simple_sheet {K : Type*} [Field K] [Algebra K L]
    (A : ValuationSubring L) {d : ℕ} (hd : 2 ≤ d) (a b : A)
    (ha : LocalRing.residue A a≠0) (hb : LocalRing.residue A b=0)
    (abase : ∃ a₀ : K, algebraMap K L a₀ = a)
    (bbase : ∃ b₀ : K, algebraMap K L b₀ = b)
    (split : ((integralFibre d a b).map (algebraMap A L)).Splits (RingHom.id L)) :
    ∃ t ∈ (integralFibre d a b).roots, LocalRing.residue A t=LocalRing.residue A a ∧
      (∀ z ∈ (integralFibre d a b).roots, LocalRing.residue A z=LocalRing.residue A a → z=t) ∧
      ∀ g : A.inertiaSubgroup K, g.val.val (t : L) = t := by
  classical
  let P := integralFibre d a b
  let ρ := LocalRing.residue A
  obtain ⟨t, ht⟩ := Multiset.card_eq_one.mp (zero_place_cluster_counts A hd a b ha hb split).2
  have iff_t (z : A) : z∈P.roots ∧ ρ z=ρ a ↔ z=t := by
    rw [←Multiset.mem_singleton (a:=t) (b:=z), ←ht, Multiset.mem_filter]
    exact and_congr_right (fun _ => eq_comm)
  have ht' := (iff_t t).mpr rfl
  refine ⟨t,ht'.1,ht'.2,fun z hz hs => (iff_t z).mp ⟨hz,hs⟩,?_⟩
  intro g
  have fixbase (z : A) (hz : ∃ c : K, algebraMap K L c=z) : g.val • z=z := by
    obtain ⟨c,hc⟩ := hz
    apply Subtype.ext
    change g.val.val (z : L)=z
    rw [←hc,g.val.val.commutes]
  let σ := MulSemiringAction.toRingAut (A.decompositionSubgroup K) A g.val
  have fxa : σ a=a := fixbase a abase
  have fxb : σ b=b := fixbase b bbase
  have eqn (z : A) : z∈P.roots ↔ z^d-(a*z^(d-1)+b)=0 := by
    rw [mem_roots (integralFibre_monic hd a b).ne_zero,IsRoot.def]
    simp [P,integralFibre]
  have root : σ t ∈ P.roots := by
    apply (eqn _).mpr
    simpa only [map_sub, map_pow, map_add, map_mul, map_zero,fxa,fxb] using
      congrArg σ ((eqn _).mp ht'.1)
  have residue : ρ (σ t)=ρ a := (inertia_residue_eq A g t).trans ht'.2
  exact congrArg Subtype.val ((iff_t (σ t)).mp ⟨root,residue⟩)

section FunctionField

variable {k : Type*} [Field k]

/-- Over the actual joint splitting field each coordinate does split. -/
theorem coordinate_splits_in_compositum {d : ℕ} (hd : 2 ≤ d) (a : k) (S : Finset k)
    {u : k} (hu : u ∈ S) :
    (cuspCoordinate d a u).Splits (algebraMap (RatFunc k) (cuspCompositum d a S)) := by
  classical
  let P := ∏ v ∈ S, cuspCoordinate d a v
  have nz : P≠0 := Finset.prod_ne_zero_iff.mpr fun v _ =>
    (integralFibre_monic hd (RatFunc.C a) (RatFunc.X+RatFunc.C v)).ne_zero
  exact splits_of_splits_of_dvd _ nz (SplittingField.splits P)
    (Finset.dvd_prod_of_mem _ hu)

/-- At any place of the product splitting field above b = -u, there is a
unique sheet reducing to the nonzero slope. Every inertia automorphism fixes
it, including when the other residue fibre is wildly ramified. -/
theorem compositum_inertia_simple_sheet {d : ℕ} (hd : 2 ≤ d) {a : k} (ha : a≠0)
    (S : Finset k) {u : k} (hu : u ∈ S) (A : ValuationSubring (cuspCompositum d a S))
    (place : CuspPlace A u) :
    ∃ t : A, (t : cuspCompositum d a S) ∈ (cuspCoordinate d a u).rootSet (cuspCompositum d a S) ∧
      LocalRing.residue A t=LocalRing.residue A (place.constants a) ∧
      (∀ z : A, (z : cuspCompositum d a S) ∈ (cuspCoordinate d a u).rootSet (cuspCompositum d a S) →
        LocalRing.residue A z=LocalRing.residue A (place.constants a) → z=t) ∧
      ∀ g : A.inertiaSubgroup (RatFunc k), g.val.val (t : cuspCompositum d a S) = t := by
  classical
  let M := cuspCompositum d a S
  let ι := algebraMap (RatFunc k) M
  let b := place.parameter + place.constants u
  let P := integralFibre d (place.constants a) b
  have lb : (b : M) = ι (RatFunc.X + RatFunc.C u) := by
    change (place.parameter : M) + (place.constants u : M) = _
    rw [place.parameter_lift,place.constants_lift,map_add]
  have mapped : P.map (algebraMap A M) = (cuspCoordinate d a u).map ι := by
    simp only [P,integralFibre,cuspCoordinate,lineFibre,Polynomial.map_sub,Polynomial.map_add,
      Polynomial.map_mul,Polynomial.map_pow,map_X,map_C]
    change X^d - (C (place.constants a : M) * X^(d-1) + C (b:M)) = _
    rw [lb,place.constants_lift]
  have hres : LocalRing.residue A b = 0 := by
    simp [b,place.specializes]
  have slope : LocalRing.residue A (place.constants a) ≠ 0 := by
    simpa only [RingHom.comp_apply,map_zero] using ((LocalRing.residue A).comp place.constants).injective.ne ha
  have split := (splits_id_iff_splits ι).mpr (coordinate_splits_in_compositum hd a S hu)
  rw [← mapped] at split
  have eqroots (x : A) :
      x ∈ P.roots ↔ (x:M) ∈ (cuspCoordinate d a u).rootSet M := by
    change _ ↔ (x:M) ∈ ((cuspCoordinate d a u).map ι).roots.toFinset
    rw [Multiset.mem_toFinset,←mapped,←valuation_roots_map A _ (integralFibre_monic hd _ _)]
    constructor
    · exact fun hx => Multiset.mem_map.mpr ⟨x,hx,rfl⟩
    · intro hx
      obtain ⟨z,hz,h⟩ := Multiset.mem_map.mp hx
      exact (Subtype.ext h : z=x) ▸ hz
  obtain ⟨t,ht,hr,unique,fix⟩ := inertia_fixes_unique_simple_sheet (K:=RatFunc k) A hd
    (place.constants a) b slope hres ⟨_,(place.constants_lift _).symm⟩ ⟨_,lb.symm⟩ split
  exact ⟨t,(eqroots _).mp ht,hr,fun z hz => unique z ((eqroots _).mpr hz),fix⟩

end FunctionField

end BlockingCurves.CuspidalGeneral
