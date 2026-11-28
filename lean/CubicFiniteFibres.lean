import CubicPoleDegree
import Mathlib.RingTheory.Localization.Integer

/-! Every rational fibre of the parameter has at most the extension degree
many rational places. Summing over the projective line makes the type of
rational places finite, independently of any estimate for its point count. -/
namespace BlockingCurves.CubicFiniteFibres
open Finset FiniteDimensional CubicAlteration CubicRepairPlaces CubicPoleFibre Polynomial nonZeroDivisors
variable {F : Type*} [Field F] [Fintype F] {R : Finset (Line F)}

private noncomputable def pol (K : Type*) [Field K] [Algebra (RatFunc F) K] : F[X] →+* K :=
  (algebraMap (RatFunc F) K).comp (algebraMap F[X] (RatFunc F))

private theorem value_pol {K : Type*} [Field K] [Algebra (RatFunc F) K] {p : RationalPlace F K} {a : F}
    (ha : Value p (algebraMap (RatFunc F) K RatFunc.X) a) (f : F[X]) : Value p (pol K f) (f.eval a) := by
  induction f using Polynomial.induction_on' with
  | h_add f g hf hg => simpa only [map_add,eval_add] using hf.add hg
  | h_monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, eval_mul, eval_pow, eval_C, eval_X]
    exact (value_const p c).mul (ha.pow n)

/-- In a polynomial relation of residue selectors all coefficients vanish
at a. Cancelling X−a produces another relation and lowers the degree of
any chosen nonzero coefficient. -/
private theorem relation_zero (K : Type*) [Field K] [Algebra (RatFunc F) K] {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → RationalPlace F K) (a : F) (ha : ∀ i, Value (p i) (algebraMap (RatFunc F) K RatFunc.X) a)
    (s : I → K) (hs : ∀ i j, Value (p j) (s i) (if i = j then 1 else 0))
    (c : I → F[X]) (rel : ∑ i, pol K (c i) * s i = 0) (k : I) : c k = 0 := by
  classical
  by_contra hk
  have dvd (i : I) : X-C a ∣ c i := by
    apply dvd_iff_isRoot.mpr
    have h := value_sum (p := p i) univ (fun j => pol K (c j) * s j)
      (fun j => (c j).eval a * (if j = i then 1 else 0))
      (fun j _ => (value_pol (ha i) (c j)).mul (hs j i))
    rw [rel] at h
    simpa [IsRoot, mul_ite] using h.unique (value_zero (p i))
  choose b hb using dvd
  have hlin := X_sub_C_ne_zero a
  have hmap : pol K (X-C a) ≠ 0 := fun h => hlin
    (((algebraMap (RatFunc F) K).injective.comp
      (IsFractionRing.injective F[X] (RatFunc F))) (h.trans (map_zero (pol K)).symm))
  have rel' : ∑ i, pol K (b i) * s i = 0 := by
    apply (mul_eq_zero.mp (show pol K (X-C a) * (∑ i, pol K (b i) * s i) = 0 from ?_)).resolve_left hmap
    rw [mul_sum]
    convert rel using 1
    apply sum_congr rfl
    intro i _
    rw [hb i, map_mul, mul_assoc]
  have bk : b k ≠ 0 := fun h => hk (by rw [hb k,h,mul_zero])
  have _hlt : (b k).natDegree < (c k).natDegree := by
    rw [hb k, natDegree_mul hlin bk, natDegree_X_sub_C]
    omega
  exact bk (relation_zero K p a ha s hs b rel' k)
termination_by (c k).natDegree
decreasing_by exact _hlt

/-- A finite family of distinct rational places above a given element of F
has size bounded by the actual degree of the branch. -/
theorem field_value_degree (K : Type*) [Field K] [Algebra (RatFunc F) K]
    [FiniteDimensional (RatFunc F) K] (P : Finset (RationalPlace F K)) (a : F)
    (h : ∀ p ∈ P, Value p (algebraMap (RatFunc F) K RatFunc.X) a) : P.card ≤ finrank (RatFunc F) K := by
  classical
  obtain ⟨s,hs⟩ := CubicPoleFibre.selectors_field P
  have hind : LinearIndependent (RatFunc F) s := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc k
    simp only [Algebra.smul_def] at hc
    obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite F[X]⁰ c
    choose d hd using hb
    simp only [Algebra.smul_def] at hd
    have rel : ∑ i, pol K (d i) * s i = 0 := by
      calc
        _ = ∑ i, pol K (b : F[X]) * (algebraMap (RatFunc F) K (c i) * s i) := by
          apply sum_congr rfl
          intro i _
          simp only [pol, RingHom.comp_apply, hd i, map_mul, mul_assoc]
        _ = 0 := by rw [← mul_sum,hc,mul_zero]
    have dz := relation_zero K (fun i : P => i.val) a (fun i => h _ i.property) s hs d rel k
    have eqn := hd k
    rw [dz,map_zero] at eqn
    exact (mul_eq_zero.mp eqn.symm).resolve_left (by
      simpa using (IsFractionRing.injective F[X] (RatFunc F)).ne (nonZeroDivisors.ne_zero b.property))

  simpa only [Fintype.card_coe] using hind.fintype_card_le_finrank

/-- The image of a rational place on the intercept line. -/
noncomputable def fieldBasePoint {K : Type*} [Field K] [Algebra (RatFunc F) K]
    (p : RationalPlace F K) : Option F := by
  classical
  exact if h : algebraMap (RatFunc F) K RatFunc.X ∈ p.ring then some (p.residue ⟨_,h⟩) else none

theorem field_fibre_finset {K : Type*} [Field K] [Algebra (RatFunc F) K]
    [FiniteDimensional (RatFunc F) K] (P : Finset (RationalPlace F K)) (b : Option F)
    (in_fibre : ∀ p ∈ P, fieldBasePoint p = b) : P.card ≤ finrank (RatFunc F) K := by
  classical
  cases b with
  | none =>
    apply CubicPoleDegree.field_pole_degree
    intro p hp ht
    have h := in_fibre p hp
    simp [fieldBasePoint,ht] at h
  | some a =>
    apply field_value_degree K _ a
    intro p hp
    have h := in_fibre p hp
    by_cases ht : algebraMap (RatFunc F) K RatFunc.X ∈ p.ring
    · exact ⟨ht,by simpa [fieldBasePoint,ht] using h⟩
    · simp [fieldBasePoint,ht] at h

theorem field_card_le_degree_times_points (K : Type*) [Field K] [Algebra (RatFunc F) K]
    [FiniteDimensional (RatFunc F) K] (P : Finset (RationalPlace F K)) :
    P.card ≤ finrank (RatFunc F) K * (Fintype.card F+1) := by
  classical
  have h := card_le_mul_card_image_of_maps_to (s := P) (f := fieldBasePoint)
    (fun _ _ => mem_univ _) (finrank (RatFunc F) K) (fun z _ => ?_)
  · simpa using h
  · exact field_fibre_finset _ z (fun _ hp => (mem_filter.mp hp).2)

/-- Rational places of a finite cover of the line over a finite field. -/
noncomputable def fieldPlaceFintype (K : Type*) [Field K] [Algebra (RatFunc F) K]
    [FiniteDimensional (RatFunc F) K] : Fintype (RationalPlace F K) :=
  fintypeOfFinsetCardLe _ (field_card_le_degree_times_points K)

/-- Every rational fibre, including infinity and branch values, is bounded
by the degree of the function field extension. -/
theorem field_fibre_card (K : Type*) [Field K] [Algebra (RatFunc F) K]
    [FiniteDimensional (RatFunc F) K] [Fintype (RationalPlace F K)] [DecidableEq F]
    (b : Option F) : Fintype.card {p : RationalPlace F K // fieldBasePoint p = b} ≤
      finrank (RatFunc F) K := by
  classical
  rw [Fintype.card_subtype]
  exact field_fibre_finset _ b (fun _ hp => (mem_filter.mp hp).2)

theorem card_le_degree_of_value (D : Branch F R) (P : Finset (Place D)) (a : F)
    (h : ∀ p ∈ P, Value p (parameter D) a) : P.card ≤ finrank (RatFunc F) D.K := by
  letI := CubicPoleDegree.branch_finite D
  exact field_value_degree D.K P a h

noncomputable def basePoint (D : Branch F R) (p : Place D) : Option F := fieldBasePoint p

theorem card_le_degree_times_points (D : Branch F R) (P : Finset (Place D)) :
    P.card ≤ finrank (RatFunc F) D.K * (Fintype.card F+1) := by
  letI := CubicPoleDegree.branch_finite D
  exact field_card_le_degree_times_points D.K P

noncomputable def placeFintype (D : Branch F R) : Fintype (Place D) := by
  letI := CubicPoleDegree.branch_finite D
  exact fieldPlaceFintype D.K

theorem rational_places_bound (D : Branch F R) :
    @Fintype.card (Place D) (placeFintype D) ≤ finrank (RatFunc F) D.K * (Fintype.card F+1) := by
  letI := placeFintype D
  simpa using card_le_degree_times_points D univ

end BlockingCurves.CubicFiniteFibres
