import CubicPoleDegree
import Mathlib.RingTheory.Localization.Integer

/-! Every rational fibre of the parameter has at most the extension degree
many rational places. Summing over the projective line makes the type of
rational places finite, independently of any estimate for its point count. -/
namespace BlockingCurves.CubicFiniteFibres
open Finset FiniteDimensional CubicAlteration CubicRepairPlaces CubicPoleFibre Polynomial nonZeroDivisors
variable {F : Type*} [Field F] [Fintype F] {R : Finset (Line F)}

private noncomputable def pol (D : Branch F R) : F[X] →+* D.K :=
  (algebraMap (RatFunc F) D.K).comp (algebraMap F[X] (RatFunc F))

private theorem value_pol {D : Branch F R} {p : Place D} {a : F}
    (ha : Value p (parameter D) a) (f : F[X]) : Value p (pol D f) (f.eval a) := by
  induction f using Polynomial.induction_on' with
  | h_add f g hf hg => simpa only [map_add,eval_add] using hf.add hg
  | h_monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, eval_mul, eval_pow, eval_C, eval_X]
    exact (value_const p c).mul (ha.pow n)

/-- In a polynomial relation of residue selectors all coefficients vanish
at a. Cancelling X−a produces another relation and lowers the degree of
any chosen nonzero coefficient. -/
private theorem relation_zero (D : Branch F R) {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → Place D) (a : F) (ha : ∀ i, Value (p i) (parameter D) a)
    (s : I → D.K) (hs : ∀ i j, Value (p j) (s i) (if i = j then 1 else 0))
    (c : I → F[X]) (rel : ∑ i, pol D (c i) * s i = 0) (k : I) : c k = 0 := by
  classical
  by_contra hk
  have dvd (i : I) : X-C a ∣ c i := by
    apply dvd_iff_isRoot.mpr
    have h := value_sum (p := p i) univ (fun j => pol D (c j) * s j)
      (fun j => (c j).eval a * (if j = i then 1 else 0))
      (fun j _ => (value_pol (ha i) (c j)).mul (hs j i))
    rw [rel] at h
    simpa [IsRoot, mul_ite] using h.unique (value_zero (p i))
  choose b hb using dvd
  have hlin := X_sub_C_ne_zero a
  have hmap : pol D (X-C a) ≠ 0 := fun h => hlin
    (((algebraMap (RatFunc F) D.K).injective.comp
      (IsFractionRing.injective F[X] (RatFunc F))) (h.trans (map_zero (pol D)).symm))
  have rel' : ∑ i, pol D (b i) * s i = 0 := by
    apply (mul_eq_zero.mp (show pol D (X-C a) * (∑ i, pol D (b i) * s i) = 0 from ?_)).resolve_left hmap
    rw [mul_sum]
    convert rel using 1
    apply sum_congr rfl
    intro i _
    rw [hb i, map_mul, mul_assoc]
  have bk : b k ≠ 0 := fun h => hk (by rw [hb k,h,mul_zero])
  have _hlt : (b k).natDegree < (c k).natDegree := by
    rw [hb k, natDegree_mul hlin bk, natDegree_X_sub_C]
    omega
  exact bk (relation_zero D p a ha s hs b rel' k)
termination_by (c k).natDegree
decreasing_by exact _hlt

/-- A finite family of distinct rational places above a given element of F
has size bounded by the actual degree of the branch. -/
theorem card_le_degree_of_value (D : Branch F R) (P : Finset (Place D)) (a : F)
    (h : ∀ p ∈ P, Value p (parameter D) a) : P.card ≤ finrank (RatFunc F) D.K := by
  classical
  obtain ⟨s,hs⟩ := CubicPoleFibre.selectors P
  have hind : LinearIndependent (RatFunc F) s := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc k
    simp only [Algebra.smul_def] at hc
    obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite F[X]⁰ c
    choose d hd using hb
    simp only [Algebra.smul_def] at hd
    have rel : ∑ i, pol D (d i) * s i = 0 := by
      calc
        _ = ∑ i, pol D b * (algebraMap (RatFunc F) D.K (c i) * s i) := by
          apply sum_congr rfl
          intro i _
          simp only [pol, RingHom.comp_apply, hd i, map_mul, mul_assoc]
        _ = 0 := by rw [← mul_sum,hc,mul_zero]
    have dz := relation_zero D (fun i : P => i.val) a (fun i => h _ i.property) s hs d rel k
    have eqn := hd k
    rw [dz,map_zero] at eqn
    exact (mul_eq_zero.mp eqn.symm).resolve_left (by
      simpa using (IsFractionRing.injective F[X] (RatFunc F)).ne (nonZeroDivisors.ne_zero b.property))
  letI := CubicPoleDegree.branch_finite D
  simpa only [Fintype.card_coe] using hind.fintype_card_le_finrank

/-- The image on the projective parameter line, with none for infinity. -/
noncomputable def basePoint (D : Branch F R) (p : Place D) : Option F := by
  classical
  exact if h : parameter D ∈ p.ring then some (p.residue ⟨_,h⟩) else none

theorem card_le_degree_times_points (D : Branch F R) (P : Finset (Place D)) :
    P.card ≤ finrank (RatFunc F) D.K * (Fintype.card F+1) := by
  classical
  have h := card_le_mul_card_image_of_maps_to (s := P) (f := basePoint D)
    (fun _ _ => mem_univ _) (finrank (RatFunc F) D.K) (fun z _ => ?_)
  · simpa using h
  · cases z with
    | none =>
      apply CubicPoleDegree.card_le_degree_of_polar
      intro p hp ht
      have eqn := (mem_filter.mp hp).2
      simp [basePoint,ht] at eqn
    | some a =>
      apply card_le_degree_of_value D _ a
      intro p hp
      have eqn := (mem_filter.mp hp).2
      by_cases ht : parameter D ∈ p.ring
      · exact ⟨ht,by simpa [basePoint,ht] using eqn⟩
      · simp [basePoint,ht] at eqn

/-- All rational places of the branch form a finite type. -/
noncomputable def placeFintype (D : Branch F R) : Fintype (Place D) :=
  fintypeOfFinsetCardLe _ (card_le_degree_times_points D)

theorem rational_places_bound (D : Branch F R) :
    @Fintype.card (Place D) (placeFintype D) ≤ finrank (RatFunc F) D.K * (Fintype.card F+1) := by
  letI := placeFintype D
  simpa using card_le_degree_times_points D univ

end BlockingCurves.CubicFiniteFibres
