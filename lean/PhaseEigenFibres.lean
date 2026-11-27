import PhaseCommonVariable

/-! Eigenspace coordinates of the actual common-intercept operator. The
arguments also apply after extending the ambient field to its algebraic closure. -/
namespace BlockingCurves.PhaseCommonVariable
open Polynomial Finset
open scoped BigOperators

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable [DecidableEq F]

/-- The scalar of the product operator on a given eigenspace. -/
theorem productEnd_on_eigen (T : Module.End F E) (Z : Finset F)
    {v:E} {mu : F} (hv : T v = mu • v) :
    productEnd T Z v = (∏ u ∈ Z, (u*mu-1)) • v := by
  induction Z using Finset.induction_on with
  | empty => simp [productEnd]
  | @insert z Z hz ih =>
    rw [productEnd,Finset.prod_insert hz, map_mul,LinearMap.mul_apply]
    change aeval T (C z*X-1) (productEnd T Z v) = _
    rw [ih]
    simp only [map_sub,map_mul,aeval_C,aeval_X,map_one,LinearMap.sub_apply,LinearMap.mul_apply,
      Module.algebraMap_end_apply,LinearMap.one_apply,LinearMap.map_smulₛₗ,RingHom.id_apply,hv,
      Finset.prod_insert hz]
    simp only [smul_smul,sub_smul,one_smul,mul_sub,sub_mul,one_mul,mul_one]
    rw [smul_sub,smul_smul]
    congr 2; ring

private theorem productEnd_insert_apply (T : Module.End F E) (Z : Finset F)
    {z : F} (hz : z ∉ Z) (v:E) :
    productEnd T (insert z Z) v = z • T (productEnd T Z v) - productEnd T Z v := by
  unfold productEnd
  rw [Finset.prod_insert hz]
  simp [LinearMap.mul_apply,Module.algebraMap_end_apply]

private theorem eigen_weight_ne_zero (Z : Finset F) {z : F} (hn : z ≠ 0) (hz : z ∉ Z) :
    (∏ u ∈ Z, (u*z⁻¹-1)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro u hu he
  have h : u/z = 1 := by simpa only [div_eq_mul_inv] using sub_eq_zero.mp he
  exact hz ((div_eq_one_iff_eq hn).1 h ▸ hu)

/-- Every vector killed by the product is a sum of its eigencoordinates.
The proof is independent of the dimension of the ambient field. -/
theorem ker_productEnd_coordinates (T : Module.End F E) (Z : Finset F)
    (nonzero : ∀ u ∈ Z, u ≠ 0) (t:E) (ht : productEnd T Z t = 0) :
    ∃ v : F → E, (∀ u ∈ Z, T (v u) = u⁻¹ • v u) ∧ (∑ u ∈ Z, v u) = t := by
  induction Z using Finset.induction_on generalizing t with
  | empty =>
    simp [productEnd] at ht
    exact ⟨fun _ => 0,by simp,by simpa using ht.symm⟩
  | @insert z Z hz ih =>
    let y := productEnd T Z t
    let b := ∏ u ∈ Z, (u*z⁻¹-1)
    let w := b⁻¹ • y
    have hn : z≠0 := nonzero z (mem_insert_self ..)
    have hb : b≠0 := eigen_weight_ne_zero Z hn hz
    have hy : T y = z⁻¹ • y := by
      have h := sub_eq_zero.mp ((productEnd_insert_apply T Z hz t).symm.trans ht)
      change z • T y = y at h
      simpa only [inv_smul_smul₀ hn] using congrArg (fun x:E => z⁻¹ • x) h
    have hw : T w = z⁻¹ • w := by
      simp only [w,LinearMap.map_smul,hy,smul_comm b⁻¹]
    have hrem : productEnd T Z (t-w) = 0 := by
      rw [map_sub,productEnd_on_eigen T Z hw]
      change y - b • (b⁻¹ • y) = 0
      rw [smul_inv_smul₀ hb,sub_self]
    obtain ⟨v,hv,hsum⟩ := ih (fun u hu => nonzero u (mem_insert_of_mem hu)) (t-w) hrem
    let v' (u:F) := if u=z then w else v u
    refine ⟨v',?_,?_⟩
    · intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · simpa [v'] using hw
      · simpa [v',ne_of_mem_of_not_mem hu hz] using hv u hu
    · rw [sum_insert hz]
      have he : (∑ u ∈ Z, v' u) = ∑ u ∈ Z, v u := sum_congr rfl
        (fun u hu => if_neg (ne_of_mem_of_not_mem hu hz))
      rw [he,hsum]
      simp [v']

/-- The product kernel is exactly the sum of the indexed eigenspaces. -/
theorem ker_productEnd_iff (T : Module.End F E) (Z : Finset F)
    (nonzero : ∀ u ∈ Z, u ≠ 0) (t:E) :
    productEnd T Z t = 0 ↔
      ∃ v : F → E, (∀ u ∈ Z, T (v u) = u⁻¹ • v u) ∧ (∑ u ∈ Z, v u) = t := by
  refine ⟨ker_productEnd_coordinates T Z nonzero t,?_⟩
  rintro ⟨v,hv,rfl⟩
  rw [map_sum]
  apply sum_eq_zero
  intro u hu
  rw [productEnd_on_eigen T Z (hv u hu)]
  have h : (∏ w ∈ Z, (w*u⁻¹-1)) = 0 := Finset.prod_eq_zero hu
    (by rw [mul_inv_cancel (nonzero u hu),sub_self])
  rw [h,zero_smul]

/-- In the whole eigencoordinate box the candidate omitting z depends
only on the z-coordinate, with its scalar explicitly nonzero. -/
theorem candidate_on_eigen_box (T : Module.End F E) (Z : Finset F) {z : F}
    (hz : z ∈ Z) (nonzero : ∀ u ∈ Z, u ≠ 0) (t c:E) (v:F → E)
    (hv : ∀ u ∈ Z, T (v u) = u⁻¹ • v u) :
    let weight := ∏ u ∈ Z.erase z, (u*z⁻¹-1)
    weight ≠ 0 ∧
      (productEnd T (Z.erase z) (t + ∑ u ∈ Z, v u)+c = 0 ↔
       v z = weight⁻¹ • (-(productEnd T (Z.erase z) t+c))) := by
  let Q := productEnd T (Z.erase z)
  let b := ∏ u ∈ Z.erase z, (u*z⁻¹-1)
  have hb : b ≠ 0 := eigen_weight_ne_zero _ (nonzero z hz) (Finset.not_mem_erase z Z)
  have hp : (∑ u ∈ Z, Q (v u)) = b • v z := by
    rw [sum_eq_single z]
    · exact productEnd_on_eigen T _ (hv z hz)
    · intro u hu ne
      dsimp [Q]
      rw [productEnd_on_eigen T _ (hv u hu)]
      have h : (∏ w ∈ Z.erase z, (w*u⁻¹-1)) = 0 := Finset.prod_eq_zero
        (mem_erase.mpr ⟨ne,hu⟩) (by rw [mul_inv_cancel (nonzero u hu),sub_self])
      rw [h,zero_smul]
    · exact fun he => (he hz).elim
  change b ≠ 0 ∧ (Q (t + ∑ u ∈ Z, v u)+c = 0 ↔ v z = _)
  refine ⟨hb,?_⟩
  rw [map_add,map_sum,hp]
  change Q t + b • v z + c = 0 ↔ v z = b⁻¹ • (-(Q t + c))
  constructor
  · intro h
    have h1 : b • v z = -(Q t+c) := by linear_combination h
    rw [← h1,inv_smul_smul₀ hb]
  · intro h
    rw [h,smul_inv_smul₀ hb]
    abel

/-- Uniqueness on the indexed coordinates, so the kernel decomposition is
internal. Values of the ambient indexing functions outside Z are immaterial. -/
theorem eigen_coordinates_unique (T : Module.End F E) (Z : Finset F)
    (nonzero : ∀ u ∈ Z, u ≠ 0) (v w:F → E)
    (hv : ∀ u ∈ Z, T (v u) = u⁻¹ • v u) (hw : ∀ u ∈ Z, T (w u) = u⁻¹ • w u)
    (hs : (∑ u ∈ Z, v u) = ∑ u ∈ Z, w u) : ∀ z ∈ Z, v z = w z := by
  intro z hz
  let c := -(productEnd T (Z.erase z) (∑ u ∈ Z, w u))
  have h₁ := (candidate_on_eigen_box T Z hz nonzero 0 c v hv).2
  have h₂ := (candidate_on_eigen_box T Z hz nonzero 0 c w hw).2
  exact (h₁.mp (by simp [c,hs])).trans (h₂.mp (by simp [c])).symm

end BlockingCurves.PhaseCommonVariable
