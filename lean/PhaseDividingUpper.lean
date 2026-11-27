import PhaseDirectionSampling
import PhaseBranches

namespace BlockingCurves.PhaseDividing
open Finset PhaseDirection
open scoped BigOperators
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
attribute [local instance] Classical.propDecidable

/-- If a line direction is transverse to a subspace containing G, each of the
s|G| good base points has a unique G-point and a unique scalar parameter. -/
theorem transverse_miss (H : Submodule F E) (G : Finset E) (inside : ∀ g ∈ G, g ∈ H)
    (v : E) (outside : v ∉ H) :
    emptyCount (hits F G v) + Fintype.card F * G.card = Fintype.card E := by
  classical
  let f (z : F × G) := (z.2:E)-v*algebraMap F E z.1
  have inj : Function.Injective f := by
    rintro ⟨t,g⟩ ⟨u,h⟩ he
    change (g:E)-v*algebraMap F E t = (h:E)-v*algebraMap F E u at he
    have eq : (t-u) • v = (g:E)-h := by
      rw [Algebra.smul_def, map_sub]
      linear_combination -he
    have mem : (t-u) • v ∈ H := eq ▸ H.sub_mem (inside g g.2) (inside h h.2)
    have ht : t=u := by
      by_contra ne
      have hh := H.smul_mem (t-u)⁻¹ mem
      apply outside
      simpa [inv_smul_smul₀ (sub_ne_zero.mpr ne)] using hh
    subst u
    exact Prod.ext rfl (Subtype.ext (by linear_combination he))
  have cover : univ.filter (fun b : E => hits F G v b = 0) = (univ.image f)ᶜ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_compl, mem_image, hits_eq_zero_iff]
    constructor
    · intro h ⟨⟨t,g⟩,he⟩
      apply h t
      change (g:E)-v*algebraMap F E t = b at he
      rw [← he]
      simp [point]
    · intro h t ht
      apply h
      exact ⟨(t,⟨point t (v,b),ht⟩), by simp [f,point]⟩
  rw [emptyCount,cover,Finset.card_compl,Finset.card_image_of_injective _ inj,
    Finset.card_univ,Fintype.card_prod,Fintype.card_coe]
  exact Nat.sub_add_cancel (by simpa using Fintype.card_le_of_injective _ inj)

/-- The count of base points over bad image values is at most the number of
empty translates observed along the one-dimensional kernel. -/
theorem source_misses (L : E →ₗ[F] E) (C : Finset E) {w : E} (hw : L w = 0)
    (hk : Nat.card (LinearMap.ker L) = Fintype.card F) :
    Fintype.card E ≤ emptyCount (hits F C w) + Fintype.card F*(C.image L).card := by
  classical
  let G := C.image L
  let good := univ.filter (fun x : E => hits F C w x ≠ 0)
  have key (x : good) : L x ∈ G := by
    have h := (Finset.mem_filter.mp x.2).2
    change ¬ hits F C w (x:E) = 0 at h
    rw [hits_eq_zero_iff] at h
    push_neg at h
    obtain ⟨t,ht⟩ := h
    refine mem_image.mpr ⟨point t (w,x),ht,?_⟩
    change L ((x:E)+w*algebraMap F E t) = L x
    rw [mul_comm,← Algebra.smul_def, map_add, map_smul, hw,smul_zero,add_zero]
  have sectionG (g : G) : ∃ x : E, L x = g := by
    obtain ⟨x,_,hx⟩ := mem_image.mp g.2
    exact ⟨x,hx⟩
  choose repr im using sectionG
  let f (x : good) : G × LinearMap.ker L :=
    let g : G := ⟨L x,key x⟩
    (g,⟨x-repr g,by simp [LinearMap.mem_ker,im]⟩)
  have recover (x : good) : (x:E) = (f x).2.1 + repr (f x).1 := by simp [f]
  have inj : Function.Injective f := fun x y he => Subtype.ext
    ((recover x).trans ((congrArg (fun z : G × LinearMap.ker L => z.2.1+repr z.1) he).trans (recover y).symm))
  have h := Fintype.card_le_of_injective _ inj
  rw [Fintype.card_coe,Fintype.card_prod,Fintype.card_coe,← Nat.card_eq_fintype_card (α := LinearMap.ker L),hk] at h
  have partition : emptyCount (hits F C w) + good.card = Fintype.card E := by
    simp only [emptyCount,good]
    rw [Finset.filter_card_add_filter_neg_card_eq_card,card_univ]
  rw [Nat.mul_comm] at h
  exact partition ▸ Nat.add_le_add_left h _
/-- Both random coordinates are genuine field elements. For a singular linear branch
the directions parallel to the image cost 1/s, and the transverse ones cost
at most the empty-fibre fraction of the multiplicative subgroup. -/
theorem singular_empty_fraction (L : E →ₗ[F] E) (C : Subgroup Eˣ) {w : E} (hw : L w = 0)
    (hw0 : w ≠ 0) (hk : Nat.card (LinearMap.ker L) = Fintype.card F) :
    let G := (carrier C).image L
    (emptyCount (fun p : E × E => hits F G p.1 p.2):ℝ)/(Fintype.card E:ℝ)^2 ≤
      1/(Fintype.card F:ℝ) + C.index/mean F (carrier C) := by
  classical
  let G := (carrier C).image L
  let B := emptyCount (hits F (carrier C) w)
  let T := Finset.univ.filter (fun v : E => v ∈ LinearMap.range L)
  let X (v : E) := emptyCount (hits F G v)
  have hr : Fintype.card (LinearMap.range L)*Fintype.card F = Fintype.card E := by
    rw [← hk, Nat.card_eq_fintype_card, card_eq_pow_finrank (K := F) (V := LinearMap.range L),
      card_eq_pow_finrank (K := F) (V := LinearMap.ker L),← pow_add,
      LinearMap.finrank_range_add_finrank_ker L, ← card_eq_pow_finrank]
  have tcard : T.card = Fintype.card (LinearMap.range L) := by
    simp [T,Fintype.card_subtype]
  have h (v : E) : X v ≤ (if v ∈ T then Fintype.card E else 0) + B := by
    by_cases hv : v ∈ LinearMap.range L
    · have le : X v ≤ Fintype.card E := Finset.card_le_univ _
      have hvT : v ∈ T := Finset.mem_filter.mpr ⟨mem_univ _,hv⟩
      rw [if_pos hvT]
      omega
    · have te := transverse_miss (LinearMap.range L) G (fun _ h => by
        obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp h; exact ⟨x,rfl⟩) v hv
      have src := source_misses L (carrier C) hw hk
      change X v + Fintype.card F*G.card = _ at te
      change _ ≤ B + Fintype.card F*G.card at src
      have hvT : v ∉ T := fun h => hv (Finset.mem_filter.mp h).2
      rw [if_neg hvT]
      omega
  have row : emptyCount (fun p : E × E => hits F G p.1 p.2) = ∑ v, X v := by
    simp only [emptyCount,X,Finset.card_filter,Fintype.sum_prod_type]
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun v _ => h v)
  rw [Finset.sum_add_distrib,←row] at bound
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ,nsmul_eq_mul,tcard] at bound
  have q0 : (0:ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  have s0 : (0:ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hrR : (Fintype.card (LinearMap.range L):ℝ)*Fintype.card F = Fintype.card E := by exact_mod_cast hr
  have le : (emptyCount (fun p : E × E => hits F G p.1 p.2):ℝ) ≤
      (Fintype.card (LinearMap.range L):ℝ)*Fintype.card E+(Fintype.card E:ℝ)*B := by exact_mod_cast bound
  have fixed := fixed_empty_fraction (F := F) C w hw0
  dsimp only
  change _ ≤ 1/(Fintype.card F:ℝ)+_
  apply le_trans _ (add_le_add_left fixed _)
  refine (div_le_iff (pow_pos q0 2)).2 ?_
  rw [add_mul]
  have one : (1/(Fintype.card F:ℝ))*(Fintype.card E:ℝ)^2 =
      (Fintype.card (LinearMap.range L):ℝ)*Fintype.card E := by
    calc
      _ = (1/(Fintype.card F:ℝ)) * ((Fintype.card (LinearMap.range L):ℝ) * Fintype.card F) * Fintype.card E := by rw [hrR]; ring
      _ = _ := by field_simp only [ne_of_gt s0]; ring
  rw [one]
  have bt : (B:ℝ)/(Fintype.card E:ℝ)*(Fintype.card E:ℝ)^2 = (Fintype.card E:ℝ)*B := by field_simp; ring
  change _ ≤ _ + (B:ℝ)/_ * _
  rwa [bt]

/-- A single bound for the regular and singular branches of the actual
relative Frobenius, with no assumption on the slope. -/
theorem frobenius_block_bound (C : Subgroup Eˣ) (a : E) :
    let G := (carrier C).image (fun x : E => x^Fintype.card F-a*x)
    (emptyCount (fun p : E × E => hits F G p.1 p.2):ℝ)/(Fintype.card E:ℝ)^2 ≤
      1/(Fintype.card F:ℝ) + (C.index:ℝ)/mean F (carrier C) := by
  classical
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let L := σ.toLinearMap - LinearMap.mulLeft F a
  have law (x : E) : L x = x^Fintype.card F-a*x := by
    change σ x-a*x = _
    rw [hσ]
  dsimp only
  simp_rw [← law]
  by_cases inj : Function.Injective L
  · have mem : (carrier C).Nonempty := ⟨1,Finset.mem_image.mpr ⟨1,mem_univ _,rfl⟩⟩
    have h := affine_empty_fraction (F := F) ((carrier C).image L) (mem.image _)
    have id : mean F ((carrier C).image L) = mean F (carrier C) := by
      simp only [mean,card_image_of_injective _ inj]
    rw [id] at h
    have h1 : (1:ℝ) ≤ C.index := by exact_mod_cast (Nat.pos_of_ne_zero C.index_ne_zero_of_finite)
    have le := div_le_div_of_nonneg_right h1 (show (0:ℝ) ≤ mean F (carrier C) by unfold mean; positivity)
    exact h.trans (le.trans (le_add_of_nonneg_left (by positivity)))
  · unfold Function.Injective at inj
    push_neg at inj
    obtain ⟨x,y,he,ne⟩ := inj
    let w := x-y
    have hw0 : w ≠ 0 := sub_ne_zero.mpr ne
    have hw : L w = 0 := by dsimp [w]; rw [map_sub,he,sub_self]
    have eigen (v : E) (hv : L v = 0) : σ v = a*v := sub_eq_zero.mp hv
    have a0 : a≠0 := by
      intro ha
      have h := eigen w hw
      rw [ha,zero_mul,← map_zero σ] at h
      exact hw0 (σ.injective h)
    let φ (t : F) : LinearMap.ker L := ⟨t • w,by change L (t • w) = 0; rw [map_smul,hw,smul_zero]⟩
    have hi : Function.Injective φ := by
      intro t u ht
      have hh : t • w = u • w := congrArg Subtype.val ht
      simp only [Algebra.smul_def] at hh
      exact (algebraMap F E).injective (mul_right_cancel₀ hw0 hh)
    have hs : Function.Surjective φ := by
      intro z
      have fixed : σ ((z:E)/w) = (z:E)/w := by
        rw [map_div₀,eigen _ z.2,eigen w hw]; field_simp; ring
      obtain ⟨t,ht⟩ := (pow_card_eq_iff_scalar F E _).1 ((hσ _).symm.trans fixed)
      refine ⟨t,Subtype.ext ?_⟩
      change t • w = _
      rw [Algebra.smul_def,ht,div_mul_cancel₀ _ hw0]
    have hk := Nat.card_congr (Equiv.ofBijective φ ⟨hi,hs⟩).symm
    exact singular_empty_fraction L C hw hw0 (hk.trans Nat.card_eq_fintype_card)

end BlockingCurves.PhaseDividing
