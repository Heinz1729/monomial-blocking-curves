import Mathlib.LinearAlgebra.Dual
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace BlockingCurves

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [FiniteDimensional K F]

/-- Every finite-slope affine line meets one of the translated graphs. -/
def GraphHits {E : Type*} [Field E] (f : E → E) (S : Set E) : Prop :=
  ∀ m b : E, ∃ x : E, f x - m * x - b ∈ S

/-- Every fiber of every nonzero ground-field functional meets S. -/
def HyperplaneHits (k : Type*) [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (S : Set V) : Prop :=
  ∀ L : V →ₗ[k] k, L ≠ 0 → ∀ b : k, ∃ s ∈ S, L s = b

private def ScaledHits (σ : F ≃ₐ[K] F) (S : Set F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F, ∃ x : F, a * (σ x - x) - b ∈ S

private theorem twist (σ : F ≃ₐ[K] F) {u m : F} (hu : σ u = m * u) (x : F) :
    σ (u*x) - m*(u*x) = σ u * (σ x - x) := by
  rw [map_mul, hu]
  ring

private theorem graphHits_iff_scaled (σ : F ≃ₐ[K] F) (S : Set F) :
    GraphHits σ S ↔ ScaledHits σ S := by
  constructor
  · intro h a ha b
    obtain ⟨u, rfl⟩ := σ.surjective a
    have h0 : u ≠ 0 := by intro hz; simp [hz] at ha
    let m := σ u / u
    have hm : σ u = m*u := by dsimp [m]; field_simp
    obtain ⟨x, hx⟩ := h m b
    refine ⟨x/u, ?_⟩
    rw [← twist σ hm]
    have he : u * (x/u) = x := by field_simp
    simpa [he] using hx
  · intro h m b
    by_cases hk : ∃ u : F, u ≠ 0 ∧ σ u = m*u
    · obtain ⟨u, hu, he⟩ := hk
      have hu' : σ u ≠ 0 := by simpa using hu
      obtain ⟨x, hx⟩ := h (σ u) hu' b
      exact ⟨u*x, by rwa [twist σ he]⟩
    · let D : F →ₗ[K] F := σ.toLinearMap - LinearMap.mulLeft K m
      have hi : Function.Injective D := by
        intro x y hxy
        by_contra hne
        apply hk
        refine ⟨x-y, sub_ne_zero.mpr hne, ?_⟩
        have hz : D (x-y) = 0 := by rw [map_sub, hxy, sub_self]
        exact sub_eq_zero.mp (show σ (x-y) - m*(x-y) = 0 from hz)
      obtain ⟨u, hu⟩ := h 1 one_ne_zero 0
      obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hi
        ((1 * (σ u-u) - 0) + b)
      change σ x - m*x = _ at hx
      exact ⟨x, by simpa only [hx, add_sub_cancel_right] using hu⟩

/-- A nullity-one endomorphism has image equal to a functional kernel. -/
private theorem nullityOneFunctional (D : F →ₗ[K] F)
    (dimKer : FiniteDimensional.finrank K (LinearMap.ker D) = 1) :
    ∃ L : F →ₗ[K] K, Function.Surjective L ∧
      ∀ y : F, L y = 0 ↔ ∃ x : F, D x = y := by
  have dimQuot : FiniteDimensional.finrank K (F ⧸ (LinearMap.range D)) =
      FiniteDimensional.finrank K K := by
    have h₁ := D.finrank_range_add_finrank_ker
    have h₂ := (LinearMap.range D).finrank_quotient_add_finrank
    rw [FiniteDimensional.finrank_self]
    omega
  let e : (F ⧸ (LinearMap.range D)) ≃ₗ[K] K := LinearEquiv.ofFinrankEq _ _ dimQuot
  refine ⟨e.toLinearMap.comp (LinearMap.range D).mkQ, e.surjective.comp (LinearMap.range D).mkQ_surjective, ?_⟩
  intro y
  change e ((LinearMap.range D).mkQ y) = 0 ↔ y ∈ (LinearMap.range D)
  rw [e.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- The image of σ−1 is the kernel of a surjective ground-field functional. -/
private theorem differenceFunctional (σ : F ≃ₐ[K] F)
    (fixed : ∀ x : F, σ x = x → ∃ c : K, algebraMap K F c = x) :
    ∃ L : F →ₗ[K] K, Function.Surjective L ∧
      ∀ y : F, L y = 0 ↔ ∃ x : F, σ x - x = y := by
  let D : F →ₗ[K] F := σ.toLinearMap - LinearMap.id
  have hk : (LinearMap.ker D) = LinearMap.range (Algebra.linearMap K F) := by
    ext x
    change (σ x - x = 0) ↔ ∃ c : K, algebraMap K F c = x
    constructor
    · exact fun hx => fixed x (sub_eq_zero.mp hx)
    · rintro ⟨c, rfl⟩
      rw [σ.commutes, sub_self]
  have dimKer : FiniteDimensional.finrank K (LinearMap.ker D) = 1 := by
    rw [hk, LinearMap.finrank_range_of_inj (algebraMap K F).injective,
      FiniteDimensional.finrank_self]
  exact nullityOneFunctional D dimKer

/-- A single nonzero functional generates the entire dual by field multiplication. -/
private theorem scalarDual (L : F →ₗ[K] K) (hL : Function.Surjective L)
    (l : F →ₗ[K] K) : ∃ c : F, ∀ x : F, l x = L (c*x) := by
  let T : F →ₗ[K] (F →ₗ[K] K) := {
    toFun := fun c => L.comp (LinearMap.mulLeft K c)
    map_add' := by intro a b; ext x; simp [add_mul]
    map_smul' := by intro t a; ext x; simp [smul_mul_assoc] }
  have hi : Function.Injective T := by
    intro a b hab
    by_contra hne
    obtain ⟨z, hz⟩ := hL 1
    let x := z/(a-b)
    have he := LinearMap.congr_fun hab x
    change L (a*x) = L (b*x) at he
    have he' : L ((a-b)*x) = 0 := by rw [sub_mul, map_sub, he, sub_self]
    have he'' : (a-b)*x = z := by dsimp [x]; field_simp [sub_ne_zero.mpr hne]
    rw [he'', hz] at he'
    exact one_ne_zero he'
  have hs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq.symm)).mp hi
  obtain ⟨c, hc⟩ := hs l
  exact ⟨c, fun x => (LinearMap.congr_fun hc x).symm⟩

/-- A translated semilinear graph blocks every line exactly when its translation
parameters meet every affine hyperplane over the fixed field. -/
theorem graphHits_iff_hyperplaneHits (σ : F ≃ₐ[K] F)
    (fixed : ∀ x : F, σ x = x → ∃ c : K, algebraMap K F c = x)
    (S : Set F) : GraphHits σ S ↔ HyperplaneHits K S := by
  rw [graphHits_iff_scaled]
  obtain ⟨L, hL, hk⟩ := differenceFunctional σ fixed
  constructor
  · intro h l hl b
    obtain ⟨c, hc⟩ := scalarDual L hL l
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hl
      ext x
      simpa using hc x
    obtain ⟨v, hv⟩ := surjective_of_nonzero_of_finrank_eq_one
      (FiniteDimensional.finrank_self K) hl b
    obtain ⟨x, hx⟩ := h c⁻¹ (inv_ne_zero hc0) (-v)
    refine ⟨c⁻¹*(σ x-x)-(-v), hx, ?_⟩
    have hd : L (σ x-x) = 0 := (hk _).2 ⟨x, rfl⟩
    rw [sub_neg_eq_add, map_add, hv, hc, ← mul_assoc, mul_inv_cancel hc0,
      one_mul, hd, zero_add]
  · intro h a ha b
    let l := L.comp (LinearMap.mulLeft K a⁻¹)
    have hl : l ≠ 0 := by
      intro he
      obtain ⟨z, hz⟩ := hL 1
      have ht := LinearMap.congr_fun he (a*z)
      change L (a⁻¹*(a*z)) = 0 at ht
      rw [← mul_assoc, inv_mul_cancel ha, one_mul, hz] at ht
      exact one_ne_zero ht
    obtain ⟨s, hs, he⟩ := h l hl (-l b)
    have hzero : L (a⁻¹*(s+b)) = 0 := by
      change l (s+b) = 0
      rw [map_add, he, add_left_neg]
    obtain ⟨x, hx⟩ := (hk _).1 hzero
    refine ⟨x, ?_⟩
    simpa only [hx, ← mul_assoc, mul_inv_cancel ha, one_mul, add_sub_cancel_right] using hs





/-- Standard kernel formulation of scatteredness of a linearized polynomial. -/
def Scattered (T : F →ₗ[K] F) : Prop :=
  ∀ m : F, FiniteDimensional.finrank K (LinearMap.ker (T - LinearMap.mulLeft K m)) ≤ 1

/-- Every linear graph yields the affine-hyperplane lower bound. -/
theorem hyperplaneHits_of_linear_graphHits (T : F →ₗ[K] F) {S : Set F}
    (h : GraphHits T S) : HyperplaneHits K S := by
  intro l hl b
  have surj := surjective_of_nonzero_of_finrank_eq_one
    (FiniteDimensional.finrank_self K) hl
  obtain ⟨m, hm⟩ := scalarDual l surj (l.comp T)
  obtain ⟨v, hv⟩ := surj b
  obtain ⟨x, hx⟩ := h m (-v)
  refine ⟨T x - m*x - (-v), hx, ?_⟩
  have hd : l (T x) = l (m*x) := hm x
  simp [map_sub, hd, hv]

/-- If every slope has nullity at most one, the two blocking conditions coincide. -/
theorem scattered_graphHits_iff (T : F →ₗ[K] F) (hT : Scattered T) (S : Set F) :
    GraphHits T S ↔ HyperplaneHits K S := by
  refine ⟨hyperplaneHits_of_linear_graphHits T, ?_⟩
  intro h m b
  let D := T - LinearMap.mulLeft K m
  by_cases hz : FiniteDimensional.finrank K (LinearMap.ker D) = 0
  · obtain ⟨l, hl, _⟩ := (⊥ : Submodule K F).exists_dual_map_eq_bot_of_lt_top
      bot_lt_top inferInstance
    obtain ⟨s, hs, _⟩ := h l hl 0
    have hinj : Function.Injective D :=
      LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinj (s+b)
    change T x - m*x = s+b at hx
    exact ⟨x, by simpa [hx] using hs⟩
  · have hle : FiniteDimensional.finrank K (LinearMap.ker D) ≤ 1 := hT m
    obtain ⟨l, surj, hk⟩ := nullityOneFunctional D (by omega)
    have hl : l ≠ 0 := by
      intro he
      obtain ⟨z, hz'⟩ := surj 1
      simp [he] at hz'
    obtain ⟨s, hs, he⟩ := h l hl (-l b)
    have he' : l (s+b) = 0 := by simp [he]
    obtain ⟨x, hx⟩ := (hk (s+b)).mp he'
    change T x - m*x = s+b at hx
    exact ⟨x, by simpa [hx] using hs⟩


/-- The equivalence for every choice of translates characterizes scattered maps. -/
theorem scattered_iff_forall_graphHits_iff (T : F →ₗ[K] F) :
    Scattered T ↔ ∀ S : Set F, GraphHits T S ↔ HyperplaneHits K S := by
  refine ⟨fun h => scattered_graphHits_iff T h, ?_⟩
  intro hall m
  let D := T - LinearMap.mulLeft K m
  let W := LinearMap.range D
  change FiniteDimensional.finrank K (LinearMap.ker D) ≤ 1
  by_contra hn
  have hits : HyperplaneHits K (W : Set F)ᶜ := by
    intro l hl b
    have hs := surjective_of_nonzero_of_finrank_eq_one
      (FiniteDimensional.finrank_self K) hl
    have notle : ¬ LinearMap.ker l ≤ W := by
      intro hle
      have hm := Submodule.finrank_mono hle
      have h₁ := D.finrank_range_add_finrank_ker
      have h₂ := l.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hs, finrank_top, FiniteDimensional.finrank_self] at h₂
      change FiniteDimensional.finrank K (LinearMap.ker l) ≤
        FiniteDimensional.finrank K (LinearMap.range D) at hm
      omega
    have hw' : ∃ w : F, l w = 0 ∧ w ∉ W := by
      by_contra hnone
      push_neg at hnone
      exact notle (fun x hx => hnone x hx)
    obtain ⟨w, hw, hwW⟩ := hw'
    obtain ⟨v, hv⟩ := hs b
    by_cases hvW : v ∈ W
    · refine ⟨w+v, ?_, by simp [hw, hv]⟩
      intro hsum
      exact hwW (by simpa using W.sub_mem hsum hvW)
    · exact ⟨v, hvW, hv⟩
  obtain ⟨x, hx⟩ := ((hall _).mpr hits) m 0
  apply hx
  change T x - m*x - 0 ∈ LinearMap.range D
  exact ⟨x, by simp [D]⟩

end BlockingCurves
