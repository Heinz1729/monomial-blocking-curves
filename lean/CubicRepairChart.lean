import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The point over infinity of the simultaneous cubic equations in §17.
Index the first line separately. On the chart where its coordinate is one,
the other line coordinates have labels `some i` and the homogenizing variable
has label `none`. The formulas hold after any extension of the coefficient field. -/
namespace BlockingCurves.CubicRepairChart

open MvPolynomial Finset
variable {K I : Type*} [Field K]

/-- The homogeneous cubic equating the parameters of two lines. Here the
projective indices `none`, `some none`, `some (some i)` mean Z, X₁, Xᵢ. -/
noncomputable def homogeneous (m₀ b₀ : K) (m b : I → K) (i : I) :
    MvPolynomial (Option (Option I)) K :=
  X (some (some i))^3 - X (some none)^3 -
    (C (m i) * X (some (some i)) - C m₀ * X (some none)) * X none^2 -
    C (b i-b₀) * X none^3

theorem homogeneous_degree (m₀ b₀ : K) (m b : I → K) (i : I) :
    (homogeneous m₀ b₀ m b i).IsHomogeneous 3 := by
  have lin (c : K) (j : Option (Option I)) : (C c * X j).IsHomogeneous 1 := by
    simpa using isHomogeneous_C_mul_X_pow c j 1
  exact (((isHomogeneous_X_pow _ 3).sub (isHomogeneous_X_pow _ 3)).sub
    (((lin (m i) _).sub (lin m₀ _)).mul (isHomogeneous_X_pow _ 2))).sub
      (isHomogeneous_C_mul_X_pow _ _ 3)

/-- The same equation after setting X₁ to one. -/
noncomputable def chart (m₀ b₀ : K) (m b : I → K) (i : I) : MvPolynomial (Option I) K :=
  X (some i)^3 - 1 - (C (m i) * X (some i) - C m₀) * X none^2 - C (b i-b₀) * X none^3

/-- Recover homogeneous coordinates on this chart from an affine coordinate tuple. -/
def projectiveLift (v : Option I → K) : Option (Option I) → K
  | none => v none
  | some none => 1
  | some (some i) => v (some i)

theorem chart_eq_homogeneous (m₀ b₀ : K) (m b : I → K) (i : I) (v : Option I → K) :
    eval v (chart m₀ b₀ m b i) = eval (projectiveLift v) (homogeneous m₀ b₀ m b i) := by
  simp [chart, homogeneous, projectiveLift]

/-- The rational point [1:...:1:0] in these affine coordinates. -/
def infinity : Option I → K
  | none => 0
  | some _ => 1

theorem infinity_on_chart (m₀ b₀ : K) (m b : I → K) (i : I) :
    eval infinity (chart m₀ b₀ m b i) = 0 := by
  simp [chart, infinity]

/-- Every horizontal partial derivative, including the off-diagonal ones. -/
theorem jacobian_entry [DecidableEq I] (m₀ b₀ : K) (m b : I → K) (i j : I) :
    eval infinity (pderiv (some j) (chart m₀ b₀ m b i)) = if i=j then 3 else 0 := by
  by_cases h : i=j
  · subst j
    simp [chart, pderiv_pow, pderiv_mul, pderiv_C, pderiv_one, infinity]
  · simp [chart, pderiv_pow, pderiv_mul, pderiv_C, pderiv_one, infinity, h, Ne.symm h,
      Pi.single_apply]

theorem jacobian_z (m₀ b₀ : K) (m b : I → K) (i : I) :
    eval infinity (pderiv none (chart m₀ b₀ m b i)) = 0 := by
  classical
  simp [chart, pderiv_pow, pderiv_mul, pderiv_C, pderiv_one, infinity, Pi.single_apply]

/-- The Jacobian's tangent kernel consists precisely of the free Z direction. -/
theorem tangent_kernel [Fintype I] (m₀ b₀ : K) (m b : I → K) (h₃ : (3:K) ≠ 0)
    (v : Option I → K) :
    (∀ i, ∑ j : Option I, eval infinity (pderiv j (chart m₀ b₀ m b i)) * v j = 0) ↔
      ∀ i, v (some i) = 0 := by
  classical
  have hs (i : I) : (∑ j : Option I, eval infinity (pderiv j (chart m₀ b₀ m b i)) * v j) =
      3 * v (some i) := by
    rw [Fintype.sum_option]
    simp [jacobian_z, jacobian_entry, ite_mul, eq_comm]
  simp [hs, h₃]

/-- At any rational point away from infinity, the coordinates divided by Z
give genuine affine roots of the simultaneous line equations. -/
theorem affine_equation (m₀ b₀ : K) (m b : I → K) (i : I) (v : Option I → K)
    (hz : v none ≠ 0) :
    eval v (chart m₀ b₀ m b i) = 0 ↔
      (v (some i)/v none)^3 - m i * (v (some i)/v none) - b i =
      (1/v none)^3 - m₀ * (1/v none) - b₀ := by
  simp only [chart, map_sub, map_pow, eval_X, map_one, map_mul, eval_C]
  field_simp
  constructor <;> intro h
  · linear_combination v none * h
  · apply (mul_left_inj' hz).mp
    linear_combination h


section FormalBranch
open PowerSeries
local notation "A" => PowerSeries K
local notation "z" => (PowerSeries.X : A)
local notation "cc" => PowerSeries.constantCoeff K

/-- The chart equation as a univariate polynomial in its unknown power series. -/
noncomputable def branchEquation (m₀ b₀ m b : K) (y : A) : A :=
  y^3 - 1 - (PowerSeries.C K m * y - PowerSeries.C K m₀)*z^2 -
    PowerSeries.C K (b-b₀)*z^3

private structure Jet (m₀ b₀ m b : K) (n : ℕ) where
  y : A
  atZero : cc y = 1
  accuracy : z^(n+1) ∣ branchEquation m₀ b₀ m b y

private noncomputable def firstJet (m₀ b₀ m b : K) : Jet m₀ b₀ m b 0 :=
  ⟨1, map_one _, by
    rw [zero_add, pow_one, PowerSeries.X_dvd_iff]
    simp [branchEquation]⟩

/-- A Newton correction preserves all previously determined coefficients. -/
private theorem liftJet (m₀ b₀ m b : K) (h₃ : (3:K) ≠ 0) {n : ℕ} (J : Jet m₀ b₀ m b n) :
    ∃ J' : Jet m₀ b₀ m b (n+1), z^(n+1) ∣ J'.y-J.y := by
  obtain ⟨r, hr⟩ := J.accuracy
  let h := z^(n+1)
  let c := -r * PowerSeries.C K (3:K)⁻¹
  let u := J.y + h*c
  have hc : cc c = -(cc r) * (3:K)⁻¹ := by simp [c]
  have hh : cc h = 0 := by simp [h]
  have hu : cc u = 1 := by simp [u, hh, J.atZero]
  let rem := r + (3*J.y^2-PowerSeries.C K m*z^2)*c + h*c^2*(3*J.y+h*c)
  have herr : branchEquation m₀ b₀ m b u = h*rem := by
    dsimp [u,rem]
    unfold branchEquation at hr ⊢
    change _ = h*r at hr
    linear_combination hr
  have hrem : z ∣ rem := PowerSeries.X_dvd_iff.mpr (by
    simp [rem,hc,hh,J.atZero]
    field_simp)
  obtain ⟨w,hw⟩ := hrem
  refine ⟨⟨u,hu,w,?_⟩, c, ?_⟩
  · rw [herr,hw,pow_succ]
    exact mul_assoc _ _ _ |>.symm
  · dsimp [u,h]
    ring

private noncomputable def jets (m₀ b₀ m b : K) (h₃ : (3:K) ≠ 0) :
    (n : ℕ) → Jet m₀ b₀ m b n
  | 0 => firstJet m₀ b₀ m b
  | n+1 => (liftJet m₀ b₀ m b h₃ (jets m₀ b₀ m b h₃ n)).choose

private theorem jets_stable (m₀ b₀ m b : K) (h₃ : (3:K) ≠ 0)
    {i j : ℕ} (hij : i ≤ j) :
    z^(i+1) ∣ (jets m₀ b₀ m b h₃ j).y - (jets m₀ b₀ m b h₃ i).y := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have h := (liftJet m₀ b₀ m b h₃ (jets m₀ b₀ m b h₃ j)).choose_spec
    change z^(j+1) ∣ (jets m₀ b₀ m b h₃ (j+1)).y - (jets m₀ b₀ m b h₃ j).y at h
    have hl := (pow_dvd_pow z (Nat.succ_le_succ hij)).trans h
    convert dvd_add hl ih using 1
    ring

/-- Lifting the simple root 1 over K, with all coefficients in K.
The reduction of a solution modulo each power of Z eventually stabilizes. -/
theorem exists_unique_branch (m₀ b₀ m b : K) (h₃ : (3:K) ≠ 0) :
    ∃! y : A, cc y = 1 ∧ branchEquation m₀ b₀ m b y = 0 := by
  let J := jets m₀ b₀ m b h₃
  let y := PowerSeries.mk fun n => PowerSeries.coeff K n (J n).y
  have close (n : ℕ) : z^(n+1) ∣ y - (J n).y := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    have hs := PowerSeries.X_pow_dvd_iff.mp
      (jets_stable m₀ b₀ m b h₃ (Nat.le_of_lt_succ hi)) i (Nat.lt_succ_self i)
    simp only [map_sub, sub_eq_zero] at hs ⊢
    simpa [y,J,PowerSeries.coeff_mk] using hs.symm
  have eq0 (n : ℕ) : z^(n+1) ∣ branchEquation m₀ b₀ m b y := by
    obtain ⟨d,hd⟩ := close n
    obtain ⟨r,hr⟩ := (J n).accuracy
    refine ⟨r + d*(y^2+y*(J n).y+(J n).y^2-PowerSeries.C K m*z^2), ?_⟩
    unfold branchEquation at hr ⊢
    linear_combination hr + (y^2+y*(J n).y+(J n).y^2-PowerSeries.C K m*z^2)*hd
  have hy : branchEquation m₀ b₀ m b y = 0 := by
    apply PowerSeries.ext
    intro n
    simpa using PowerSeries.X_pow_dvd_iff.mp (eq0 n) n (Nat.lt_succ_self n)
  have hc : cc y = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [y,PowerSeries.coeff_mk,PowerSeries.coeff_zero_eq_constantCoeff_apply,(J 0).atZero]
  refine ⟨y,⟨hc,hy⟩,?_⟩
  rintro u ⟨hu,heu⟩
  let factor := u^2+u*y+y^2-PowerSeries.C K m*z^2
  have hf : factor ≠ 0 := by
    intro h
    have ht := congrArg cc h
    simp [factor,hc,hu] at ht
    exact h₃ (by linear_combination ht)
  have he : (u-y)*factor = 0 := by
    unfold branchEquation at hy heu
    dsimp [factor]
    linear_combination heu-hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hf)

/-- All the formal roots lie over one and the same parameter. In a field
containing the series ring, take the parameter Z⁻³ and the roots yᵢ/Z.
This applies in particular to its fraction field. -/
theorem simultaneous_roots_at_inverse_cube {L : Type*} [Field L]
    (m b : I → K) (h₃ : (3:K) ≠ 0) (φ : PowerSeries K →+* L) (hz : φ z ≠ 0) :
    ∃ y : I → PowerSeries K, ∀ i, cc (y i) = 1 ∧
      (φ (y i) / φ z)^3 - φ (PowerSeries.C K (m i)) * (φ (y i) / φ z) -
      φ (PowerSeries.C K (b i)) = (φ z)⁻¹^3 := by
  classical
  let y := fun i => (exists_unique_branch 0 0 (m i) (b i) h₃).exists.choose
  have hy (i : I) := (exists_unique_branch 0 0 (m i) (b i) h₃).exists.choose_spec
  refine ⟨y, fun i => ⟨(hy i).1, ?_⟩⟩
  have h := congrArg φ (hy i).2
  change φ (branchEquation 0 0 (m i) (b i) (y i)) = φ 0 at h
  simp [branchEquation] at h
  field_simp
  linear_combination (φ z)^4 * h



end FormalBranch

end BlockingCurves.CubicRepairChart
