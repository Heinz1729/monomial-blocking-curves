import CubicRepairBranch
import PencilSampling
import Mathlib.Algebra.GeomSum

/-! A common Laurent branch for arbitrary degrees invertible in the base field. -/
namespace BlockingCurves.PencilRepairBranch
open PowerSeries
noncomputable section
variable {F : Type*} [Field F]
local notation "A" => PowerSeries F
local notation "z" => (PowerSeries.X : A)
local notation "cc" => PowerSeries.constantCoeff F

private def equation (d : ℕ) (m b : F) (u : A) : A :=
  u^d-1-PowerSeries.C F m*u*z^(d-1)-PowerSeries.C F b*z^d

private def diff (d : ℕ) (m : F) (u v : A) : A :=
  (∑ i ∈ Finset.range d, u^i*v^(d-1-i)) - PowerSeries.C F m*z^(d-1)

private theorem factor (d : ℕ) (m b : F) (u v : A) :
    equation d m b u - equation d m b v = (u-v)*diff d m u v := by
  unfold equation diff
  linear_combination -((Commute.all u v).mul_geom_sum₂ d)

private theorem cc_diff {d : ℕ} (hd : 2 ≤ d) (m : F) {u v : A} (hu : cc u=1) (hv : cc v=1) :
    cc (diff d m u v) = (d:F) := by
  simp [diff, hu,hv, zero_pow (show d-1 ≠ 0 by omega)]

private structure Jet (d : ℕ) (m b : F) (n : ℕ) where
  y : A
  atZero : cc y = 1
  accuracy : z^(n+1) ∣ equation d m b y

private def first {d : ℕ} (hd : 2 ≤ d) (m b : F) : Jet d m b 0 :=
  ⟨1,map_one _, by
    rw [zero_add,pow_one,PowerSeries.X_dvd_iff]
    simp [equation,zero_pow (show d-1≠0 by omega),zero_pow (show d≠0 by omega)]⟩

private theorem step {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0) (m b : F) {n : ℕ}
    (J : Jet d m b n) : ∃ J' : Jet d m b (n+1), z^(n+1) ∣ J'.y-J.y := by
  obtain ⟨r,hr⟩ := J.accuracy
  let h := z^(n+1)
  let c := -r * PowerSeries.C F (d:F)⁻¹
  let u := J.y+h*c
  have hh : cc h = 0 := by simp [h]
  have hu : cc u = 1 := by simp [u, hh, J.atZero]
  let rem := r+c*diff d m u J.y
  have herr : equation d m b u = h*rem := by
    have he := factor d m b u J.y
    change equation d m b J.y = h*r at hr
    rw [hr, show u-J.y = h*c by dsimp [u]; ring] at he
    dsimp only [rem]
    linear_combination he
  have hrem : z ∣ rem := PowerSeries.X_dvd_iff.mpr (by
    simp [rem,c,cc_diff hd m hu J.atZero,hp])
  obtain ⟨w,hw⟩ := hrem
  refine ⟨⟨u,hu,w,?_⟩,c,?_⟩
  · rw [herr,hw,pow_succ]
    exact (mul_assoc _ _ _).symm
  · dsimp [u,h]; ring

private def jets {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0) (m b : F) :
    (n : ℕ) → Jet d m b n
  | 0 => first hd m b
  | n+1 => (step hd hp m b (jets hd hp m b n)).choose

private theorem stable {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0) (m b : F) {i j : ℕ} (hij : i ≤ j) :
    z^(i+1) ∣ (jets hd hp m b j).y - (jets hd hp m b i).y := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have h := (step hd hp m b (jets hd hp m b j)).choose_spec
    change z^(j+1) ∣ (jets hd hp m b (j+1)).y - (jets hd hp m b j).y at h
    convert dvd_add ((pow_dvd_pow z (Nat.succ_le_succ hij)).trans h) ih using 1
    ring

/-- The simple residue root one lifts through every order, over the original field. -/
theorem unique_series_root {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0) (m b : F) :
    ∃! y : A, cc y = 1 ∧ y^d - 1 - PowerSeries.C F m*y*z^(d-1) - PowerSeries.C F b*z^d = 0 := by
  let J := jets hd hp m b
  let y := PowerSeries.mk fun n => PowerSeries.coeff F n (J n).y
  have close (n : ℕ) : z^(n+1) ∣ y - (J n).y := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    have hs := PowerSeries.X_pow_dvd_iff.mp (stable hd hp m b (Nat.le_of_lt_succ hi)) i (Nat.lt_succ_self i)
    simp only [map_sub,sub_eq_zero] at hs ⊢
    simpa [y,J,PowerSeries.coeff_mk] using hs.symm
  have eq0 (n : ℕ) : z^(n+1) ∣ equation d m b y := by
    obtain ⟨v,hv⟩ := close n
    obtain ⟨r,hr⟩ := (J n).accuracy
    refine ⟨r+v*diff d m y (J n).y,?_⟩
    have he := factor d m b y (J n).y
    rw [hv,hr] at he
    linear_combination he
  have hy : equation d m b y = 0 := by
    apply PowerSeries.ext
    intro n
    simpa using PowerSeries.X_pow_dvd_iff.mp (eq0 n) n (Nat.lt_succ_self n)
  have hc : cc y = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [y,PowerSeries.coeff_mk,PowerSeries.coeff_zero_eq_constantCoeff_apply,(J 0).atZero]
  refine ⟨y,⟨hc,hy⟩,?_⟩
  rintro u ⟨hu,heu⟩
  have he := factor d m b u y
  change equation d m b u = 0 at heu
  rw [heu,hy,sub_self,eq_comm,mul_eq_zero] at he
  apply sub_eq_zero.mp (he.resolve_right ?_)
  intro h
  exact hp (by simpa [cc_diff hd m hu hc] using congrArg cc h)

/-- The series roots, divided by the uniformizer, solve all line equations at
the common parameter z⁻ᵈ. In particular horizontal lines are allowed. -/
theorem simultaneous_roots {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0) {I L : Type*} [Field L]
    (m b : I → F) (φ : A →+* L) (hz : φ z ≠ 0) :
    ∃ y : I → A, ∀ i, cc (y i)=1 ∧
      (φ (y i)/φ z)^d - φ (PowerSeries.C F (m i))*(φ (y i)/φ z) - φ (PowerSeries.C F (b i)) =
      ((φ z)^d)⁻¹ := by
  choose y hy using fun i => (unique_series_root hd hp (m i) (b i)).exists
  refine ⟨y, fun i => ⟨(hy i).1,?_⟩⟩
  have he := congrArg φ (hy i).2
  simp only [map_sub,map_pow,map_one,map_mul,map_zero] at he
  have hpow : φ z ^ d = φ z ^ (d-1) * φ z := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1≤d)]
  have hcancel : φ (y i) / φ z * φ z^d = φ (y i) * φ z^(d-1) := by
    rw [hpow, mul_comm (φ z^(d-1)), ← mul_assoc, div_mul_cancel₀ _ hz]
  apply (mul_left_inj' (pow_ne_zero d hz)).mp
  rw [sub_mul,sub_mul,div_pow,div_mul_cancel₀ _ (pow_ne_zero _ hz),mul_assoc,hcancel,
    inv_mul_cancel (pow_ne_zero _ hz)]
  linear_combination he

end
end BlockingCurves.PencilRepairBranch
