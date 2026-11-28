import FixedDegreeBudget
import Mathlib.FieldTheory.Adjoin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The root-by-root Castelnuovo–Severi calculation for a compositum of
splitting fields. The stage inequality itself is a classical geometric input.
All bounds here apply without restrictions on ramification. -/

namespace BlockingCurves.CuspidalTower

open Polynomial IntermediateField FiniteDimensional Real Filter

/-- Adjoining a new root after a set of distinct roots is already in the
coefficient field costs at most the residual degree. This applies to the
actual fields in a splitting tower, including relative degree one. -/
theorem remaining_root_degree {K M : Type*} [Field K] [Field M] [Algebra K M]
    (P : K[X]) (monic : P.Monic) (x : M) (root : aeval x P = 0)
    (known : Finset K) (roots : ∀ a ∈ known, P.IsRoot a)
    (fresh : ∀ a ∈ known, x ≠ algebraMap K M a) :
    finrank K (adjoin K ({x} : Set M)) + known.card ≤ P.natDegree := by
  classical
  have sub : known.val ≤ P.roots :=
    (Multiset.le_iff_subset known.nodup).2 fun a ha =>
      (mem_roots monic.ne_zero).2 (roots a ha)
  obtain ⟨Q,hQ⟩ := (known.val.prod_X_sub_C_dvd_iff_le_roots monic.ne_zero).2 sub
  have hQ0 : Q ≠ 0 := fun hz => monic.ne_zero (by simpa [hz] using hQ)
  have factor : aeval x (∏ a ∈ known, (X-C a : K[X])) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun a ha => by
      simpa only [map_sub, aeval_X, aeval_C] using sub_ne_zero.mpr (fresh a ha)
  have hx : IsIntegral K x := ⟨P,monic,root⟩
  rw [hQ, map_mul] at root
  have rootQ : aeval x Q=0 := (mul_eq_zero.mp root).resolve_left factor
  have deg := natDegree_le_of_dvd (minpoly.dvd K x rootQ) hQ0
  have degreeQ := congrArg natDegree hQ
  have hprod : (known.val.map fun a => (X-C a : K[X])).prod ≠ 0 :=
    fun hz => monic.ne_zero (by simpa [hz] using hQ)
  rw [natDegree_mul hprod hQ0, natDegree_multiset_prod_X_sub_C_eq_card] at degreeQ
  rw [adjoin.finrank hx]
  change P.natDegree = known.card + Q.natDegree at degreeQ
  omega

/-- The geometric degrees and genera of a root tower, indexed first by
polynomial, then by the number of distinct roots already adjoined.
`overRoot` is the degree of the new stage over the single rational root
field, whose degree over the parameter line is `d`. -/
structure RootTower (d ell : ℕ) where
  degree : ℕ → ℕ → ℕ
  genus : ℕ → ℕ → ℕ
  relative : ℕ → ℕ → ℕ
  overRoot : ℕ → ℕ → ℕ
  positive : ∀ i ≤ ell, ∀ j ≤ d, 0 < degree i j
  base_degree : degree 0 0 = 1
  base_genus : genus 0 0 = 0
  glue_degree : ∀ i < ell, degree (i+1) 0 = degree i d
  glue_genus : ∀ i < ell, genus (i+1) 0 = genus i d
  tower_degree : ∀ i < ell, ∀ j < d, degree i (j+1) = relative i j * degree i j
  root_degree : ∀ i < ell, ∀ j < d, degree i (j+1) = d * overRoot i j
  residual_degree : ∀ i < ell, ∀ j < d, relative i j + j ≤ d
  castelnuovo : ∀ i < ell, ∀ j < d,
    genus i (j+1) ≤ relative i j * genus i j + (relative i j-1)*(overRoot i j-1)

/-- The correction from the minus one in each factor of the
Castelnuovo–Severi term telescopes when the shifted genus is normalized. -/
private theorem normalized_step {n N g G e m d : ℝ} (hn : 0<n) (hN : 0<N)
    (hd : 0<d) (hn' : N=e*n) (hr : N=d*m)
    (cs : G ≤ e*g + (e-1)*(m-1)) :
    (G-1)/N ≤ (g-1)/n+(e-1)/d := by
  apply (div_le_iff hN).2
  calc
    G-1 ≤ e*g+(e-1)*(m-1)-1 := by linarith
    _ = e*(g-1)+(e-1)*m := by ring
    _ = (g-1)/n*N+(e-1)/d*N := by
      congr 1
      · rw [hn']; field_simp; ring
      · rw [hr]; field_simp; ring
    _ = _ := by ring

private noncomputable def ratio {d ell : ℕ} (T : RootTower d ell) (i j : ℕ) : ℝ :=
  ((T.genus i j:ℝ)-1)/(T.degree i j:ℝ)

private theorem polynomial_cost {d ell : ℕ} (hd : 0<d) (T : RootTower d ell)
    (i : ℕ) (hi : i<ell) (j : ℕ) (hj : j≤d) :
    2*(d:ℝ)*ratio T i j ≤
      2*d*ratio T i 0 + (j:ℝ)*(2*d-j-1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j<d := hj
    let e := T.relative i j
    let m := T.overRoot i j
    have hn := T.positive i hi.le j hj'.le
    have hN := T.positive i hi.le (j+1) hj
    have tower := T.tower_degree i hi j hj'
    have cover := T.root_degree i hi j hj'
    have he : 0<e := by
      by_contra! hz; have : T.relative i j=0 := Nat.eq_zero_of_le_zero hz
      simp [this] at tower; omega
    have hm : 0<m := by
      by_contra! hz; have : T.overRoot i j=0 := Nat.eq_zero_of_le_zero hz
      simp [this] at cover; omega
    have cs : (T.genus i (j+1):ℝ) ≤ (e:ℝ)*T.genus i j+((e:ℝ)-1)*((m:ℝ)-1) := by
      rw [← Nat.cast_one (R:=ℝ), ← Nat.cast_sub he, ← Nat.cast_sub hm]
      exact_mod_cast T.castelnuovo i hi j hj'
    have step : ratio T i (j+1) ≤ ratio T i j + ((e:ℝ)-1)/d :=
      normalized_step (by exact_mod_cast hn) (by exact_mod_cast hN) (by exact_mod_cast hd)
        (by exact_mod_cast tower) (by exact_mod_cast cover) cs
    have rem : (e:ℝ)+j ≤ d := by exact_mod_cast T.residual_degree i hi j hj'
    have scaled := mul_le_mul_of_nonneg_left step (by positivity : 0 ≤ 2*(d:ℝ))
    have idiv : 2*(d:ℝ)*(ratio T i j+((e:ℝ)-1)/d) =
        2*d*ratio T i j+2*(e-1) := by field_simp; ring
    rw [idiv] at scaled
    push_cast
    nlinarith only [ih hj'.le,scaled,rem]

/-- Over `ell` polynomials of degree `d`, the sharpened genus estimate is
`2g+2H ≤ ell*(d-1)*H+2`, where `H` is the final geometric degree. -/
theorem genus_budget {d ell : ℕ} (hd : 0<d) (T : RootTower d ell) :
    2*T.genus ell 0 + 2*T.degree ell 0 ≤ ell*(d-1)*T.degree ell 0+2 := by
  have bound (i : ℕ) (hi : i≤ell) :
      2*ratio T i 0 ≤ -2+(i:ℝ)*((d:ℝ)-1) := by
    induction i with
    | zero => simp [ratio,T.base_genus,T.base_degree]
    | succ i ih =>
      have hi' : i<ell := hi
      have cost := polynomial_cost hd T i hi' d le_rfl
      have same : ratio T (i+1) 0 = ratio T i d := by
        simp only [ratio,T.glue_degree i hi',T.glue_genus i hi']
      rw [same]
      push_cast
      have diff : 2*ratio T i d ≤ 2*ratio T i 0+((d:ℝ)-1) := by
        apply (mul_le_mul_left (by exact_mod_cast hd : (0:ℝ)<d)).mp
        linarith only [cost]
      nlinarith only [diff,ih hi'.le]
  have h := bound ell le_rfl
  have hn : (0:ℝ)<T.degree ell 0 := by
    exact_mod_cast T.positive ell le_rfl 0 (Nat.zero_le _)
  unfold ratio at h
  rw [← mul_div_assoc, div_le_iff hn] at h
  have hreal : 2*(T.genus ell 0:ℝ) + 2*(T.degree ell 0:ℝ) ≤
      (ell:ℝ)*((d:ℝ)-1)*T.degree ell 0+2 := by linarith only [h]
  rw [← Nat.cast_one (R:=ℝ), ← Nat.cast_sub hd] at hreal
  exact_mod_cast hreal

/-- The same relative degrees give the factorial bound on the order of
the geometric group, independently of the genera and of the constants. -/
theorem degree_budget {d ell : ℕ} (T : RootTower d ell) :
    T.degree ell 0 ≤ d.factorial^ell := by
  have block (i : ℕ) (hi : i<ell) (j : ℕ) (hj : j≤d) :
      T.degree i j * (d-j).factorial ≤ T.degree i 0 * d.factorial := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j<d := hj
      have hrel := T.residual_degree i hi j hj'
      have hfac : (d-j).factorial = (d-j)*(d-(j+1)).factorial := by
        conv_lhs => rw [show d-j=(d-(j+1))+1 by omega,Nat.factorial_succ]
        congr 1
        omega
      rw [T.tower_degree i hi j hj',Nat.mul_comm (T.relative i j),Nat.mul_assoc]
      apply (le_trans ?_ (ih hj'.le))
      apply Nat.mul_le_mul_left
      rw [hfac]
      exact Nat.mul_le_mul_right _ (show T.relative i j≤d-j by omega)
  have bound (i : ℕ) (hi : i≤ell) : T.degree i 0 ≤ d.factorial^i := by
    induction i with
    | zero => simp [T.base_degree]
    | succ i ih =>
      have hi' : i<ell := hi
      rw [T.glue_degree i hi',pow_succ]
      exact (by simpa using block i hi' d le_rfl :
        T.degree i d ≤ T.degree i 0*d.factorial).trans (Nat.mul_le_mul_right _ (ih hi'.le))
  exact bound ell le_rfl

/-- For every fixed coefficient strictly below the leading threshold the
point surplus holds simultaneously for *all* towers with at most c log q
polynomials. The same threshold leaves room for slope separation. -/
theorem uniform_point_budget {d : ℕ} (hd : 2≤d) {c : ℝ} (hc : 0<c)
    (subcritical : c*log (d.factorial:ℝ) < 1/2) :
    ∀ᶠ q : ℝ in atTop, ∀ ell : ℕ, (ell:ℝ) ≤ c*log q → ∀ T : RootTower d ell,
      1+(d:ℝ)*ell^2 < q ∧
      (2*(ell:ℝ)+1)*T.degree ell 0 <
        q+1-2*(T.genus ell 0:ℝ)*sqrt q := by
  let D : ℝ := d.factorial
  let ε := 1/2-c*log D
  have hε : 0<ε := sub_pos.mpr subcritical
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  have hD : 2≤D := by
    dsimp [D]
    have h : 2≤d.factorial := Nat.factorial_le hd
    exact_mod_cast h
  have hlogD := log_nonneg (show 1≤D by linarith)
  let A := (d:ℝ)*c^2
  have hA : 0<A := by dsimp [A]; positivity
  have log_small := tendsto_log_atTop.eventually
    (isLittleO_log_id_atTop.def (show 0<ε/2 by positivity))
  have sq_small := (isLittleO_log_rpow_rpow_atTop 2 (show (0:ℝ)<1 by norm_num)).def
    (show 0<(2*A)⁻¹ by positivity)
  filter_upwards [eventually_gt_atTop (2:ℝ),tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_log_atTop.eventually_ge_atTop (2*log (4*(d+1:ℝ))/ε), log_small, sq_small]
    with q hq hL hC hls hsq
  intro ell hell T
  have qpos : 0<q := by linarith
  have ep : log (4*(d+1:ℝ)) ≤ ε/2*log q := by
    have h := (div_le_iff hε).mp hC
    calc
      _ = (2*log (4*(d+1:ℝ)))/2 := by ring
      _ ≤ (log q*ε)/2 := div_le_div_of_nonneg_right h (by norm_num)
      _ = _ := by ring
  have ll : log (log q) ≤ ε/2*log q := by
    simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg (log_nonneg hL),
      abs_of_nonneg (by linarith : 0 ≤ log q)] using hls
  have win : (ell:ℝ)*log D ≤ log q/2-log (log q)-log (4*(d+1:ℝ)) := by
    have he := mul_le_mul_of_nonneg_right hell hlogD
    dsimp [ε] at ll ep
    nlinarith only [he,ep,ll]
  have sq : (log q)^2 ≤ (2*A)⁻¹*q := by
    simpa only [Real.rpow_two,Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (log q)),
      abs_of_pos qpos] using hsq
  have loss : A*(log q)^2 ≤ q/2 := by
    calc
      _ ≤ A*((2*A)⁻¹*q) := mul_le_mul_of_nonneg_left sq hA.le
      _ = q/2 := by field_simp; ring
  have sqell := pow_le_pow_left (Nat.cast_nonneg ell : (0:ℝ)≤ell) hell 2
  have deg : (T.degree ell 0:ℝ)≤D^ell := by dsimp [D]; exact_mod_cast degree_budget T
  have gen := genus_budget (by omega : 0<d) T
  have pos := T.positive ell le_rfl 0 (Nat.zero_le _)
  have gen' : 2*(T.genus ell 0:ℝ) ≤ ell*((d:ℝ)-1)*T.degree ell 0 := by
    rw [← Nat.cast_one (R:=ℝ), ← Nat.cast_sub (by omega : 1≤d)]
    exact_mod_cast (show 2*T.genus ell 0 ≤ ell*(d-1)*T.degree ell 0 by omega)
  constructor
  · dsimp [A] at loss
    nlinarith only [mul_le_mul_of_nonneg_left sqell (by linarith : (0:ℝ)≤d),loss,hq]
  · exact FixedDegreeBudget.growing_window hd' hD hL qpos gen' deg (Nat.cast_nonneg _)
      (by nlinarith only [mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg ell)]) win

end BlockingCurves.CuspidalTower
