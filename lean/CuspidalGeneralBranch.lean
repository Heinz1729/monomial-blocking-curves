import CuspidalGeneral
import PencilCollisionCover
import CubicAsymptotics

namespace BlockingCurves.CuspidalGeneral

open Finset Polynomial

variable {F : Type*} [Field F]

/-- The entire geometric zero fibre, counted with its actual multiplicities.
The formula applies over every field extension and in wild characteristic. -/
theorem zero_fibre_roots {d : ℕ} (hd : 2 ≤ d) (a : F) :
    ((X ^ d - C a * X ^ (d-1)) : F[X]).roots = (d-1) • ({0} : Multiset F) + {a} := by
  have form : ((X ^ d - C a * X ^ (d-1)) : F[X])=X^(d-1)*(X-C a) := by
    rw [mul_sub,←pow_succ,show d-1+1=d by omega,mul_comm (X^(d-1)) (C a)]
  rw [form,roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (X_sub_C_ne_zero a)),
    roots_X_pow,roots_X_sub_C]

/-- Outside 0 the vanishing derivative gives at most one further possible
critical point. Keeping natural casts retains the bad-characteristic cases. -/
theorem critical_point_iff {d : ℕ} (hd : 3 ≤ d) (a t : F) :
    (((X^d-C a*X^(d-1)):F[X]).derivative.eval t=0) ↔
      t=0 ∨ (d:F)*t=(d-1:ℕ)*a := by
  obtain ⟨k,rfl⟩ : ∃ k, d=k+3 := ⟨d-3,by omega⟩
  have identity : (((X^(k+3)-C a*X^(k+2)):F[X]).derivative.eval t)=
      t^(k+1)*(((k+3:ℕ):F)*t-((k+2:ℕ):F)*a) := by
    simp only [derivative_sub,derivative_mul,derivative_C,zero_mul,zero_add,
      derivative_X_pow,eval_sub,eval_mul,eval_C,eval_natCast,eval_pow,eval_X]
    change ((k+3:ℕ):F)*t^(k+2)-a*(((k+2:ℕ):F)*t^(k+1))=_
    rw [pow_succ t (k+1)]
    ring
  change (((X^(k+3)-C a*X^(k+2)):F[X]).derivative.eval t=0) ↔ _
  rw [identity,mul_eq_zero,sub_eq_zero]
  simp

/-- All critical values after base change are among 0 and a scalar multiple
of a^d. In either bad characteristic the only critical value is zero. -/
theorem critical_value_cases {d : ℕ} (hd : 3 ≤ d) (a t : F) (ha : a≠0)
    (critical : (((X^d-C a*X^(d-1)):F[X]).derivative.eval t=0)) :
    let c := ((d-1:ℕ):F)/(d:F)
    t^d-a*t^(d-1)=0 ∨ t^d-a*t^(d-1)=(c^d-c^(d-1))*a^d := by
  let c := ((d-1:ℕ):F)/(d:F)
  change _=0 ∨ _=(c^d-c^(d-1))*a^d
  rcases (critical_point_iff hd a t).mp critical with rfl | eqn
  · exact Or.inl (by simp [zero_pow (by omega : d≠0),zero_pow (by omega : d-1≠0)])
  · have nm : ((d-1:ℕ):F)=(d:F)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
    by_cases dz : (d:F)=0
    ·
      rw [dz,nm,dz,zero_sub,neg_one_mul,zero_mul] at eqn
      exact (ha (neg_eq_zero.mp eqn.symm)).elim
    · have tval : t=c*a := by
        dsimp [c]
        rw [nm] at eqn ⊢
        field_simp [dz]
        linear_combination eqn
      have ap : a^(d-1)*a=a^d := by rw [←pow_succ,show d-1+1=d by omega]
      right
      rw [tval,mul_pow,mul_pow,sub_mul]
      linear_combination (c^(d-1))* (Eq.symm ap)

/-- Excluding at most d times the number of ordered distinct shift pairs
leaves a nonzero slope and disjoint finite branch sets. The choice κ=0
covers the case with just one finite branch value. -/
theorem exists_separating_slope [Fintype F] [DecidableEq F] {d : ℕ} (hd : 0<d)
    (S : Finset F) (κ : F)
    (room : 1+S.offDiag.card * d < Fintype.card F) :
    ∃ a : F, a≠0 ∧ ∀ u ∈ S, ∀ v ∈ S, u≠v →
      Disjoint ({-u,κ*a^d-u} : Set F) {-v,κ*a^d-v} := by
  classical
  let bad (z : F×F) := univ.filter (fun a : F => κ*a^d=z.1-z.2)
  let excluded := insert 0 (S.offDiag.biUnion bad)
  have bound (z : F×F) (hz : z∈S.offDiag) : (bad z).card ≤ d := by
    convert (PencilCollisionCover.scaled_power_fibre_le d hd κ (z.1-z.2)
      (sub_ne_zero.mpr (mem_offDiag.mp hz).2.2)).trans (Nat.gcd_le_left _ hd) using 1
    congr 1
    ext t
    simp [bad]
  have small : excluded.card < Fintype.card F := by
    have := card_biUnion_le_card_mul S.offDiag bad d bound
    have := card_insert_le (0:F) (S.offDiag.biUnion bad)
    dsimp [excluded]
    omega
  obtain ⟨a,free⟩ : ∃ a : F, a∉excluded := by
    by_contra! all
    rw [eq_univ_of_forall all,card_univ] at small
    exact (lt_irrefl _) small
  have avoid (u v : F) (hu : u∈S) (hv : v∈S) (hne : u≠v) : κ*a^d≠u-v := by
    intro h
    exact free (mem_insert_of_mem (mem_biUnion.mpr ⟨(u,v),mem_offDiag.mpr ⟨hu,hv,hne⟩,
      mem_filter.mpr ⟨mem_univ _,h⟩⟩))
  refine ⟨a,fun e => free (e ▸ mem_insert_self _ _),?_⟩
  intro u hu v hv hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with h | h <;> rcases hy with j | j
  · exact hne (by linear_combination h-j)
  · exact avoid v u hv hu hne.symm (by linear_combination h-j)
  · exact avoid u v hu hv hne (by linear_combination j-h)
  · exact hne (by linear_combination h-j)

/-- The numerical twist test after removing up to 2ℓ+1 branch fibres.
The genus and degree estimates of the actual twist are geometric inputs. -/
theorem twist_threshold {q D C g : ℝ} {ell : ℕ}
    (hq : 16 ≤ q) (hD : 2 ≤ D) (hC : 1 ≤ C)
    (hg : g ≤ ell*(C-1)*D^ell)
    (hs : (ell:ℝ) ≤ (Real.log q-2*Real.log (Real.log q))/(2*Real.log D)
      - Real.log (16*C)/Real.log D) :
    (2*(ell:ℝ)+1)*D^ell < q+1-2*g*Real.sqrt q := by
  let e := (ell:ℝ)*D^ell
  have extended : g+e ≤ (ell:ℝ)*C*D^ell := by dsimp [e]; linarith only [hg]
  have cut := CubicAsymptotics.twist_point_threshold hq hD hC extended hs
  have hpow : 0 ≤ D^ell := pow_nonneg (by linarith) _
  have enon : 0 ≤ e := mul_nonneg (Nat.cast_nonneg _) hpow
  have sqrt : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr (by linarith)
  have paid : e ≤ e*Real.sqrt q := le_mul_of_one_le_right enon sqrt
  dsimp [e] at cut paid enon
  linarith only [cut,paid,hpow,enon]

end BlockingCurves.CuspidalGeneral
