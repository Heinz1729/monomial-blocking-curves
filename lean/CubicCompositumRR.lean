import Mathlib.FieldTheory.Adjoin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Convert

/-! For a one-root step K = B(x), the powers of x give a B-basis.
Multiplying them by a space of old functions and bounding their poles gives
the rational-second-factor case of Castelnuovo–Severi by Riemann–Roch. -/
namespace BlockingCurves.CubicCompositumRR
open Finset FiniteDimensional IntermediateField
variable {k B K : Type*} [Field k] [Field B] [Field K]
variable [Algebra k B] [Algebra B K] [Algebra k K] [IsScalarTower k B K]

/-- Polynomial evaluation in a specified new generator, on a direct sum of
copies of a subspace of the old field, inside a subspace of the new field. -/
def sumPowers {n : ℕ} (x : K) (U : Submodule k B) (V : Submodule k K)
    (hUV : ∀ (j : Fin n) (u : U), (u : B) • x^(j:ℕ) ∈ V) :
    (Fin n → U) →ₗ[k] V where
  toFun a := ⟨∑ j, (a j : B) • x^(j:ℕ), V.sum_mem fun j _ => hUV j (a j)⟩
  map_add' a b := by
    apply Subtype.ext
    change (∑ j, ((a j:B)+(b j:B)) • x^(j:ℕ)) = _ + _
    simp only [add_smul,Finset.sum_add_distrib]
  map_smul' r a := by
    apply Subtype.ext
    change (∑ j, (r • (a j:B)) • x^(j:ℕ)) = r • _
    simp only [smul_assoc,Finset.smul_sum]

private theorem powers_independent [FiniteDimensional B K] (x : K)
    (hgen : adjoin B {x} = ⊤) :
    LinearIndependent B (fun i : Fin (finrank B K) => x^(i:ℕ)) := by
  let e : adjoin B {x} ≃ₐ[B] K := (equivOfEq hgen).trans IntermediateField.topEquiv
  let pb := (adjoin.powerBasis (IsIntegral.of_finite B x)).map e
  have hg : pb.gen = x := by
    rw [show pb.gen = e (adjoin.powerBasis (IsIntegral.of_finite B x)).gen from PowerBasis.map_gen _ _]
    rfl
  have hb : LinearIndependent B (fun i : Fin pb.dim => pb.basis i) := pb.basis.linearIndependent
  simp_rw [pb.basis_eq_pow, hg] at hb
  rw [pb.finrank]
  exact hb

/-- Linear independence is over the old function field, so the coefficient
spaces can be chosen over the ground field without losing injectivity. -/
theorem sumPowers_injective [FiniteDimensional B K] (x : K) (hgen : adjoin B {x} = ⊤)
    (U : Submodule k B) (V : Submodule k K)
    (hUV : ∀ (j : Fin (finrank B K)) (u : U), (u : B) • x^(j:ℕ) ∈ V) :
    Function.Injective (sumPowers x U V hUV) := by
  apply LinearMap.ker_eq_bot.mp
  apply (LinearMap.ker_eq_bot').2
  intro a ha
  have h : (∑ j, (a j:B) • x^(j:ℕ)) = 0 := congrArg Subtype.val ha
  have hz := Fintype.linearIndependent_iff.mp (powers_independent x hgen) (fun j => (a j:B)) h
  funext j
  exact Subtype.ext (hz j)

theorem dimension_bound [FiniteDimensional B K] (x : K) (hgen : adjoin B {x} = ⊤)
    (U : Submodule k B) (V : Submodule k K) [FiniteDimensional k U] [FiniteDimensional k V]
    (hUV : ∀ (j : Fin (finrank B K)) (u : U), (u : B) • x^(j:ℕ) ∈ V) :
    finrank B K * finrank k U ≤ finrank k V := by
  have h := LinearMap.finrank_le_finrank_of_injective (sumPowers_injective x hgen U V hUV)
  simpa [finrank_pi_fintype] using h

/-- Specialize U and V to large-divisor Riemann–Roch spaces. Here m is the
degree of the divisor downstairs, c bounds the cost of the poles of
1,x,…,x^(n₁−1), and n₂ is the degree of the function x.  The two dimension
identities are in the nonspecial range. -/
theorem genus_bound [FiniteDimensional B K] (x : K) (hgen : adjoin B {x} = ⊤)
    (U : Submodule k B) (V : Submodule k K) [FiniteDimensional k U] [FiniteDimensional k V]
    (hUV : ∀ (j : Fin (finrank B K)) (u : U), (u : B) • x^(j:ℕ) ∈ V)
    (m c n₂ g₁ g : ℕ) (hn₂ : 0 < n₂)
    (oldRR : finrank k U + g₁ = m+1)
    (newRR : finrank k V + g = finrank B K*m+c+1)
    (poleCost : c ≤ (finrank B K-1)*n₂) :
    g ≤ finrank B K*g₁ + (finrank B K-1)*(n₂-1) := by
  have hd := dimension_bound x hgen U V hUV
  have hn : 0 < finrank B K := finrank_pos
  let n := finrank B K
  change n*finrank k U ≤ _ at hd
  change _ = n*m+c+1 at newRR
  change c ≤ (n-1)*n₂ at poleCost
  change g ≤ n*g₁ + (n-1)*(n₂-1)
  have hs : n-1+1=n := Nat.sub_add_cancel hn
  have hs₂ : n₂-1+1=n₂ := Nat.sub_add_cancel hn₂
  have hc : c ≤ (n-1)*(n₂-1)+(n-1) := by
    calc
      c ≤ (n-1)*n₂ := poleCost
      _ = _ := by conv_lhs => rw [← hs₂]
                  rw [Nat.mul_add,Nat.mul_one]
  have he := congrArg (n*·) oldRR
  simp only [Nat.mul_add,Nat.mul_one] at he
  omega

end BlockingCurves.CubicCompositumRR
