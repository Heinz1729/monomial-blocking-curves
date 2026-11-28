import CuspidalGlobalChart
import CuspidalLocalFactor

/-! Single-coordinate automorphisms of the actual common splitting field,
constructed by restricting automorphisms of a Laurent-field closure. -/
namespace BlockingCurves.CuspidalLocal

open Polynomial CuspidalGeneral
noncomputable section
variable {K : Type*} [Field K]

private abbrev sheet (a : K) : PowerSeries K := PowerSeries.C K a + PowerSeries.X

private abbrev inclusion (K : Type*) [Field K] := algebraMap (PowerSeries K) (LaurentSeries K)

private theorem own_factorization (n : ℕ) (a α : K) :
    (cuspCoordinate (n+1) a α).map (chartMap n a α).toRingHom =
      (X-C (inclusion K (sheet a))) * (complement PowerSeries.X (sheet a) n).map (inclusion K) := by
  have split := congrArg (fun P => P.map (inclusion K))
    (factorization (PowerSeries.C K a) PowerSeries.X n)
  dsimp only at split
  rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at split
  rw [split, chart_coordinate]
  refine congrArg (Polynomial.map (inclusion K)) ?_
  simp only [integralFibre, chartIntercept, Nat.add_sub_cancel, sub_self,
    map_zero, add_zero, pow_succ X n]
  ring

/-- On the actual joint splitting field over K(B), an automorphism supported
at the chosen coordinate can carry any nondistinguished root to any other.
The coordinate label and all remaining root sets are the original ones. -/
theorem supported_global_transport [IsAlgClosed K] {d : ℕ} (hd : 3 ≤ d)
    {a α : K} (ha : a ≠ 0) (S : Finset K) (hα : α ∈ S)
    (separated : ∀ v ∈ S, v ≠ α →
      Disjoint ({-α,extraCritical d a-α} : Set K) {-v,extraCritical d a-v}) :
    ∃ x₀ ∈ (cuspCoordinate d a α).rootSet (cuspCompositum d a S),
      ∀ y ∈ (cuspCoordinate d a α).rootSet (cuspCompositum d a S),
      ∀ z ∈ (cuspCoordinate d a α).rootSet (cuspCompositum d a S), y ≠ x₀ → z ≠ x₀ →
        ∃ g : cuspCompositum d a S ≃ₐ[RatFunc K] cuspCompositum d a S,
          g x₀ = x₀ ∧ g y = z ∧ ∀ v ∈ S, v ≠ α →
            ∀ x ∈ (cuspCoordinate d a v).rootSet (cuspCompositum d a S), g x = x := by
  obtain ⟨n,rfl⟩ : ∃ n, d=n+1+1 := ⟨d-2,by omega⟩
  let ι := globalEmbedding (n+1) a α S
  let r := inclusion K (sheet a)
  let r' := algebraMap (LaurentSeries K) (ChartClosure K) r
  let Q := (complement PowerSeries.X (sheet a) (n+1)).map (inclusion K)
  have split := own_factorization (n+1) a α
  obtain ⟨x₀,h₀,hx₀⟩ := global_root_of_local_root (n+1) a α α S hα r' (by
    rw [split]; simp [r',r, inclusion, sheet])
  refine ⟨x₀,h₀,?_⟩
  intro y hy z hz ny nz
  have other (w : cuspCompositum (n+1+1) a S)
      (hw : w ∈ (cuspCoordinate (n+1+1) a α).rootSet _) (hn : w ≠ x₀) :
      aeval (ι w) Q = 0 := by
    have root := chart_root_test (n+1) a α α S hw
    rw [split] at root
    change aeval (ι w) ((X-C r)*Q) = 0 at root
    simp only [map_mul,map_sub,aeval_X,aeval_C,mul_eq_zero,sub_eq_zero] at root
    exact root.resolve_left (fun e => hn (ι.injective (e.trans hx₀.symm)))
  obtain ⟨σ,move⟩ := local_root_transport a ha n (ι y) (ι z) (other y hy ny) (other z hz nz)
  obtain ⟨g,res⟩ := descend_local_action (n+1) a α S σ
  refine ⟨g,ι.injective ?_,ι.injective ((res y).trans move),?_⟩
  · change globalEmbedding (n+1) a α S (g x₀) = _
    rw [res,hx₀]
    exact σ.commutes r
  · intro v hv ne x hx
    exact ι.injective ((res x).trans (fixes_other_chart_root hd ha (separated v hv ne) S σ hx))

end
end BlockingCurves.CuspidalLocal
