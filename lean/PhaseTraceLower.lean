import NormPencilTrace
import PhaseBranches
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The hyperplane obstruction for a Frobenius map with cyclotomic branches.
Multiplication against a nonzero functional gives the full finite-field dual. -/
namespace BlockingCurves.PhaseTraceLower

variable {F E ι : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  [FiniteDimensional F E]

private theorem represent (L : E →ₗ[F] F) (hL : L ≠ 0) (P : E →ₗ[F] F) :
    ∃ a : E, ∀ x, L (a*x) = P x := by
  obtain ⟨c,hc⟩ := NormPencil.trace_representative L
  obtain ⟨d,hd⟩ := NormPencil.trace_representative P
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hL
    ext x
    simpa using (hc x).symm
  refine ⟨d/c, fun x => ?_⟩
  rw [← hc, ← mul_assoc, show c*(d/c) = d by field_simp, hd]

/-- Independent multipliers allow all base-field coordinates to be prescribed at once. -/
theorem coordinate_surjective (w : ι → E) (independent : LinearIndependent F w)
    (L : E →ₗ[F] F) (hL : L ≠ 0) :
    Function.Surjective (fun b : E => fun i : ι => L (w i * b)) := by
  classical
  intro y
  let h := independent.to_subtype_range
  let B := Basis.extend h
  let values := Function.extend w y (fun _ : E => (0 : F))
  let P := B.constr F (fun i => values i.val)
  obtain ⟨b,hb⟩ := represent L hL P
  refine ⟨b, funext fun i => ?_⟩
  let j : h.extend (Set.subset_univ _) :=
    ⟨w i, Basis.subset_extend h (Set.mem_range_self i)⟩
  have hj : B j = w i := Basis.extend_apply_self h j
  change L (w i * b) = y i
  rw [mul_comm, hb, ← hj, Basis.constr_basis]
  exact independent.injective.extend_apply _ _ _

/-- Parameters enlarged by the branch multipliers meet every affine hyperplane. -/
theorem orbit_hyperplane_hits (w : ι → E) (independent : LinearIndependent F w)
    (T : E →ₗ[F] E) (f : E → E)
    (branches : ∀ x, ∃ i, T (w i * x) = w i * f x) {S : Set E}
    (blocks : GraphHits f S) : HyperplaneHits F {z | ∃ i, ∃ u ∈ S, z = w i*u} := by
  intro L hL y
  obtain ⟨a,ha⟩ := represent L hL (L.comp T)
  obtain ⟨b,hb⟩ := coordinate_surjective w independent L hL (fun _ => -y)
  obtain ⟨x,hx⟩ := blocks a b
  obtain ⟨i,hi⟩ := branches x
  refine ⟨w i * (f x-a*x-b), ⟨i, _, hx, rfl⟩, ?_⟩
  have he := ha (w i*x)
  change L (a*(w i*x)) = L (T (w i*x)) at he
  rw [hi, mul_left_comm] at he
  have hb' : L (w i*b) = -y := congrFun hb i
  rw [mul_sub, mul_sub, map_sub, map_sub, ← he, sub_self, hb']
  simp

/-- Jamison--Brouwer--Schrijver applied to the union of the dilates. -/
theorem cardinal_lower [Fintype ι] [Nonempty ι] (w : ι → E)
    (independent : LinearIndependent F w) (T : E →ₗ[F] E) (f : E → E)
    (branches : ∀ x, ∃ i, T (w i * x) = w i * f x) (S : Finset E)
    (blocks : GraphHits f (S : Set E)) :
    (Fintype.card F-1) * FiniteDimensional.finrank F E + 1 ≤ Fintype.card ι * S.card := by
  classical
  let U := (Finset.univ.product S).image (fun p : ι × E => w p.1*p.2)
  have hit : HyperplaneHits F (U : Set E) := by
    intro L hL y
    obtain ⟨z,⟨i,u,hu,rfl⟩,hz⟩ := orbit_hyperplane_hits w independent T f branches blocks L hL y
    exact ⟨_, Finset.mem_image.mpr ⟨(i,u), Finset.mem_product.mpr ⟨Finset.mem_univ _,hu⟩,rfl⟩,hz⟩
  obtain ⟨x,hx⟩ := blocks 0 0
  let i := Classical.arbitrary ι
  have hU : U.Nonempty := ⟨_, Finset.mem_image.mpr ⟨(i,_),
    Finset.mem_product.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩⟩
  have lower := lower_of_hyperplaneHits (FiniteDimensional.finBasis F E) U hU hit
  have upper : U.card ≤ (Finset.univ.product S : Finset (ι × E)).card := Finset.card_image_le
  have hprod := Finset.card_product (Finset.univ : Finset ι) S
  simpa only [Fintype.card_fin, Finset.card_univ] using lower.trans (upper.trans_eq hprod)

/-- The divisible phase for actual finite extensions, in the projective pencil of the paper. -/
theorem divisible_projective_lower {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (divides : m ∣ Fintype.card F-1) (phase : m ∣ n)
    (size : Fintype.card E = Fintype.card F^n) (S : Finset E)
    (blocks : ProjectiveBlocks (Fintype.card F+(Fintype.card E-1)/m) (S : Set E)) :
    (Fintype.card F-1)*n+1 ≤ m*S.card := by
  classical
  let μ : Set F := ↑(Polynomial.nthRootsFinset m F)
  letI : Nonempty μ := ⟨⟨1,Polynomial.one_mem_nthRootsFinset (by omega)⟩⟩
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  have eig (z : μ) : ∃ w : E, w ≠ 0 ∧ σ w = (z : F) • w := by
    let u := Units.mk0 (z : F) (Polynomial.ne_zero_of_mem_nthRootsFinset z.property)
    have hu : u^m=1 := Units.ext ((Polynomial.mem_nthRootsFinset (by omega)).mp z.property)
    obtain ⟨w,hw,he⟩ := ExtensionPhase.exists_frobenius_eigenvector hn phase size u hu
    exact ⟨w,hw,by rw [hσ,he,Algebra.smul_def]; rfl⟩
  choose w hw0 hw using eig
  have independent : LinearIndependent F w :=
    Module.End.eigenvectors_linearIndependent σ.toLinearMap μ w fun z =>
      ⟨Module.End.mem_eigenspace_iff.mpr (hw z), hw0 z⟩
  let d := Fintype.card F + (Fintype.card E-1)/m
  have branches (x:E) : ∃ i : μ, σ.toLinearMap (w i*x) = w i*x^d := by
    by_cases hx : x = 0
    · refine ⟨Classical.arbitrary μ, ?_⟩
      have hd : 0 < d := Nat.add_pos_left Fintype.card_pos _
      simp [hx,zero_pow hd.ne']
    obtain ⟨z,hz,he⟩ := ExtensionPhase.cyclotomic_value_in_ground divides size x hx
    have hz' : (z:F)^m=1 := congrArg (fun u : Fˣ => (u:F)) hz
    let i : μ := ⟨(z:F),(Polynomial.mem_nthRootsFinset (by omega)).mpr hz'⟩
    refine ⟨i,?_⟩
    change σ (w i*x) = w i*x^(Fintype.card F+(Fintype.card E-1)/m)
    rw [map_mul,hw i,Algebra.smul_def,hσ,pow_add,← he]
    change algebraMap F E (z:F)*w i*x^Fintype.card F = _
    ring
  have hd : 2 ≤ d := le_trans (Fintype.one_lt_card (α := F)) (Nat.le_add_right _ _)
  have lower := cardinal_lower w independent σ.toLinearMap (fun x : E => x^d) branches S
    ((projectiveBlocks_iff_graphHits hd _).mp blocks)
  have hcard : Fintype.card μ ≤ m := by
    change Fintype.card ↥(Polynomial.nthRootsFinset m F) ≤ m
    rw [Fintype.card_coe,Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m (1:F))
  have dim : FiniteDimensional.finrank F E = n :=
    (Nat.pow_right_injective Fintype.one_lt_card) ((card_eq_pow_finrank (K := F) (V := E)).symm.trans size)
  rw [dim] at lower
  exact lower.trans (Nat.mul_le_mul_right _ hcard)

/-- The integer form of the lower bound in Theorem 10. -/
theorem divisible_projective_lower_rounded {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (divides : m ∣ Fintype.card F-1) (phase : m ∣ n)
    (size : Fintype.card E = Fintype.card F^n) (S : Finset E)
    (blocks : ProjectiveBlocks (Fintype.card F+(Fintype.card E-1)/m) (S : Set E)) :
    1 + n*(Fintype.card F-1)/m ≤ S.card := by
  have h := divisible_projective_lower hm hn divides phase size S blocks
  have h' : n*(Fintype.card F-1) < S.card*m := by
    rw [Nat.mul_comm n, Nat.mul_comm S.card]
    exact h
  have := (Nat.div_lt_iff_lt_mul (by omega : 0 < m)).2 h'
  omega

end BlockingCurves.PhaseTraceLower
