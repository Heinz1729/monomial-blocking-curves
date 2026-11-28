import CuspidalCompositumGenus
import CuspidalGeometricFrobenius
import CuspidalTwistFibre

/-! The remaining point-counting inputs use the genus and degree of the
same geometric splitting field in which the root tower is constructed. -/
namespace BlockingCurves.CuspidalGeneral
open CuspidalRootTower CuspidalTower FiniteDimensional
noncomputable section
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- Rational points on a descended twist. The Hasse–Weil and fibre bounds
use the actual geometric genus and covering degree. Specialization only
compares Frobenius conjugacy classes on the explicit regular locus. -/
structure TwistProjection {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
    (γ : S → Equiv.Perm (Fin d)) where
  Point : Type u
  [finitePoints : Fintype Point]
  projection : Point → Option F
  hasseWeil : (Fintype.card F : ℝ) + 1 -
    2 * (ambientGenus (AlgebraicClosure F) (GeometricSplitting d a S) : ℝ) *
    Real.sqrt (Fintype.card F) ≤ Fintype.card Point
  fibreDegree : ∀ b, Fintype.card {p : Point // projection p = b} ≤
    finrank (RatFunc (AlgebraicClosure F)) (GeometricSplitting d a S)
  specialization : ∀ p b, projection p = some b → ∀ hb : some b ∉ excludedBranches d a S,
    ∀ α : S, IsConj (regularFibreAction hd ha S hb α).perm (γ α)

attribute [instance] TwistProjection.finitePoints

private def TwistProjection.pointData {d : ℕ} {hd : 3 ≤ d} {a : F} {ha : a ≠ 0} {S : Finset F}
    {γ : S → Equiv.Perm (Fin d)} (X : TwistProjection hd ha S γ) : TwistPointData d a S γ := by
  classical
  let e := (Fintype.equivFin X.Point).symm
  refine TwistPointData.ofConjugacy hd ha S γ (Fintype.card X.Point)
    (ambientGenus (AlgebraicClosure F) (GeometricSplitting d a S))
    (finrank (RatFunc (AlgebraicClosure F)) (GeometricSplitting d a S))
    (fun i => X.projection (e i)) X.hasseWeil ?_ (fun p => X.specialization (e p))
  intro b
  rw [← Fintype.card_subtype]
  exact (le_of_eq (Fintype.card_congr (e.subtypeEquiv (by intro i; rfl)))).trans (X.fibreDegree b)

private theorem alignTower {d m n : ℕ} (h : m = n) (T : RootTower d m) :
    ∃ U : RootTower d n, U.genus n 0 = T.genus m 0 ∧ U.degree n 0 = T.degree m 0 := by
  subst n
  exact ⟨T,rfl,rfl⟩

/-- The classical laws on the actual fields and the rational points of the
twists in the constructed arithmetic-Frobenius coset. -/
def FrobeniusTwistLaws {d : ℕ} (hd : 3 ≤ d) (S : Finset F) : Prop :=
    ∀ (a : F) (ha : a ≠ 0), (∀ u ∈ S, ∀ v ∈ S, u ≠ v →
        Disjoint ({-u,extraCritical d a-u} : Set F) {-v,extraCritical d a-v}) →
      CastelnuovoSeveri (AlgebraicClosure F) (GeometricSplitting d a S) ∧
      ∀ g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S,
        Nonempty (TwistProjection hd ha S (frobeniusRootAction hd ha S * geometricRootAction hd ha S g))

/-- Explicit all-characteristic cuspidal lower bound from Castelnuovo–Severi
and the rational-point laws of the Frobenius twists. -/
theorem lower_of_frobenius_twists {d : ℕ} (hd : 3 ≤ d) (S : Finset F)
    (room : 1 + S.offDiag.card*d < Fintype.card F) (geometry : FrobeniusTwistLaws hd S)
    (hq : 16 ≤ (Fintype.card F : ℝ)) (blocks : Blocks d (S : Set F)) :
    (Real.log (Fintype.card F) - 2*Real.log (Real.log (Fintype.card F))) /
      (2*Real.log (d.factorial : ℝ)) - Real.log (16*(d : ℝ))/Real.log (d.factorial : ℝ) < S.card := by
  apply lower_of_twist_geometry hd S room _ hq blocks
  intro a ha sep
  obtain ⟨cs,twists⟩ := geometry a ha sep
  let S' := geometricShifts S
  have ha' := (_root_.map_ne_zero (algebraMap F (AlgebraicClosure F))).mpr ha
  let T := realizedTower hd ha' S' cs
  obtain ⟨U,hg,hN⟩ := alignTower (geometricShifts_card S) T
  refine ⟨frobeniusRootAction hd ha S,U,?_⟩
  intro g
  obtain ⟨X⟩ := twists g
  exact ⟨X.pointData, (hg.trans (terminal_genus hd ha' S' cs)).symm,
    (hN.trans (terminal_degree hd ha' S' cs)).symm⟩

/-- For each subcritical coefficient the same threshold works for every finite
field and every blocking shift set satisfying the classical geometric inputs. -/
theorem logarithmic_lower_of_frobenius_twists {d : ℕ} (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c)
    (window : c * Real.log (d.factorial : ℝ) < 1/2) :
    ∀ᶠ q : ℝ in Filter.atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      (Fintype.card F : ℝ) = q → ∀ S : Finset F, FrobeniusTwistLaws hd S →
        Blocks d (S : Set F) → c * Real.log q < S.card := by
  filter_upwards [eventual_explicit_window (by omega : 2 ≤ d) hc window] with q hq
  rintro F _ _ _ rfl S geometry blocks
  obtain ⟨hq,sep,threshold⟩ := hq
  by_contra! small
  have sq := pow_le_pow_left (Nat.cast_nonneg S.card : (0:ℝ) ≤ S.card) small 2
  have count : S.offDiag.card ≤ S.card^2 := by
    rw [Finset.offDiag_card, pow_two]
    exact Nat.sub_le _ _
  have roomReal : (1:ℝ) + S.offDiag.card*d < Fintype.card F := by
    apply lt_of_le_of_lt _ sep
    have h : (S.offDiag.card : ℝ) ≤ (S.card : ℝ)^2 := by exact_mod_cast count
    rw [mul_comm (S.offDiag.card : ℝ)]
    exact add_le_add_left (mul_le_mul_of_nonneg_left (h.trans sq) (Nat.cast_nonneg _)) 1
  have room : 1 + S.offDiag.card*d < Fintype.card F := by exact_mod_cast roomReal
  exact (not_lt_of_ge small) (threshold.trans (lower_of_frobenius_twists hd S room geometry hq blocks))

end
end BlockingCurves.CuspidalGeneral
