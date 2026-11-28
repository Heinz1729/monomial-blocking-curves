import CuspidalRationalSpecialization
import CuspidalTwistDegree
import CuspidalTwistGenus
import CuspidalCompositumLower

/-! The cuspidal lower bound on the rational places of the actual
Frobenius fixed field. The two curve inequalities are explicit. -/

namespace BlockingCurves.CuspidalDescent

open CuspidalGeneral CuspidalRootTower CubicRepairPlaces CubicFiniteFibres
noncomputable section
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- Hasse–Weil for rational places of the fixed field and the dimension
of regular differentials on its actual geometric scalar extension. -/
def TwistHasseWeil {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
    (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S) : Prop :=
  (Fintype.card F : ℝ) + 1 - 2 * (twistGeometricGenus S g hd ha : ℝ) * Real.sqrt (Fintype.card F)
    ≤ Nat.card (RationalPlace F (twistField d a S g))

/-- Assemble the canonical projection and its specialization directly on
the descended field. Hasse–Weil supplies the lower bound for its points. -/
def descendedProjection {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
    (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)
    (hw : TwistHasseWeil hd ha S g) :
    TwistProjection hd ha S (frobeniusRootAction hd ha S * geometricRootAction hd ha S g) := by
  let D := twistField d a S g
  letI : FiniteDimensional (RatFunc F) D := (twist_degree_eq hd ha S g).1
  letI := fieldPlaceFintype (F := F) D
  refine { Point := RationalPlace F D, projection := fieldBasePoint,
           hasseWeil := ?_, fibreDegree := ?_, specialization := ?_ }
  · simpa only [TwistHasseWeil,twist_geometric_genus,Nat.card_eq_fintype_card] using hw
  · intro b
    exact (field_fibre_card (F := F) D b).trans_eq (twist_degree_eq hd ha S g).2
  · intro p b hp hb α
    exact rational_place_specialization hd ha S g p hp hb α

/-- The two outstanding classical inequalities, on specified fields. -/
def DescendedCurveLaws {d : ℕ} (hd : 3 ≤ d) (S : Finset F) : Prop :=
  ∀ (a : F) (ha : a ≠ 0), (∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      Disjoint ({-u,extraCritical d a-u} : Set F) {-v,extraCritical d a-v}) →
    CastelnuovoSeveri (AlgebraicClosure F) (GeometricSplitting d a S) ∧
    ∀ g, TwistHasseWeil hd ha S g

private theorem twistLaws_of_descended {d : ℕ} (hd : 3 ≤ d) (S : Finset F)
    (laws : DescendedCurveLaws hd S) : FrobeniusTwistLaws hd S := by
  intro a ha sep
  obtain ⟨cs, hw⟩ := laws a ha sep
  exact ⟨cs,fun g => ⟨descendedProjection hd ha S g (hw g)⟩⟩

theorem lower_of_descended_curves {d : ℕ} (hd : 3 ≤ d) (S : Finset F)
    (room : 1 + S.offDiag.card*d < Fintype.card F) (laws : DescendedCurveLaws hd S)
    (hq : 16 ≤ (Fintype.card F : ℝ)) (blocks : Blocks d (S : Set F)) :
    (Real.log (Fintype.card F) - 2*Real.log (Real.log (Fintype.card F))) /
      (2*Real.log (d.factorial : ℝ)) - Real.log (16*(d : ℝ))/Real.log (d.factorial : ℝ) < S.card :=
  lower_of_frobenius_twists hd S room (twistLaws_of_descended hd S laws) hq blocks

/-- The threshold is chosen before the field and its shift set. -/
theorem logarithmic_lower_of_descended_curves {d : ℕ} (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c)
    (window : c * Real.log (d.factorial : ℝ) < 1/2) :
    ∀ᶠ q : ℝ in Filter.atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      (Fintype.card F : ℝ) = q → ∀ S : Finset F, DescendedCurveLaws hd S →
        Blocks d (S : Set F) → c * Real.log q < S.card := by
  filter_upwards [logarithmic_lower_of_frobenius_twists.{u} hd hc window] with q hq
  intro F _ _ _ size S laws
  exact hq F size S (twistLaws_of_descended hd S laws)

end
end BlockingCurves.CuspidalDescent
