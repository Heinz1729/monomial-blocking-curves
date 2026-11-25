import GeneralGeometry
import LowerBound
import UpperBound

namespace BlockingCurves
variable {K E : Type*} [Field K] [Fintype K] [Field E] [Algebra K E] [FiniteDimensional K E]

/-- Transfer the exact finite affine blocking number through a line-incidence equivalence. -/
theorem exact_graph_minimum_of_reduction (f : E → E)
    (reduce : ∀ S : Set E, GraphHits f S ↔ HyperplaneHits K S) :
    IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧ GraphHits f (S : Set E)}
      ((Fintype.card K - 1) * FiniteDimensional.finrank K E + 1) := by
  classical
  let b := FiniteDimensional.finBasis K E
  have lb (S : Finset E) (hs : GraphHits f (S : Set E)) :
      (Fintype.card K - 1) * FiniteDimensional.finrank K E + 1 ≤ S.card := by
    obtain ⟨x, hx⟩ := hs 0 0
    have hne : S.Nonempty := ⟨_, hx⟩
    simpa using lower_of_hyperplaneHits b S hne ((reduce _).mp hs)
  obtain ⟨S, hsize, hhit⟩ := exists_hyperplaneHits_le b
  have hs := (reduce (S : Set E)).mpr hhit
  refine ⟨⟨S, le_antisymm (by simpa using hsize) (lb S hs), hs⟩, ?_⟩
  rintro _ ⟨T, rfl, ht⟩
  exact lb T ht

/-- For the graph of an automorphism over its fixed field, this is the genuine
minimum: a witness exists and all finite translation parameter sets obey the bound. -/
theorem exact_graph_minimum (σ : E ≃ₐ[K] E)
    (hfix : ∀ x : E, σ x = x ↔ ∃ k : K, algebraMap K E k = x) :
    IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧ GraphHits σ (S : Set E)}
      ((Fintype.card K - 1) * FiniteDimensional.finrank K E + 1) :=
  exact_graph_minimum_of_reduction σ
    (graphHits_iff_hyperplaneHits σ fun x hx => (hfix x).mp hx)

/-- The same minimum holds for any scattered linear map. -/
theorem exact_scattered_minimum (T : E →ₗ[K] E) (hT : Scattered T) :
    IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧ GraphHits T (S : Set E)}
      ((Fintype.card K - 1) * FiniteDimensional.finrank K E + 1) :=
  exact_graph_minimum_of_reduction T (scattered_graphHits_iff T hT)

#print axioms exact_graph_minimum
#print axioms exact_scattered_minimum
end BlockingCurves

