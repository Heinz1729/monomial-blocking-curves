import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Independent choices in additive cosets and intersections of two norm circles. -/
namespace BlockingCurves.NormFibreSampling

open scoped BigOperators

/-- A transversal meets every target if the sum of the exact bad tuple counts
is smaller than the full product space. Coordinates may have different targets. -/
theorem exists_transversal {I k J : Type*} [Fintype I] [Fintype k] [Fintype J]
    (row : J → I → Finset k)
    (h : (∑ j, ∏ i, (Fintype.card k - (row j i).card)) <
      Fintype.card k ^ Fintype.card I) :
    ∃ u : I → k, ∀ j, ∃ i, u i ∈ row j i := by
  classical
  let bad (j : J) := Fintype.piFinset (fun i => (row j i)ᶜ)
  let U := Finset.univ.biUnion bad
  have hbad (j : J) : (bad j).card = ∏ i, (Fintype.card k - (row j i).card) := by
    simp [bad, Finset.card_compl]
  have hU : U.card < Fintype.card (I → k) := by
    calc
      U.card ≤ ∑ j, (bad j).card := Finset.card_biUnion_le
      _ < Fintype.card (I → k) := by simpa [hbad] using h
  obtain ⟨u, hu⟩ : ∃ u, u ∉ U := by
    by_contra! hall
    rw [Finset.eq_univ_of_forall hall, Finset.card_univ] at hU
    exact (lt_irrefl _ hU)
  refine ⟨u, fun j => ?_⟩
  by_contra! hn
  apply hu
  apply Finset.mem_biUnion.mpr
  exact ⟨j, Finset.mem_univ _, Fintype.mem_piFinset.mpr (fun i => Finset.mem_compl.mpr (hn i))⟩

/-- A bound on the mean number of misses per coordinate gives the
corresponding power bound on the number of bad tuples. -/
theorem prod_le_mean_pow {I : Type*} [Fintype I] [Nonempty I] (c : I → ℕ) :
    (∏ i, (c i : ℝ)) ≤ ((∑ i, (c i : ℝ)) / Fintype.card I) ^ Fintype.card I := by
  classical
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset I)
    (fun _ => (1 : ℝ)) (fun i => (c i : ℝ)) (by intros; norm_num)
    (by simpa using hcard) (by intros; positivity)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, one_mul] at h
  have hp := pow_le_pow_left (Real.rpow_nonneg (Finset.prod_nonneg (fun _ _ => by positivity)) _) h
    (Fintype.card I)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (Finset.prod_nonneg (fun _ _ => by positivity)),
    inv_mul_cancel hcard.ne', Real.rpow_one] at hp

end BlockingCurves.NormFibreSampling
