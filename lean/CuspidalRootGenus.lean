import CuspidalRootInertia
import CubicGenusTransport

/-! Genus of the rational subfields inside a compositum of translated cusp
covers. The parameter is a polynomial in any single sheet, including in wild
characteristic. The constant-field structures throughout are the restrictions of
the given embedding of the parameter field. -/
namespace BlockingCurves.CuspidalTower
open IntermediateField Polynomial FiniteDimensional CuspidalGeneral
noncomputable section
universe u
variable {k M : Type u} [Field k] [Field M] [Algebra (RatFunc k) M]

private instance coefficientAlgebra (E : IntermediateField (RatFunc k) M) : Algebra k E :=
  ((algebraMap (RatFunc k) E).comp RatFunc.C).toAlgebra

abbrev fieldForms (E : IntermediateField (RatFunc k) M) := CubicRationalGenus.regularForms k E
abbrev fieldGenus (E : IntermediateField (RatFunc k) M) := CubicRationalGenus.genus k E

theorem base_rational : Nonempty (RatFunc k ≃ₐ[k] (⊥ : IntermediateField (RatFunc k) M)) :=
  ⟨AlgEquiv.ofRingEquiv (f := (IntermediateField.botEquiv (RatFunc k) M).symm.toRingEquiv)
    (by intro c; rfl)⟩

theorem base_genus : fieldGenus (⊥ : IntermediateField (RatFunc k) M) = 0 :=
  CubicRationalGenus.rational_genus_zero (base_rational (M := M)).some

theorem base_forms_finite : FiniteDimensional k (fieldForms (⊥ : IntermediateField (RatFunc k) M)) :=
  CubicRationalGenus.rational_finiteDimensional (base_rational (M := M)).some

/-- If x is an actual root over the parameter line, k(b)(x) is rational
over k. This uses b = x^d - a*x^(d-1) - u and needs no separability input. -/
theorem single_root_rational {d : ℕ} {a u : k} {x : M}
    (hx : x ∈ (cuspCoordinate d a u).rootSet M) :
    Nonempty (RatFunc k ≃ₐ[k] adjoin (RatFunc k) ({x} : Set M)) := by
  have he := (mem_rootSet.mp hx).2
  simp only [cuspCoordinate, lineFibre, map_sub, map_add, map_mul, map_pow,
    aeval_X, aeval_C, sub_eq_zero] at he
  obtain ⟨e,h⟩ := CubicRepairPlaces.rational_single_of_power_equation x d (d-1) a u
    (by simpa only [map_add] using he)
  exact ⟨AlgEquiv.ofRingEquiv (f := e) (fun c => Subtype.ext (h c))⟩

theorem single_root_forms_eq_bot {d : ℕ} {a u : k} {x : M}
    (hx : x ∈ (cuspCoordinate d a u).rootSet M) :
    fieldForms (adjoin (RatFunc k) ({x} : Set M)) = ⊥ :=
  CubicRationalGenus.regularForms_eq_bot (single_root_rational hx).some

theorem single_root_genus {d : ℕ} {a u : k} {x : M}
    (hx : x ∈ (cuspCoordinate d a u).rootSet M) :
    fieldGenus (adjoin (RatFunc k) ({x} : Set M)) = 0 :=
  CubicRationalGenus.rational_genus_zero (single_root_rational hx).some

theorem single_root_forms_finite {d : ℕ} {a u : k} {x : M}
    (hx : x ∈ (cuspCoordinate d a u).rootSet M) :
    FiniteDimensional k (fieldForms (adjoin (RatFunc k) ({x} : Set M))) :=
  CubicRationalGenus.rational_finiteDimensional (single_root_rational hx).some

/-- A cardinal version of the classical genus bound supplies finite
dimensionality as well as the numerical bound on genus. -/
theorem field_genus_of_rank_bound (E : IntermediateField (RatFunc k) M) {b : ℕ}
    (h : Module.rank k (fieldForms E) ≤ (b : Cardinal)) :
    FiniteDimensional k (fieldForms E) ∧ fieldGenus E ≤ b := by
  classical
  let basis := Basis.ofVectorSpace k (fieldForms E)
  letI := basis.fintypeIndexOfRankLtAleph0 (h.trans_lt (Cardinal.nat_lt_aleph0 _))
  letI := FiniteDimensional.of_fintype_basis basis
  rw [← FiniteDimensional.finrank_eq_rank'] at h
  exact ⟨inferInstance, Nat.cast_le.mp h⟩

def ambientGenus (k M : Type u) [Field k] [Field M] [Algebra (RatFunc k) M] : ℕ :=
    letI : Algebra k M := ((algebraMap (RatFunc k) M).comp RatFunc.C).toAlgebra
    CubicRationalGenus.genus k M

/-- Identifying the last intermediate field with the full compositum
preserves genus over the embedded constant field. -/
theorem fieldGenus_top : fieldGenus (⊤ : IntermediateField (RatFunc k) M) = ambientGenus k M := by
  letI : Algebra k M := ((algebraMap (RatFunc k) M).comp RatFunc.C).toAlgebra
  let e : (⊤ : IntermediateField (RatFunc k) M) ≃ₐ[RatFunc k] M := IntermediateField.topEquiv
  apply CubicRationalGenus.genus_congr (F := k)
  exact AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun c => e.commutes (RatFunc.C c))

end
end BlockingCurves.CuspidalTower
