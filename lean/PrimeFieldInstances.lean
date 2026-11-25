import CubicGlobal
import Cubic47Global
import FieldTransport

namespace BlockingCurves

/-- The two prime-field enumerations on the same GaloisField interface as Theorem 1. -/
theorem cubic41_galoisField_minimum :
    IsLeast {r : ℕ | ∃ S : Finset (GaloisField 41 1), S.card = r ∧
      ProjectiveBlocks 3 (S : Set (GaloisField 41 1))} 5 :=
  projective_minimum_ringEquiv (GaloisField.equivZmodP 41).symm.toRingEquiv
    (by decide) Cubic41.projective_cubic_minimum

theorem cubic47_galoisField_minimum :
    IsLeast {r : ℕ | ∃ S : Finset (GaloisField 47 1), S.card = r ∧
      ProjectiveBlocks 3 (S : Set (GaloisField 47 1))} 5 :=
  projective_minimum_ringEquiv (GaloisField.equivZmodP 47).symm.toRingEquiv
    (by decide) Cubic47.projective_cubic_minimum

end BlockingCurves
