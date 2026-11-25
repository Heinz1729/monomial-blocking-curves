import Lake
open Lake DSL

package blockingCurves

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib BlockingCurves where
  -- The kernel reduces lists of up to 47² cubic rows in the finite certificates.
  weakLeanArgs := #["--tstack=131072"]
  roots := #[`BlockingCurves, `GeneralGeometry, `UpperBound, `LowerBound, `MainResult,
    `Projective, `Frobenius, `Paper, `F8Example, `Cubic41, `Cubic41Semantics,
    `CubicSymmetry, `CubicGlobal, `CubicOrbit, `Cubic47, `Cubic47Semantics,
    `Cubic47Symmetry, `Cubic47Global, `Cubic47Orbit, `CubicSlope, `ProblemStatement,
    `StatementComparison, `GeometricIrreducibility, `ScatteredComparison, `NontrivialPencil,
    `FieldTransport, `PrimeFieldInstances, `F8Semantics]
