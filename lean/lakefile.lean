import Lake
open Lake DSL

package blockingCurves

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib BlockingCurves where
  roots := #[`BlockingCurves, `GeneralGeometry, `UpperBound, `LowerBound, `MainResult,
    `Projective, `Frobenius, `Paper, `F8Example, `Cubic41, `Cubic41Semantics,
    `CubicSymmetry, `CubicGlobal, `CubicOrbit]
