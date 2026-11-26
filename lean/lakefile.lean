import Lake
open Lake DSL

package blockingCurves

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib BlockingCurves where
  roots := #[`BlockingCurves, `GeneralGeometry, `UpperBound, `LowerBound, `MainResult,
    `Projective, `Frobenius, `Paper, `F8Example, `Cubic41, `Cubic41Semantics,
    `CubicSymmetry, `CubicGlobal, `CubicOrbit, `Cubic47, `Cubic47Semantics,
    `Cubic47Symmetry, `Cubic47Global, `Cubic47Orbit, `CubicSlope, `ProblemStatement,
    `StatementComparison, `GeometricIrreducibility, `ScatteredComparison, `NontrivialPencil,
    `FieldTransport, `PrimeFieldInstances, `F8Semantics, `CubicCertificate, `CubicPairCount,
    `CubicAsymptotics, `CubicCocycles, `CubicCovering, `CubicValueSet, `CubicCharacters,
    `CubicMonodromy, `CubicUnsigned, `CubicSurfaceTrace, `CubicCurveTrace,
    `CubicUnramified, `CubicRationalRoots,
    `CubicAlteration, `CubicDoubleMiss, `CubicAlterationSize, `CubicRepairChart,
    `CubicRepairDegree, `CubicRepairPlaces, `CubicRepairBranch, `CubicPoleFibre, `CubicPoleScalars,
    `CubicPoleDegree, `CubicFiniteFibres, `CubicStageFields, `CubicCompositumRR, `CubicRationalGenus,
    `CubicGenusTransport, `CubicZetaPoints, `CubicRepairGeometry, `CubicLogLog,
    `FrobeniusCoset,
    `Sextic32, `Sextic32Geometry, `Sextic32Search, `Sextic32Global]
