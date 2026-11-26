import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Source specification for Asgarli–Ghioca–Yip, arXiv:2510.15332v2,
Definition 1.1, Question 5.4 and equations (5.3)–(5.4).
https://arxiv.org/html/2510.15332v2

Read this file independently of the proofs. Coordinates 0, 1, 2 are X, Y, Z.
A point is a nonzero vector modulo scalar multiplication in mathlib's
projectivization. In the dual plane a triple of line coefficients is taken
modulo the same equivalence. Evaluation uses mathlib's representative `rep`;
the comparison theorems recover the usual equations on *any* representatives. -/

namespace AsgarliGhiocaYip

abbrev Plane (F : Type*) [Field F] := Projectivization F (Fin 3 → F)
abbrev DualPlane (F : Type*) [Field F] := Projectivization F (Fin 3 → F)
abbrev Form (F : Type*) [CommSemiring F] := MvPolynomial (Fin 3) F

variable {F : Type*} [Field F]

/-- The rational points of a line whose dual coordinates are [a:b:c]. -/
def linePoints (L : DualPlane F) : Set (Plane F) :=
  {P | L.rep 0 * P.rep 0 + L.rep 1 * P.rep 1 + L.rep 2 * P.rep 2 = 0}

/-- Rational zero set of a plane form. -/
def curvePoints (f : Form F) : Set (Plane F) := {P | MvPolynomial.eval P.rep f = 0}

def isBlocking (B : Set (Plane F)) : Prop := ∀ L : DualPlane F, (linePoints L ∩ B).Nonempty
def containsNoLine (B : Set (Plane F)) : Prop := ∀ L : DualPlane F, ¬ linePoints L ⊆ B

/-- Geometric and degree requirements on each component in Definition 1.1. -/
def admissible (d : ℕ) (f : Form F) : Prop :=
  1 < d ∧ f.IsHomogeneous d ∧ f.totalDegree = d ∧
    Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f)

/-- Definition 1.1, for a collection indexed by a finite type. -/
def isBlockingFamily {ι : Type*} [Finite ι] (deg : ι → ℕ) (f : ι → Form F) : Prop :=
  (∀ i, admissible (deg i) (f i)) ∧ isBlocking (⋃ i, curvePoints (f i))

/-- Question 5.4: the equation X^d − α Z^d = Y Z^(d−1). -/
noncomputable def pencilForm (d : ℕ) (α : F) : Form F :=
  MvPolynomial.X 0 ^ d - MvPolynomial.C α * MvPolynomial.X 2 ^ d -
    MvPolynomial.X 1 * MvPolynomial.X 2 ^ (d - 1)

def pencilPoints (d : ℕ) (S : Set F) : Set (Plane F) := ⋃ α : S, curvePoints (pencilForm d α.1)

/-- The number requested by Question 5.4, with Definition 1.1's geometric conditions. -/
def isPencilMinimum (F : Type*) [Field F] (d n : ℕ) : Prop :=
  IsLeast {r : ℕ | ∃ S : Finset F, S.card = r ∧
    isBlockingFamily (fun _ : S => d) (fun α : S => pencilForm d (α : F))} n

/-- Every polynomial value set from (5.3) meets the parameter set. -/
def hitsValueSets (d : ℕ) (S : Set F) : Prop :=
  ∀ u v : F, (S ∩ Set.range (fun x : F => x ^ d + u * x + v)).Nonempty

end AsgarliGhiocaYip
