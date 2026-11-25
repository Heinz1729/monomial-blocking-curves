import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Set.Image

/-! Source-facing specification. Asgarli–Ghioca–Yip, arXiv:2510.15332v2,
§5, equations (5.3)–(5.4) and Question 5.4. This file imports no project proofs. -/

namespace AsgarliGhiocaYip

/-- Every polynomial value set from (5.3) meets the parameter set. -/
def hitsValueSets {F : Type*} [Field F] (d : ℕ) (S : Set F) : Prop :=
  ∀ u v : F, (S ∩ Set.range (fun x : F => x ^ d + u * x + v)).Nonempty

end AsgarliGhiocaYip
