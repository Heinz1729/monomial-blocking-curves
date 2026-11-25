import Lean

/-! A standalone certificate in the quotient F₂[t]/(t³+t+1).
    Residues are the three coefficient bits, constant coefficient first. -/
namespace CubicFieldExample
abbrev E := Fin 8
abbrev Mask := Fin 256

def add (x y : E) : E := ⟨(x.val ^^^ y.val) % 8, Nat.mod_lt _ (by decide)⟩
def timesT (x : E) : E :=
  ⟨(((2*x.val) % 8) ^^^ (if x.val.testBit 2 then 3 else 0)) % 8,
       Nat.mod_lt _ (by decide)⟩
def mul (x y : E) : E :=
  add (if y.val.testBit 0 then x else 0)
    (add (if y.val.testBit 1 then timesT x else 0)
         (if y.val.testBit 2 then timesT (timesT x) else 0))
def has (S : Mask) (x : E) : Bool := S.val.testBit x.val
def elems : List E := (Array.ofFn id).toList
def size (S : Mask) : Nat := (elems.filter (has S)).length

/-- The nonvertical line y=mx+b meets a selected conic precisely when
    x²+mx+b is a selected translation parameter for some x. -/
def blocks (S : Mask) : Bool :=
  elems.all fun m => elems.all fun b =>
    elems.any fun x => has S (add (mul x x) (add (mul m x) b))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem arithmetic :
    (∀ x : E, add x x = 0 ∧ add x 0 = x ∧ mul x 1 = x) ∧
    (∀ x y : E, add x y = add y x ∧ mul x y = mul y x) ∧
    (∀ x y z : E, add (add x y) z = add x (add y z) ∧
       mul (mul x y) z = mul x (mul y z) ∧
       mul x (add y z) = add (mul x y) (mul x z)) ∧
    (∀ x : E, x ≠ 0 → (elems.any fun y => mul x y == 1) = true) := by decide

/-- The bits of 23 are 0,1,2,4, encoding 0,1,t,t². -/
theorem witness : size 23 = 4 ∧ blocks 23 = true := by decide

/-- All 256 subsets are represented by their eight membership bits. -/
theorem minimum : ∀ S : Mask, blocks S = true → 4 ≤ size S := by decide

def masks : List Mask := (Array.ofFn id).toList

theorem optimal_sets :
    (masks.filter fun S => (size S == 4) && blocks S).length = 56 := by decide

#print axioms arithmetic
#print axioms witness
#print axioms minimum
#print axioms optimal_sets
end CubicFieldExample

