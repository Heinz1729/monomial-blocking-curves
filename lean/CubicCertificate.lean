import Lean

/-! Reindex kernel computations before reducing them. Each inner test touches
only a single slope or a single pair of fixed coordinates. -/

namespace CubicCertificate

private theorem filter_append (xs ys : List α) (p : α → Bool) :
    (xs ++ ys).filter p = xs.filter p ++ ys.filter p := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [List.filter, h, ih]

theorem filter_bind (xs : List α) (f : α → List β) (p : β → Bool) :
    (xs.bind f).filter p = xs.bind (fun x => (f x).filter p) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.cons_bind, filter_append, ih, List.cons_bind]

theorem bind_blocks (xs : List α) (f : α → List β) (g : β → List γ) :
    (xs.bind f).bind g = xs.bind (fun x => (f x).bind g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.cons_bind, List.append_bind, ih, List.cons_bind]

def count (xs : List α) (f : α → Nat) : Nat :=
  xs.foldr (fun x n => f x+n) 0

theorem length_bind (xs : List α) (f : α → List β) :
    (xs.bind f).length = count xs (fun x => (f x).length) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.cons_bind, List.length_append, ih]; rfl

private theorem count_append (xs ys : List α) (f : α → Nat) :
    count (xs ++ ys) f = count xs f + count ys f := by
  induction xs with
  | nil => simp [count]
  | cons a xs ih => change f a + count (xs ++ ys) f = (f a + count xs f) + count ys f
                    rw [ih, Nat.add_assoc]

theorem count_bind (xs : List α) (f : α → List β) (g : β → Nat) :
    count (xs.bind f) g = count xs (fun x => count (f x) g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.cons_bind, count_append, ih]; rfl

/-- Consecutive input slices. Each certificate also checks that concatenating
the slices recovers the entire input in its original order. -/
def blocks (width number : Nat) (xs : List α) : List (List α) :=
  (List.range number).map fun i => (xs.drop (i*width)).take width

/-- Slice the expected answer at the recorded per-block output lengths.
The verifier separately checks the concatenation against the whole answer. -/
def splitSizes : List Nat → List α → List (List α)
  | [], _ => []
  | n :: ns, xs => xs.take n :: splitSizes ns (xs.drop n)

/-- Each leaf compares only the output of one slice with its expected rows. -/
inductive CheckedBind (f : α → List β) : List (List α) → List (List β) → Prop where
  | nil : CheckedBind f [] []
  | cons {xs parts ys outputs} : xs.bind f = ys → CheckedBind f parts outputs →
      CheckedBind f (xs :: parts) (ys :: outputs)

theorem bind_checked {f : α → List β} {xs parts ys outputs}
    (cover : parts.join = xs) (h : CheckedBind f parts outputs)
    (result : outputs.join = ys) : xs.bind f = ys := by
  subst xs
  subst ys
  induction h with
  | nil => rfl
  | cons eq _ ih =>
    simp only [List.join, List.append_bind]
    rw [eq, ih]

inductive CheckedCount (f : α → Nat) : List (List α) → List Nat → Prop where
  | nil : CheckedCount f [] []
  | cons {xs parts n totals} : count xs f = n → CheckedCount f parts totals →
      CheckedCount f (xs :: parts) (n :: totals)

theorem count_checked {f : α → Nat} {xs parts n totals}
    (cover : parts.join = xs) (h : CheckedCount f parts totals)
    (result : count totals id = n) : count xs f = n := by
  subst xs
  subst n
  induction h with
  | nil => rfl
  | cons eq _ ih =>
    simp only [List.join, count_append]
    rw [eq, ih]
    rfl

/-- Construct one kernel proof per slice, then use only the structural glue. -/
macro "verify_bind_blocks" : tactic =>
  `(tactic| repeat' first | exact CubicCertificate.CheckedBind.nil |
      refine CubicCertificate.CheckedBind.cons (by decide) ?_)

macro "verify_count_blocks" : tactic =>
  `(tactic| repeat' first | exact CubicCertificate.CheckedCount.nil |
      refine CubicCertificate.CheckedCount.cons (by decide) ?_)

end CubicCertificate
