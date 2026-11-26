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

end CubicCertificate
