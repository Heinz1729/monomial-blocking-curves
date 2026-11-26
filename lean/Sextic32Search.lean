import Sextic32
import Mathlib.Data.List.Basic

namespace Sextic32

def pool : List E := elems.filter fun x => x != 0 && x != 1

/-- Check a size-k sublist of the remaining pool by branching on its first element.
The recursion depth is bounded by 30 even though there are 27,405 normalized six-sets. -/
def allMiss : List E → Nat → List E → Bool
  | _, 0, picked => !hits picked
  | [], _+1, _ => true
  | a::xs, k+1, picked => allMiss xs k (picked ++ [a]) && allMiss xs (k+1) picked

theorem allMiss_sound {xs ys : List E} (hs : List.Sublist ys xs) (picked : List E)
    (h : allMiss xs ys.length picked = true) : hits (picked ++ ys) = false := by
  induction hs generalizing picked with
  | slnil => simpa [allMiss] using h
  | @cons ys xs a hs ih =>
    cases ys with
    | nil => simpa [allMiss] using h
    | cons y ys => exact ih picked ((Bool.and_eq_true_iff _ _).mp h).2
  | cons₂ a _ ih =>
    simpa using ih (picked ++ [a]) ((Bool.and_eq_true_iff _ _).mp h).1

private theorem prepend_miss {a : E} {xs : List E}
    (first : allMiss xs 3 [a] = true) (rest : allMiss xs 4 [] = true) :
    allMiss (a :: xs) 4 [] = true := by
  change (allMiss xs 3 [a] && allMiss xs 4 []) = true
  simp only [first, rest, Bool.and_self]

/- Separate kernel commands release the reduction cache after each first element.
The largest slice contains only binom(29,3) candidates. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem first2 : allMiss (pool.drop 1) 3 [2] = true := by decide
private theorem first3 : allMiss (pool.drop 2) 3 [3] = true := by decide
private theorem first4 : allMiss (pool.drop 3) 3 [4] = true := by decide
private theorem first5 : allMiss (pool.drop 4) 3 [5] = true := by decide
private theorem first6 : allMiss (pool.drop 5) 3 [6] = true := by decide
private theorem first7 : allMiss (pool.drop 6) 3 [7] = true := by decide
private theorem first8 : allMiss (pool.drop 7) 3 [8] = true := by decide
private theorem first9 : allMiss (pool.drop 8) 3 [9] = true := by decide
private theorem first10 : allMiss (pool.drop 9) 3 [10] = true := by decide
private theorem first11 : allMiss (pool.drop 10) 3 [11] = true := by decide
private theorem first12 : allMiss (pool.drop 11) 3 [12] = true := by decide
private theorem first13 : allMiss (pool.drop 12) 3 [13] = true := by decide
private theorem first14 : allMiss (pool.drop 13) 3 [14] = true := by decide
private theorem first15 : allMiss (pool.drop 14) 3 [15] = true := by decide
private theorem first16 : allMiss (pool.drop 15) 3 [16] = true := by decide
private theorem first17 : allMiss (pool.drop 16) 3 [17] = true := by decide
private theorem first18 : allMiss (pool.drop 17) 3 [18] = true := by decide
private theorem first19 : allMiss (pool.drop 18) 3 [19] = true := by decide
private theorem first20 : allMiss (pool.drop 19) 3 [20] = true := by decide
private theorem first21 : allMiss (pool.drop 20) 3 [21] = true := by decide
private theorem first22 : allMiss (pool.drop 21) 3 [22] = true := by decide
private theorem first23 : allMiss (pool.drop 22) 3 [23] = true := by decide
private theorem first24 : allMiss (pool.drop 23) 3 [24] = true := by decide
private theorem first25 : allMiss (pool.drop 24) 3 [25] = true := by decide
private theorem first26 : allMiss (pool.drop 25) 3 [26] = true := by decide
private theorem first27 : allMiss (pool.drop 26) 3 [27] = true := by decide
private theorem first28 : allMiss (pool.drop 27) 3 [28] = true := by decide

theorem no_normalized_six : allMiss pool 4 [] = true := by
  apply prepend_miss first2
  apply prepend_miss first3
  apply prepend_miss first4
  apply prepend_miss first5
  apply prepend_miss first6
  apply prepend_miss first7
  apply prepend_miss first8
  apply prepend_miss first9
  apply prepend_miss first10
  apply prepend_miss first11
  apply prepend_miss first12
  apply prepend_miss first13
  apply prepend_miss first14
  apply prepend_miss first15
  apply prepend_miss first16
  apply prepend_miss first17
  apply prepend_miss first18
  apply prepend_miss first19
  apply prepend_miss first20
  apply prepend_miss first21
  apply prepend_miss first22
  apply prepend_miss first23
  apply prepend_miss first24
  apply prepend_miss first25
  apply prepend_miss first26
  apply prepend_miss first27
  apply prepend_miss first28
  decide

end Sextic32
