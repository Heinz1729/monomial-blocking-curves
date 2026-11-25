import Cubic41Semantics
import Cubic47
import Mathlib.Data.List.Basic

/-! The certificate's bit masks and sorted tuple enumeration express the
literal incidence problem in residues modulo 47. -/
namespace CubicPencil47

theorem bit_mem (xs : List Nat) (j : Nat) : (maskOf xs).testBit j = true ↔ j ∈ xs :=
  CubicPencil41.bit_mem xs j

private theorem overlap (ys zs : List Nat) :
    (maskOf ys &&& maskOf zs) ≠ 0 ↔ ∃ j ∈ ys, j ∈ zs := by
  constructor
  · intro hn
    obtain ⟨j, hj⟩ := Nat.ne_zero_implies_bit_true hn
    rw [Nat.testBit_and, Bool.and_eq_true, bit_mem, bit_mem] at hj
    exact ⟨j, hj⟩
  · rintro ⟨j, hy, hz⟩ he
    have h : (maskOf ys &&& maskOf zs).testBit j = true := by
      rw [Nat.testBit_and, Bool.and_eq_true, bit_mem, bit_mem]
      exact ⟨hy, hz⟩
    simp [he] at h

private theorem row_overlap (m b : Nat) (ys : List Nat) :
    (maskOf (cubicValues m b) &&& maskOf ys) ≠ 0 ↔
      ∃ x ∈ residues, (x*x*x + m*x + b) % 47 ∈ ys := by
  rw [overlap]
  constructor
  · rintro ⟨j, hj, hy⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj
    exact ⟨x, hx, hy⟩
  · rintro ⟨x,hx,hy⟩
    exact ⟨_, List.mem_map.mpr ⟨x,hx,rfl⟩, hy⟩

/-- The optimized normalized test is equivalent to literal modular incidence. -/
theorem normalized_iff (extras : List Nat) :
    hitsRows (maskOf extras) = true ↔
      ∀ m ∈ residues, ∀ b ∈ residues, ∃ x ∈ residues,
        (x*x*x + m*x + b) % 47 ∈ 0 :: 1 :: extras := by
  unfold hitsRows
  rw [← rows_verified, List.all_eq_true]
  constructor
  · intro h m hm b hb
    let row := maskOf (cubicValues m b)
    have hr : row ∈ allRows := List.mem_bind.mpr ⟨m,hm,List.mem_map.mpr ⟨b,hb,rfl⟩⟩
    by_cases hbase : (row &&& 3) = 0
    · have hr' : row ∈ difficultRows := List.mem_filter.mpr ⟨hr, by simpa using hbase⟩
      have hn : (row &&& maskOf extras) ≠ 0 := by simpa using h row hr'
      obtain ⟨x,hx,hy⟩ := (row_overlap m b extras).mp hn
      exact ⟨x,hx,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)⟩
    · have hn : (row &&& maskOf [0,1]) ≠ 0 := hbase
      obtain ⟨x,hx,hy⟩ := (row_overlap m b [0,1]).mp hn
      refine ⟨x,hx,?_⟩
      simp at hy
      rcases hy with hy | hy <;> simp [hy]
  · intro h row hrow
    obtain ⟨hr,hbase⟩ := List.mem_filter.mp hrow
    obtain ⟨m,hm,hmb⟩ := List.mem_bind.mp hr
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hmb
    have hn : ¬ (∃ x ∈ residues, (x*x*x+m*x+b)%47 ∈ [0,1]) := by
      intro hx
      apply (row_overlap m b [0,1]).mpr hx
      simpa using hbase
    obtain ⟨x,hx,hy⟩ := h m hm b hb
    have he : (x*x*x+m*x+b)%47 ∈ extras := by
      simp only [List.mem_cons] at hy
      rcases hy with hy | hy | hy
      · exact False.elim (hn ⟨x,hx,by simp [hy]⟩)
      · exact False.elim (hn ⟨x,hx,by simp [hy]⟩)
      · exact hy
    simpa using (row_overlap m b extras).mpr ⟨x,hx,he⟩

private theorem mem_extra {u : Nat} (hu : 2 ≤ u) (hu' : u < 47) : u ∈ extra := by
  apply List.mem_map.mpr
  exact ⟨u - 2, List.mem_range.mpr (by omega), by omega⟩

theorem no_four_witness {u v : Nat} (hu : 2 ≤ u) (huv : u < v) (hv : v < 47) :
    ¬ hitsRows (maskOf [u,v]) = true := by
  intro h
  have hp : (u,v) ∈ pairs := by
    apply List.mem_bind.mpr
    exact ⟨u,mem_extra hu (by omega),List.mem_map.mpr
      ⟨v,List.mem_filter.mpr ⟨mem_extra (by omega) hv,by simpa using huv⟩,rfl⟩⟩
  have hsol : (u,v) ∈ fourSolutions := List.mem_filter.mpr ⟨hp,h⟩
  simp [no_normalized_four] at hsol

theorem five_witness : hitsRows (maskOf [3,15,33]) = true := by decide

theorem five_witness_iff {u v w : Nat} (hu : 2 ≤ u) (huv : u < v) (hvw : v < w)
    (hw : w < 47) : hitsRows (maskOf [u,v,w]) = true ↔
      (u,v,w) ∈ representativeTriples := by
  have hp : (u,v) ∈ pairs := by
    exact List.mem_bind.mpr ⟨u,mem_extra hu (by omega),List.mem_map.mpr
      ⟨v,List.mem_filter.mpr ⟨mem_extra (by omega) (by omega),by simpa using huv⟩,rfl⟩⟩
  have ht : (u,v,w) ∈ triples := by
    exact List.mem_bind.mpr ⟨(u,v),hp,List.mem_map.mpr
      ⟨w,List.mem_filter.mpr ⟨mem_extra (by omega) hw,by simpa using hvw⟩,rfl⟩⟩
  rw [← classify_normalized_five]
  exact ⟨fun h => List.mem_filter.mpr ⟨ht,h⟩, fun h => (List.mem_filter.mp h).2⟩

#print axioms normalized_iff
#print axioms no_four_witness
#print axioms five_witness
#print axioms five_witness_iff

end CubicPencil47
