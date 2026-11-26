import Sextic32
import Cubic41Semantics
import FieldTransport
import Mathlib.Algebra.Field.MinimalAxioms

namespace Sextic32
open BlockingCurves

/-- Distinguish the finite-field arithmetic from the modular arithmetic on Fin 32. -/
structure Bits where
  val : E
  deriving DecidableEq

def bitsEquiv : Bits ≃ E := ⟨Bits.val, Bits.mk, fun _ => rfl, fun _ => rfl⟩
instance : Fintype Bits := Fintype.ofEquiv E bitsEquiv.symm
instance : Zero Bits := ⟨⟨0⟩⟩
instance : One Bits := ⟨⟨1⟩⟩
instance : Add Bits := ⟨fun a b => ⟨add a.val b.val⟩⟩
instance : Mul Bits := ⟨fun a b => ⟨mul a.val b.val⟩⟩
instance : Neg Bits := ⟨id⟩
instance : Inv Bits := ⟨fun a => ⟨inv a.val⟩⟩
instance : Field Bits := Field.ofMinimalAxioms Bits
  (fun a b c => bitsEquiv.injective (arithmetic.2.2.1 a.val b.val c.val).1)
  (fun a => bitsEquiv.injective ((arithmetic.2.1 _ _).1.trans (arithmetic.1 a.val).2.1))
  (fun a => bitsEquiv.injective (arithmetic.1 a.val).1)
  (fun a b c => bitsEquiv.injective (arithmetic.2.2.1 a.val b.val c.val).2.1)
  (fun a b => bitsEquiv.injective (arithmetic.2.1 a.val b.val).2)
  (fun a => bitsEquiv.injective ((arithmetic.2.1 _ _).2.trans (arithmetic.1 a.val).2.2))
  (fun ⟨a⟩ ha => bitsEquiv.injective (arithmetic.2.2.2 a (fun h => ha (congrArg Bits.mk h))))
  (by rfl)
  (fun a b c => bitsEquiv.injective (arithmetic.2.2.1 a.val b.val c.val).2.2)
  ⟨0, 1, by decide⟩

private theorem mem_elems : ∀ a : E, a ∈ elems := by decide

private theorem mask_eq (xs : List E) : mask xs = CubicPencil41.maskOf (xs.map Fin.val) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (fun n : Nat => 1 <<< x.val ||| n) ih

private theorem overlap (xs ys : List E) :
    (mask xs &&& mask ys) ≠ 0 ↔ ∃ x ∈ xs, x ∈ ys := by
  simp only [mask_eq]
  constructor
  · intro hn
    obtain ⟨j,hj⟩ := Nat.ne_zero_implies_bit_true hn
    rw [Nat.testBit_and, Bool.and_eq_true, CubicPencil41.bit_mem, CubicPencil41.bit_mem] at hj
    obtain ⟨x,hx,hr⟩ := List.mem_map.mp hj.1
    obtain ⟨y,hy,hs⟩ := List.mem_map.mp hj.2
    exact ⟨x,hx,(Fin.ext (hr.trans hs.symm)) ▸ hy⟩
  · rintro ⟨x,hx,hy⟩ he
    have hb : (CubicPencil41.maskOf (xs.map Fin.val) &&&
        CubicPencil41.maskOf (ys.map Fin.val)).testBit x.val = true := by
      rw [Nat.testBit_and, Bool.and_eq_true, CubicPencil41.bit_mem, CubicPencil41.bit_mem]
      exact ⟨List.mem_map_of_mem _ hx, List.mem_map_of_mem _ hy⟩
    simp [he] at hb

private theorem row_overlap (m b : E) (ys : List E) :
    (mask (elems.map (value m b)) &&& mask ys) ≠ 0 ↔ ∃ x : E, value m b x ∈ ys := by
  rw [overlap]
  constructor
  · rintro ⟨_, hy, hz⟩
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
    exact ⟨x,hz⟩
  · rintro ⟨x,hx⟩
    exact ⟨_,List.mem_map_of_mem _ (mem_elems x),hx⟩

private theorem raw_hits (ys : List E) :
    hits ys = true ↔ ∀ m b : E, ∃ x : E, value m b x ∈ 0 :: 1 :: ys := by
  unfold hits
  rw [← rows_verified, List.all_eq_true]
  constructor
  · intro h m b
    let r := mask (elems.map (value m b))
    have hm : r ∈ lineRows := List.mem_bind.mpr ⟨m,mem_elems m,
      List.mem_map.mpr ⟨b, mem_elems b, rfl⟩⟩
    by_cases hb : r &&& 3 = 0
    · have hc := h r (List.mem_filter.mpr ⟨hm, by simpa using hb⟩)
      obtain ⟨x,hx⟩ := (row_overlap m b ys).1 (by simpa using hc)
      exact ⟨x,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)⟩
    · obtain ⟨x,hx⟩ := (row_overlap m b [0,1]).1 hb
      refine ⟨x, ?_⟩
      rcases (by simpa using hx : value m b x = 0 ∨ value m b x = 1) with h0 | h1
      · simp [h0]
      · simp [h1]
  · intro h r hr
    obtain ⟨hrow,hbase⟩ := List.mem_filter.mp hr
    obtain ⟨m,_,hm⟩ := List.mem_bind.mp hrow
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hm
    obtain ⟨x,hx⟩ := h m b
    have hx' : value m b x ∈ ys := by
      by_contra hy
      have h01 : value m b x ∈ ([0,1] : List E) := by simpa [hy] using hx
      have he := (row_overlap m b [0,1]).2 ⟨x,h01⟩
      exact he (by simpa using hbase)
    simpa using (row_overlap m b ys).2 ⟨x,hx'⟩

def params (ys : List E) : Finset Bits := (ys.map Bits.mk).toFinset

@[simp] theorem mem_params (x : Bits) (ys : List E) : x ∈ params ys ↔ x.val ∈ ys := by
  cases x
  simp [params]

theorem hits_iff_projective (ys : List E) :
    hits ys = true ↔ ProjectiveBlocks 6 (params (0 :: 1 :: ys) : Set Bits) := by
  rw [projectiveBlocks_iff_graphHits (by decide), raw_hits]
  have hv (m b x : Bits) : (x^6-m*x-b).val = value m.val b.val x.val := by
    rw [show x^6 = (x*x*x)*(x*x*x) by ring, sub_eq_add_neg, sub_eq_add_neg]
    rfl
  constructor
  · intro h m b
    obtain ⟨x,hx⟩ := h m.val b.val
    exact ⟨⟨x⟩, (mem_params _ _).2 (by simpa only [hv] using hx)⟩
  · intro h m b
    obtain ⟨x,hx⟩ := h ⟨m⟩ ⟨b⟩
    exact ⟨x.val, by simpa only [hv] using (mem_params _ _).1 hx⟩

end Sextic32
