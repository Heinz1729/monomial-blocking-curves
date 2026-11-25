import F8Example
import FieldTransport
import Mathlib.Algebra.Field.MinimalAxioms

namespace CubicFieldExample
open BlockingCurves

/-- The field carrier has its own arithmetic rather than the residue arithmetic on Fin 8. -/
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
private def inverseBits (a : E) : E := ((elems.find? fun b => mul a b == 1).getD 0)
instance : Inv Bits := ⟨fun a => ⟨inverseBits a.val⟩⟩

instance : Field Bits := Field.ofMinimalAxioms Bits
  (fun a b c => bitsEquiv.injective (arithmetic.2.2.1 a.val b.val c.val).1)
  (fun a => bitsEquiv.injective ((arithmetic.2.1 _ _).1.trans (arithmetic.1 a.val).2.1))
  (fun a => bitsEquiv.injective (arithmetic.1 a.val).1)
  (fun a b c => bitsEquiv.injective (arithmetic.2.2.1 a.val b.val c.val).2.1)
  (fun a b => bitsEquiv.injective (arithmetic.2.1 a.val b.val).2)
  (fun a => bitsEquiv.injective ((arithmetic.2.1 _ _).2.trans (arithmetic.1 a.val).2.2))
  (fun ⟨a⟩ ha => bitsEquiv.injective
    ((show ∀ x : E, x ≠ 0 → mul x (inverseBits x) = 1 by decide) a
      (fun h => ha (congrArg Bits.mk h))))
  (by rfl)
  (fun a b c => bitsEquiv.injective (arithmetic.2.2.1 a.val b.val c.val).2.2)
  ⟨0, 1, by decide⟩

def decoded (S : Mask) : Finset Bits := Finset.univ.filter fun x => has S x.val = true

@[simp] theorem mem_decoded (S : Mask) (x : Bits) :
    x ∈ decoded S ↔ has S x.val = true := by simp [decoded]

private theorem mem_elems : ∀ a : E, a ∈ elems := by decide

theorem blocks_iff_projective (S : Mask) :
    blocks S = true ↔ ProjectiveBlocks 2 (decoded S : Set Bits) := by
  rw [projectiveBlocks_iff_graphHits (by decide)]
  simp only [blocks, List.all_eq_true, List.any_eq_true, mem_elems, true_implies, true_and]
  have calcBits (m b x : Bits) :
      (x^2 - m*x - b).val = add (mul x.val x.val) (add (mul m.val x.val) b.val) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, pow_two]
    exact (arithmetic.2.2.1 _ _ _).1
  constructor
  · intro h m b
    obtain ⟨x, hx⟩ := h m.val b.val
    refine ⟨⟨x⟩, (mem_decoded _ _).2 ?_⟩
    simpa only [calcBits] using hx
  · intro h m b
    obtain ⟨x, hx⟩ := h ⟨m⟩ ⟨b⟩
    refine ⟨x.val, ?_⟩
    simpa only [calcBits] using (mem_decoded S _).1 hx

set_option maxRecDepth 4096 in
theorem decoded_card : ∀ s : Mask, (decoded s).card = size s := by decide

noncomputable def fieldEquiv : Bits ≃+* GaloisField 2 3 :=
  FiniteField.ringEquivOfCardEq (by
    rw [GaloisField.card 2 3 (by decide), Fintype.card_congr bitsEquiv]
    decide)

theorem blocks_iff_galoisField (S : Mask) :
    blocks S = true ↔ ProjectiveBlocks 2 (fieldEquiv '' (decoded S : Set Bits)) := by
  rw [projectiveBlocks_image_iff fieldEquiv (by decide), blocks_iff_projective]

theorem decoded_bijective : Function.Bijective decoded := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro m n he
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · let x : Bits := ⟨⟨i, hi⟩⟩
      apply Bool.eq_iff_iff.mpr
      change has m x.val = true ↔ has n x.val = true
      rw [← mem_decoded, ← mem_decoded, he]
    · have hp : 2^8 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le m.isLt hp),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le n.isLt hp)]
  · rw [Fintype.card_finset, Fintype.card_congr bitsEquiv]
    decide

noncomputable def parameterEquiv : Mask ≃ Finset (GaloisField 2 3) :=
  (Equiv.ofBijective decoded decoded_bijective).trans fieldEquiv.toEquiv.finsetCongr

theorem parameterEquiv_card (s : Mask) : (parameterEquiv s).card = size s :=
  (Finset.card_map _).trans (decoded_card s)

theorem blocks_iff_parameterEquiv (s : Mask) :
    blocks s = true ↔ ProjectiveBlocks 2 (parameterEquiv s : Set (GaloisField 2 3)) := by
  change _ ↔ ProjectiveBlocks 2
    (((decoded s).map fieldEquiv.toEquiv.toEmbedding) : Set (GaloisField 2 3))
  rw [Finset.coe_map]
  exact blocks_iff_galoisField s

/-- The 56 optimal masks enumerate distinct geometric parameter sets and exhaust them. -/
theorem projective_optimal_count :
    Nat.card {S : Finset (GaloisField 2 3) // S.card = 4 ∧
      ProjectiveBlocks 2 (S : Set (GaloisField 2 3))} = 56 := by
  let p := fun s : Mask => Nat.beq (size s) 4 && blocks s
  have equiv := parameterEquiv.subtypeEquiv (p := fun s => p s = true)
    (q := fun S : Finset (GaloisField 2 3) => S.card = 4 ∧ ProjectiveBlocks 2 (S : Set (GaloisField 2 3)))
    (fun s => by simp [p, parameterEquiv_card, ← blocks_iff_parameterEquiv])
  rw [← Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hm : masks = List.finRange 256 := by
    unfold masks
    rw [Array.toList_eq]
    apply List.ext_get
    · rw [List.length_finRange]
      exact Array.size_ofFn _
    · intro i hi hj
      rw [← Array.getElem_eq_data_get, Array.getElem_ofFn, List.get_finRange]
      rfl
  have hmask : masks.toFinset = Finset.univ := by ext; simp [hm]
  have hn : masks.Nodup := hm ▸ List.nodup_finRange 256
  calc
    _ = (masks.toFinset.filter (fun s => p s = true)).card := by rw [hmask]
    _ = ((masks.filter p).toFinset).card := congrArg Finset.card (List.toFinset_filter masks p).symm
    _ = (masks.filter p).length := List.toFinset_card_of_nodup (hn.filter p)
    _ = 56 := optimal_sets

end CubicFieldExample
