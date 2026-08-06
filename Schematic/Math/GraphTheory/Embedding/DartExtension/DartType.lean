import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finite.Card
import Schematic.Math.GraphTheory.Embedding.Geometry

/-!
Generic dart extension type.

This ports the small `ecp_dart` datatype from `cfmap.v`: two fresh darts plus
the old dart set.  The concrete configuration constructors use this type when
adding an edge pair to a hypermap.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

/-- Extend a dart type by two distinguished fresh darts. -/
inductive ExtDart (α : Type u)
  | new
  | newEdge
  | old (a : α)
  deriving DecidableEq, Repr

namespace ExtDart

variable {α : Type u}

/-- Encode an extended dart as a nested option. -/
def encode : ExtDart α → Option (Option α)
  | new => none
  | newEdge => some none
  | old a => some (some a)

/-- Decode a nested option as an extended dart. -/
def decode : Option (Option α) → ExtDart α
  | none => new
  | some none => newEdge
  | some (some a) => old a

@[simp]
theorem decode_encode (x : ExtDart α) :
    decode (encode x) = x := by
  cases x <;> rfl

@[simp]
theorem encode_decode (x : Option (Option α)) :
    encode (decode x) = x := by
  cases x with
  | none => rfl
  | some x =>
      cases x <;> rfl

/-- Equivalence with a nested option type. -/
def equivOption : ExtDart α ≃ Option (Option α) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

instance [Fintype α] : Fintype (ExtDart α) :=
  Fintype.ofEquiv (Option (Option α)) equivOption.symm

theorem old_injective :
    Function.Injective (old : α → ExtDart α) := by
  intro a b h
  cases h
  rfl

theorem old_ne_new (a : α) :
    old a ≠ (new : ExtDart α) := by
  intro h
  cases h

theorem old_ne_newEdge (a : α) :
    old a ≠ (newEdge : ExtDart α) := by
  intro h
  cases h

theorem new_ne_newEdge :
    (new : ExtDart α) ≠ newEdge := by
  intro h
  cases h

theorem card [Fintype α] :
    Fintype.card (ExtDart α) = Fintype.card α + 2 := by
  rw [Fintype.card_congr equivOption]
  simp [Fintype.card_option, Nat.add_comm, Nat.add_left_comm]

namespace Perm

variable (σ : Equiv.Perm α)

/-- Extend a permutation to the old darts while swapping the two fresh darts.
This is the common edge permutation used by Gonthier's extension constructors. -/
def edge : Equiv.Perm (ExtDart α) where
  toFun
    | new => newEdge
    | newEdge => new
    | old a => old (σ a)
  invFun
    | new => newEdge
    | newEdge => new
    | old a => old (σ.symm a)
  left_inv := by
    intro x
    cases x <;> simp
  right_inv := by
    intro x
    cases x <;> simp

@[simp]
theorem edge_new :
    edge σ new = newEdge :=
  rfl

@[simp]
theorem edge_newEdge :
    edge σ newEdge = new :=
  rfl

@[simp]
theorem edge_old (a : α) :
    edge σ (old a) = old (σ a) :=
  rfl

/-- Extending a fixed-point-free involution preserves those properties. -/
theorem edge_plain
    (hσ : ∀ a : α, σ (σ a) = a ∧ σ a ≠ a) :
    ∀ x : ExtDart α, edge σ (edge σ x) = x ∧ edge σ x ≠ x := by
  intro x
  cases x with
  | new => exact ⟨rfl, new_ne_newEdge.symm⟩
  | newEdge => exact ⟨rfl, new_ne_newEdge⟩
  | old a =>
      exact ⟨congrArg old (hσ a).1, fun h => (hσ a).2 (old_injective h)⟩

end Perm

end ExtDart

end FourColor

end Schematic.Math.GraphTheory
