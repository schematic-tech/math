import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
The four colours used by the hypermap four-colour theorem development.

This mirrors the small finite colour type in Gonthier's `color.v`.  The
operation `add` is bitwise xor on two bits; it is used later for edge traces
and Kempe-chain normalisation.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

/-- The four colours, viewed as two-bit vectors. -/
inductive Color
  | zero
  | one
  | two
  | three
  deriving DecidableEq

instance : Fintype Color where
  elems := {Color.zero, Color.one, Color.two, Color.three}
  complete := by
    intro c
    cases c <;> simp

namespace Color

/-- Lower colour bit. -/
def bit0 : Color → Bool
  | zero => false
  | one => true
  | two => false
  | three => true

/-- Upper colour bit. -/
def bit1 : Color → Bool
  | zero => false
  | one => false
  | two => true
  | three => true

/-- Construct a colour from upper and lower bits. -/
def cons : Bool → Bool → Color
  | false, false => zero
  | false, true => one
  | true, false => two
  | true, true => three

/-- Bitwise xor on colours. -/
def add : Color → Color → Color
  | zero, c => c
  | one, zero => one
  | one, one => zero
  | one, two => three
  | one, three => two
  | two, zero => two
  | two, one => three
  | two, two => zero
  | two, three => one
  | three, zero => three
  | three, one => two
  | three, two => one
  | three, three => zero

instance : Add Color where
  add := add

@[simp]
theorem cons_bits (c : Color) :
    cons c.bit1 c.bit0 = c := by
  cases c <;> rfl

@[simp]
theorem bit1_cons (b1 b0 : Bool) :
    bit1 (cons b1 b0) = b1 := by
  cases b1 <;> cases b0 <;> rfl

@[simp]
theorem bit0_cons (b1 b0 : Bool) :
    bit0 (cons b1 b0) = b0 := by
  cases b1 <;> cases b0 <;> rfl

@[simp]
theorem zero_add (c : Color) :
    zero + c = c := by
  cases c <;> rfl

@[simp]
theorem add_zero (c : Color) :
    c + zero = c := by
  cases c <;> rfl

theorem add_comm (c d : Color) :
    c + d = d + c := by
  cases c <;> cases d <;> rfl

theorem add_assoc (a b c : Color) :
    a + b + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem add_left_comm (a b c : Color) :
    a + (b + c) = b + (a + c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp]
theorem add_self (c : Color) :
    c + c = zero := by
  cases c <;> rfl

@[simp]
theorem add_left_self (c d : Color) :
    c + (c + d) = d := by
  cases c <;> cases d <;> rfl

@[simp]
theorem add_right_self (c d : Color) :
    c + d + d = c := by
  cases c <;> cases d <;> rfl

@[simp]
theorem add_left_add_left (a c d : Color) :
    (a + c) + (a + d) = c + d := by
  cases a <;> cases c <;> cases d <;> rfl

@[simp]
theorem one_add_two :
    one + two = three := rfl

@[simp]
theorem two_add_one :
    two + one = three := rfl

@[simp]
theorem one_add_three :
    one + three = two := rfl

@[simp]
theorem three_add_one :
    three + one = two := rfl

@[simp]
theorem two_add_three :
    two + three = one := rfl

@[simp]
theorem three_add_two :
    three + two = one := rfl

theorem add_left_cancel {a b c : Color}
    (h : add a b = add a c) :
    b = c := by
  cases a <;> cases b <;> cases c <;> simp [add] at h ⊢

theorem add_right_cancel {a b c : Color}
    (h : add b a = add c a) :
    b = c := by
  cases a <;> cases b <;> cases c <;> simp [add] at h ⊢

@[simp]
theorem add_eq_zero_iff_eq (c d : Color) :
    c + d = zero ↔ c = d := by
  cases c <;> cases d <;> decide

@[simp]
theorem bit0_add (c d : Color) :
    bit0 (c + d) = Bool.xor c.bit0 d.bit0 := by
  cases c <;> cases d <;> rfl

@[simp]
theorem bit1_add (c d : Color) :
    bit1 (c + d) = Bool.xor c.bit1 d.bit1 := by
  cases c <;> cases d <;> rfl

/-- Encode the four-colour type as `Fin 4`. -/
def toFin4 : Color → Fin 4
  | zero => 0
  | one => 1
  | two => 2
  | three => 3

/-- Decode `Fin 4` as the four-colour type. -/
def ofFin4 (i : Fin 4) : Color :=
  if i = 0 then zero
  else if i = 1 then one
  else if i = 2 then two
  else three

@[simp]
theorem ofFin4_toFin4 (c : Color) :
    ofFin4 (toFin4 c) = c := by
  cases c <;> simp [ofFin4, toFin4]

@[simp]
theorem toFin4_ofFin4 (i : Fin 4) :
    toFin4 (ofFin4 i) = i := by
  revert i
  decide

/-- Equivalence between the custom colour type and the mathlib cardinal
colour type used by `SimpleGraph.Colorable 4`. -/
def equivFin4 : Color ≃ Fin 4 where
  toFun := toFin4
  invFun := ofFin4
  left_inv := ofFin4_toFin4
  right_inv := toFin4_ofFin4

@[simp]
theorem card :
    Fintype.card Color = 4 := by
  rw [Fintype.card_congr equivFin4]
  simp

theorem exists_ne_two (a b : Color) :
    ∃ c : Color, c ≠ a ∧ c ≠ b := by
  revert a b
  decide

theorem exists_ne_three (a b c : Color) :
    ∃ d : Color, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  revert a b c
  decide

end Color

end FourColor

end Schematic.Math.GraphTheory
