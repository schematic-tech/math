import Mathlib.Data.Nat.Bits
import Schematic.Math.GraphTheory.Embedding.Color

/-!
Colour traces.

This ports the first self-contained part of Gonthier's `color.v`: the six
permutations of the three non-zero edge colours and the conversion from a list
of region colours to its cyclic edge-colour trace.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

/-- The six permutations of the non-zero colours, all fixing `Color.zero`. -/
inductive EdgePerm
  | p123
  | p132
  | p213
  | p231
  | p312
  | p321
  deriving DecidableEq

instance : Fintype EdgePerm where
  elems := {EdgePerm.p123, EdgePerm.p132, EdgePerm.p213,
    EdgePerm.p231, EdgePerm.p312, EdgePerm.p321}
  complete := by
    intro g
    cases g <;> simp

namespace EdgePerm

/-- Apply an edge-colour permutation. -/
def apply : EdgePerm → Color → Color
  | p123, c => c
  | p132, Color.zero => Color.zero
  | p132, Color.one => Color.one
  | p132, Color.two => Color.three
  | p132, Color.three => Color.two
  | p213, Color.zero => Color.zero
  | p213, Color.one => Color.two
  | p213, Color.two => Color.one
  | p213, Color.three => Color.three
  | p231, Color.zero => Color.zero
  | p231, Color.one => Color.two
  | p231, Color.two => Color.three
  | p231, Color.three => Color.one
  | p312, Color.zero => Color.zero
  | p312, Color.one => Color.three
  | p312, Color.two => Color.one
  | p312, Color.three => Color.two
  | p321, Color.zero => Color.zero
  | p321, Color.one => Color.three
  | p321, Color.two => Color.two
  | p321, Color.three => Color.one

instance : CoeFun EdgePerm (fun _ => Color → Color) where
  coe := apply

/-- Inverse edge-colour permutation. -/
def inv : EdgePerm → EdgePerm
  | p231 => p312
  | p312 => p231
  | g => g

/-- Composition of edge-colour permutations, in function order:
`comp g h c = g (h c)`. -/
def comp : EdgePerm → EdgePerm → EdgePerm
  | p123, h => h
  | p132, p123 => p132
  | p132, p132 => p123
  | p132, p213 => p312
  | p132, p231 => p321
  | p132, p312 => p213
  | p132, p321 => p231
  | p213, p123 => p213
  | p213, p132 => p231
  | p213, p213 => p123
  | p213, p231 => p132
  | p213, p312 => p321
  | p213, p321 => p312
  | p231, p123 => p231
  | p231, p132 => p213
  | p231, p213 => p321
  | p231, p231 => p312
  | p231, p312 => p123
  | p231, p321 => p132
  | p312, p123 => p312
  | p312, p132 => p321
  | p312, p213 => p132
  | p312, p231 => p123
  | p312, p312 => p231
  | p312, p321 => p213
  | p321, p123 => p321
  | p321, p132 => p312
  | p321, p213 => p231
  | p321, p231 => p213
  | p321, p312 => p132
  | p321, p321 => p123

@[simp]
theorem inv_inv (g : EdgePerm) :
    inv (inv g) = g := by
  cases g <;> rfl

@[simp]
theorem apply_zero (g : EdgePerm) :
    g Color.zero = Color.zero := by
  cases g <;> rfl

@[simp]
theorem inv_apply_apply (g : EdgePerm) (c : Color) :
    inv g (g c) = c := by
  cases g <;> cases c <;> rfl

@[simp]
theorem apply_inv_apply (g : EdgePerm) (c : Color) :
    g (inv g c) = c := by
  cases g <;> cases c <;> rfl

theorem injective (g : EdgePerm) :
    Function.Injective g := by
  intro c d h
  calc
    c = inv g (g c) := (inv_apply_apply g c).symm
    _ = inv g (g d) := by rw [h]
    _ = d := inv_apply_apply g d

/-- Any injective colour map fixing `Color.zero` is one of the six edge-colour
permutations. -/
theorem exists_eq_of_injective_apply_zero
    {f : Color → Color}
    (hf : Function.Injective f)
    (h0 : f Color.zero = Color.zero) :
    ∃ g : EdgePerm, ∀ c : Color, f c = g c := by
  have h01 : f Color.zero ≠ f Color.one := by
    intro h
    have h' : Color.zero = Color.one := hf h
    cases h'
  have h02 : f Color.zero ≠ f Color.two := by
    intro h
    have h' : Color.zero = Color.two := hf h
    cases h'
  have h03 : f Color.zero ≠ f Color.three := by
    intro h
    have h' : Color.zero = Color.three := hf h
    cases h'
  have h12 : f Color.one ≠ f Color.two := by
    intro h
    have h' : Color.one = Color.two := hf h
    cases h'
  have h13 : f Color.one ≠ f Color.three := by
    intro h
    have h' : Color.one = Color.three := hf h
    cases h'
  have h23 : f Color.two ≠ f Color.three := by
    intro h
    have h' : Color.two = Color.three := hf h
    cases h'
  cases h1 : f Color.one with
  | zero =>
      exact False.elim (h01 (by rw [h0, h1]))
  | one =>
      cases h2 : f Color.two with
      | zero =>
          exact False.elim (h02 (by rw [h0, h2]))
      | one =>
          exact False.elim (h12 (by rw [h1, h2]))
      | two =>
          cases h3 : f Color.three with
          | zero =>
              exact False.elim (h03 (by rw [h0, h3]))
          | one =>
              exact False.elim (h13 (by rw [h1, h3]))
          | two =>
              exact False.elim (h23 (by rw [h2, h3]))
          | three =>
              exact ⟨EdgePerm.p123,
                by intro c; cases c <;> simp [h0, h1, h2, h3, apply]⟩
      | three =>
          cases h3 : f Color.three with
          | zero =>
              exact False.elim (h03 (by rw [h0, h3]))
          | one =>
              exact False.elim (h13 (by rw [h1, h3]))
          | two =>
              exact ⟨EdgePerm.p132,
                by intro c; cases c <;> simp [h0, h1, h2, h3, apply]⟩
          | three =>
              exact False.elim (h23 (by rw [h2, h3]))
  | two =>
      cases h2 : f Color.two with
      | zero =>
          exact False.elim (h02 (by rw [h0, h2]))
      | one =>
          cases h3 : f Color.three with
          | zero =>
              exact False.elim (h03 (by rw [h0, h3]))
          | one =>
              exact False.elim (h23 (by rw [h2, h3]))
          | two =>
              exact False.elim (h13 (by rw [h1, h3]))
          | three =>
              exact ⟨EdgePerm.p213,
                by intro c; cases c <;> simp [h0, h1, h2, h3, apply]⟩
      | two =>
          exact False.elim (h12 (by rw [h1, h2]))
      | three =>
          cases h3 : f Color.three with
          | zero =>
              exact False.elim (h03 (by rw [h0, h3]))
          | one =>
              exact ⟨EdgePerm.p231,
                by intro c; cases c <;> simp [h0, h1, h2, h3, apply]⟩
          | two =>
              exact False.elim (h13 (by rw [h1, h3]))
          | three =>
              exact False.elim (h23 (by rw [h2, h3]))
  | three =>
      cases h2 : f Color.two with
      | zero =>
          exact False.elim (h02 (by rw [h0, h2]))
      | one =>
          cases h3 : f Color.three with
          | zero =>
              exact False.elim (h03 (by rw [h0, h3]))
          | one =>
              exact False.elim (h23 (by rw [h2, h3]))
          | two =>
              exact ⟨EdgePerm.p312,
                by intro c; cases c <;> simp [h0, h1, h2, h3, apply]⟩
          | three =>
              exact False.elim (h13 (by rw [h1, h3]))
      | two =>
          cases h3 : f Color.three with
          | zero =>
              exact False.elim (h03 (by rw [h0, h3]))
          | one =>
              exact ⟨EdgePerm.p321,
                by intro c; cases c <;> simp [h0, h1, h2, h3, apply]⟩
          | two =>
              exact False.elim (h23 (by rw [h2, h3]))
          | three =>
              exact False.elim (h13 (by rw [h1, h3]))
      | three =>
          exact False.elim (h12 (by rw [h1, h2]))

theorem map_add (g : EdgePerm) (c d : Color) :
    g (c + d) = g c + g d := by
  cases g <;> cases c <;> cases d <;> rfl

@[simp]
theorem comp_apply (g h : EdgePerm) (c : Color) :
    comp g h c = g (h c) := by
  cases g <;> cases h <;> cases c <;> rfl

@[simp]
theorem comp_p123_left (g : EdgePerm) :
    comp EdgePerm.p123 g = g := by
  cases g <;> rfl

@[simp]
theorem comp_p123_right (g : EdgePerm) :
    comp g EdgePerm.p123 = g := by
  cases g <;> rfl

@[simp]
theorem p231_apply_p132 (c : Color) :
    EdgePerm.p231 (EdgePerm.p132 c) = EdgePerm.p132 (EdgePerm.p312 c) := by
  cases c <;> rfl

@[simp]
theorem p312_apply_p132 (c : Color) :
    EdgePerm.p312 (EdgePerm.p132 c) = EdgePerm.p132 (EdgePerm.p231 c) := by
  cases c <;> rfl

/-- Rotation that sends a non-zero first trace colour to `Color.one`.
`Color.zero` is treated as the identity, matching the Coq failure convention
for improper traces. -/
def edgeRot : Color → EdgePerm
  | Color.zero => p123
  | Color.one => p123
  | Color.two => p312
  | Color.three => p231

theorem other_colors
    {c : Color}
    (hc : c ≠ Color.zero)
    (d : Color) :
    d = Color.zero ∨ d = c ∨ d = EdgePerm.p312 c ∨ d = EdgePerm.p231 c := by
  cases c with
  | zero => exact False.elim (hc rfl)
  | one =>
      cases d <;> simp [apply]
  | two =>
      cases d <;> simp [apply]
  | three =>
      cases d <;> simp [apply]

end EdgePerm

/-- A colour sequence. -/
abbrev ColSeq := List Color

namespace ColSeq

/-- First colour, defaulting to zero. -/
def headColor : ColSeq → Color
  | [] => Color.zero
  | c :: _ => c

/-- Sum of a colour sequence under xor. -/
def sum : ColSeq → Color :=
  List.foldr (fun c s => c + s) Color.zero

/-- Pairwise sums, seeded by the colour immediately before the list. -/
def pairSums : Color → ColSeq → ColSeq
  | _, [] => []
  | c, d :: ds => (c + d) :: pairSums d ds

/-- Partial trace: adjacent linear pairwise sums. -/
def ptrace : ColSeq → ColSeq
  | [] => []
  | c :: cs => pairSums c cs

/-- Complete a partial trace with the redundant final sum. -/
def ctrace (et : ColSeq) : ColSeq :=
  et ++ [sum et]

/-- Cyclic edge-colour trace of a region-colour sequence. -/
def trace : ColSeq → ColSeq
  | [] => []
  | c :: cs => ctrace (ptrace (c :: cs))

/-- The previous-element list used by MathComp's `belast`.
`prevs z [a,b,c] = [z,a,b]`. -/
def prevs (fallback : Color) : ColSeq → ColSeq
  | [] => []
  | c :: cs => fallback :: prevs c cs

/-- Accumulate edge colours after each step.  This is MathComp's `scanl` shape:
`scanAdd c [e₀,e₁] = [c+e₀, c+e₀+e₁]`. -/
def scanAdd : Color → ColSeq → ColSeq
  | _, [] => []
  | c, e :: es =>
      let c' := c + e
      c' :: scanAdd c' es

/-- Reconstruct a region-colour sequence with prescribed first colour from a
cyclic edge trace. -/
def untrace (c0 : Color) (et : ColSeq) : ColSeq :=
  scanAdd c0 (prevs Color.zero et)

/-- Right-rotated trace, seeded by the last colour. -/
def urtrace (cs : ColSeq) : ColSeq :=
  pairSums (cs.getLastD Color.zero) cs

/-- Left rotation by one position, matching MathComp's `rot 1`. -/
def rot1 : ColSeq → ColSeq
  | [] => []
  | c :: cs => cs ++ [c]

/-- A proper trace starts with a non-zero edge colour. -/
def ProperTrace (et : ColSeq) : Prop :=
  headColor et ≠ Color.zero

instance properTraceDecidable (et : ColSeq) :
    Decidable et.ProperTrace := by
  unfold ProperTrace
  infer_instance

/-- Map an edge-colour permutation over a trace. -/
def perm (g : EdgePerm) (et : ColSeq) : ColSeq :=
  et.map g

/-- Normalised tail of a trace: rotate a non-zero head colour to `one`, or
return the distinguished bad trace `[zero]` for an improper trace. -/
def ttail (et : ColSeq) : ColSeq :=
  if et.ProperTrace then
    match et with
    | [] => []
    | c :: cs => perm (EdgePerm.edgeRot c) cs
  else
    [Color.zero]

/-- The tail-order predicate used to halve the trace search by the
`two`/`three` symmetry. -/
def evenTail : ColSeq → Bool :=
  List.foldr
    (fun c b =>
      match c with
      | Color.zero => b
      | Color.one => b
      | Color.two => true
      | Color.three => false)
    true

@[simp]
theorem evenTail_nil :
    evenTail [] = true := rfl

@[simp]
theorem evenTail_cons_zero (et : ColSeq) :
    evenTail (Color.zero :: et) = evenTail et := rfl

@[simp]
theorem evenTail_cons_one (et : ColSeq) :
    evenTail (Color.one :: et) = evenTail et := rfl

@[simp]
theorem evenTail_cons_two (et : ColSeq) :
    evenTail (Color.two :: et) = true := rfl

@[simp]
theorem evenTail_cons_three (et : ColSeq) :
    evenTail (Color.three :: et) = false := rfl

/-- A trace is even when its normalised tail is even. -/
def evenTrace (et : ColSeq) : Bool :=
  evenTail (ttail et)

/-- The trace permutation that makes a trace even. -/
def etracePerm (et : ColSeq) : EdgePerm :=
  if evenTrace et then EdgePerm.p123 else EdgePerm.p132

/-- The even representative of an edge-colour trace. -/
def etrace (et : ColSeq) : ColSeq :=
  perm (etracePerm et) et

/-- The normalised even tail of a trace. -/
def etail (et : ColSeq) : ColSeq :=
  perm (etracePerm et) (ttail et)

/-- Standardised partial trace of a colour sequence. -/
def eptrace (cs : ColSeq) : ColSeq :=
  etail (ptrace cs)

/-- Count the colours whose high bit is set. -/
def countBit1 : ColSeq → Nat :=
  List.foldr (fun c n => if c.bit1 then n + 1 else n) 0

@[simp]
theorem countBit1_nil :
    countBit1 [] = 0 := rfl

@[simp]
theorem countBit1_cons (c : Color) (et : ColSeq) :
    countBit1 (c :: et) = if c.bit1 then countBit1 et + 1 else countBit1 et := by
  cases c <;> rfl

@[simp]
theorem countBit1_append :
    ∀ xs ys : ColSeq, countBit1 (xs ++ ys) = countBit1 xs + countBit1 ys
  | [], ys => by simp
  | c :: xs, ys => by
      cases c <;> simp [countBit1_append xs ys, Color.bit1] <;> omega

@[simp]
theorem countBit1_singleton (c : Color) :
    countBit1 [c] = if c.bit1 then 1 else 0 := by
  cases c <;> rfl

theorem countBit1_append_singleton (et : ColSeq) (c : Color) :
    countBit1 (et ++ [c]) = countBit1 et + if c.bit1 then 1 else 0 := by
  simp

theorem countBit1_bodd_eq_sum_bit1 :
    ∀ et : ColSeq, (countBit1 et).bodd = (sum et).bit1
  | [] => rfl
  | c :: et => by
      have ih := countBit1_bodd_eq_sum_bit1 et
      change
        (if c.bit1 then countBit1 et + 1 else countBit1 et).bodd =
          (c + sum et).bit1
      cases c <;> cases hsum : sum et <;>
        simp [Color.bit1, hsum, ih, Nat.bodd_succ]

@[simp]
theorem ctrace_nil :
    ctrace [] = [Color.zero] := rfl

@[simp]
theorem ctrace_cons (c : Color) (et : ColSeq) :
    ctrace (c :: et) = c :: et ++ [c + sum et] := by
  rfl

theorem countBit1_ctrace_cons (c : Color) (et : ColSeq) :
    countBit1 (ctrace (c :: et)) =
      (if c.bit1 then countBit1 (et ++ [c + sum et]) + 1
        else countBit1 (et ++ [c + sum et])) := by
  cases c <;> rfl

theorem not_mem_zero_ctrace_cons_iff (c : Color) (et : ColSeq) :
    Color.zero ∉ ctrace (c :: et) ↔
      c ≠ Color.zero ∧ Color.zero ∉ et ++ [c + sum et] := by
  cases c <;> simp [ctrace_cons]

@[simp]
theorem sum_nil :
    sum [] = Color.zero := rfl

@[simp]
theorem sum_cons (c : Color) (cs : ColSeq) :
    sum (c :: cs) = c + sum cs := rfl

@[simp]
theorem pairSums_nil (c : Color) :
    pairSums c [] = [] := rfl

@[simp]
theorem pairSums_cons (c d : Color) (ds : ColSeq) :
    pairSums c (d :: ds) = (c + d) :: pairSums d ds := rfl

theorem length_pairSums (c : Color) (cs : ColSeq) :
    (pairSums c cs).length = cs.length := by
  induction cs generalizing c with
  | nil => rfl
  | cons d ds ih =>
      simp [pairSums, ih]

theorem pairSums_append_singleton (c x : Color) :
    ∀ cs : ColSeq,
      pairSums c (cs ++ [x]) = pairSums c cs ++ [cs.getLastD c + x]
  | [] => rfl
  | d :: ds => by
      cases ds with
      | nil => rfl
      | cons e es =>
          change
            (c + d) :: pairSums d ((e :: es) ++ [x]) =
              (c + d) :: (pairSums d (e :: es) ++
                [(d :: e :: es).getLastD c + x])
          rw [pairSums_append_singleton d x (e :: es)]
          simp [List.getLast?_cons_cons]
          rw [List.getLast?_eq_getLast_of_ne_nil (by simp : e :: es ≠ [])]
          simp

theorem length_ptrace :
    ∀ cs : ColSeq, (ptrace cs).length = cs.length - 1
  | [] => rfl
  | c :: cs => by
      simp [ptrace, length_pairSums]

theorem length_ctrace (et : ColSeq) :
    (ctrace et).length = et.length + 1 := by
  simp [ctrace]

theorem length_trace :
    ∀ cs : ColSeq, (trace cs).length = cs.length
  | [] => rfl
  | c :: cs => by
      simp [trace, length_ctrace, length_ptrace]

theorem length_rot1 :
    ∀ cs : ColSeq, (rot1 cs).length = cs.length
  | [] => rfl
  | _ :: cs => by
      simp [rot1]

@[simp]
theorem prevs_nil (fallback : Color) :
    prevs fallback [] = [] := rfl

@[simp]
theorem prevs_cons (fallback c : Color) (cs : ColSeq) :
    prevs fallback (c :: cs) = fallback :: prevs c cs := rfl

theorem length_prevs (fallback : Color) (cs : ColSeq) :
    (prevs fallback cs).length = cs.length := by
  induction cs generalizing fallback with
  | nil => rfl
  | cons c cs ih =>
      simp [prevs, ih]

@[simp]
theorem scanAdd_nil (c : Color) :
    scanAdd c [] = [] := rfl

@[simp]
theorem scanAdd_cons (c e : Color) (es : ColSeq) :
    scanAdd c (e :: es) = (c + e) :: scanAdd (c + e) es := rfl

theorem length_scanAdd (c : Color) (es : ColSeq) :
    (scanAdd c es).length = es.length := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
      simp [scanAdd, ih]

theorem length_untrace (c0 : Color) (et : ColSeq) :
    (untrace c0 et).length = et.length := by
  simp [untrace, length_scanAdd, length_prevs]

theorem prevs_tail_eq_dropLast (e : Color) (es : ColSeq) :
    prevs e es = (e :: es).dropLast := by
  induction es generalizing e with
  | nil => rfl
  | cons d ds ih =>
      simp [prevs, ih]

theorem pairSums_scanAdd (c : Color) (es : ColSeq) :
    pairSums c (scanAdd c es) = es := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
      simp [scanAdd, ih]

theorem ptrace_untrace (c0 : Color) (et : ColSeq) :
    ptrace (untrace c0 et) = et.dropLast := by
  cases et with
  | nil => rfl
  | cons e es =>
      simp [untrace, prevs_tail_eq_dropLast, pairSums_scanAdd, ptrace]

theorem prevs_append_singleton
    (fallback last : Color) (et : ColSeq) :
    prevs fallback (et ++ [last]) = fallback :: et := by
  induction et generalizing fallback with
  | nil => rfl
  | cons e et ih =>
      simp [ih]

theorem prevs_ctrace (et : ColSeq) :
    prevs Color.zero (ctrace et) = Color.zero :: et := by
  simp [ctrace, prevs_append_singleton]

theorem scanAdd_pairSums (c : Color) (cs : ColSeq) :
    scanAdd c (pairSums c cs) = cs := by
  induction cs generalizing c with
  | nil => rfl
  | cons d ds ih =>
      simp [pairSums, ih]

theorem untrace_ctrace_ptrace :
    ∀ cs : ColSeq, cs ≠ [] → untrace cs.headColor (trace cs) = cs
  | [], h => False.elim (h rfl)
  | c :: cs, _ => by
      simp [trace, untrace, prevs_ctrace, headColor, ptrace, scanAdd_pairSums]

theorem untrace_trace (c0 : Color) (cs : ColSeq) :
    untrace c0 (trace (c0 :: cs)) = c0 :: cs := by
  exact untrace_ctrace_ptrace (c0 :: cs) (by simp)

theorem pairSums_add_left (a c : Color) (cs : ColSeq) :
    pairSums (a + c) (cs.map (fun d => a + d)) = pairSums c cs := by
  induction cs generalizing c with
  | nil => rfl
  | cons d ds ih =>
      simp [pairSums, ih]

theorem ptrace_add_left (a : Color) :
    ∀ cs : ColSeq, ptrace (cs.map (fun c => a + c)) = ptrace cs
  | [] => rfl
  | c :: cs => by
      exact pairSums_add_left a c cs

theorem sum_append (xs ys : ColSeq) :
    sum (xs ++ ys) = sum xs + sum ys := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih =>
      calc
        sum ((x :: xs) ++ ys) = x + sum (xs ++ ys) := rfl
        _ = x + (sum xs + sum ys) := by rw [ih]
        _ = (x + sum xs) + sum ys :=
          (Color.add_assoc x (sum xs) (sum ys)).symm
        _ = sum (x :: xs) + sum ys := rfl

theorem sum_singleton (c : Color) :
    sum [c] = c := by
  simp [sum]

theorem sum_reverse : ∀ et : ColSeq, sum et.reverse = sum et
  | [] => rfl
  | e :: et => by
      rw [List.reverse_cons, sum_append, sum_singleton, sum_reverse]
      exact Color.add_comm (sum et) e

theorem sum_rot1 :
    ∀ cs : ColSeq, sum (rot1 cs) = sum cs
  | [] => rfl
  | c :: cs => by
      rw [rot1, sum_append, sum_singleton]
      exact Color.add_comm (sum cs) c

theorem sum_pairSums (c : Color) :
    ∀ cs : ColSeq, sum (pairSums c cs) = c + cs.getLastD c
  | [] => by
      simp
  | d :: ds => by
      calc
        sum (pairSums c (d :: ds)) = (c + d) + sum (pairSums d ds) := rfl
        _ = (c + d) + (d + ds.getLastD d) := by
          rw [sum_pairSums d ds]
        _ = c + ds.getLastD d := by
          rw [Color.add_assoc]
          simp
        _ = c + (d :: ds).getLastD c := by
          cases ds with
          | nil => rfl
          | cons e es =>
              simp [List.getLast?_cons_cons]
              rw [List.getLast?_eq_getLast_of_ne_nil (by simp : e :: es ≠ [])]
              simp

theorem ctrace_pairSums (c : Color) (cs : ColSeq) :
    ctrace (pairSums c cs) = pairSums c (cs ++ [c]) := by
  rw [ctrace, pairSums_append_singleton, sum_pairSums]
  simp [Color.add_comm]

theorem trace_cons (c : Color) (cs : ColSeq) :
    trace (c :: cs) = pairSums c (cs ++ [c]) := by
  simp [trace, ptrace, ctrace_pairSums]

theorem urtrace_rot1 :
    ∀ cs : ColSeq, urtrace (rot1 cs) = trace cs
  | [] => rfl
  | [c] => by
      simp [urtrace, rot1, trace, ptrace, ctrace, sum]
  | c₁ :: c₂ :: cs => by
      rw [trace_cons]
      change
        pairSums (((c₂ :: cs) ++ [c₁]).getLastD Color.zero)
          ((c₂ :: cs) ++ [c₁]) =
        pairSums c₁ ((c₂ :: cs) ++ [c₁])
      simp [List.getLastD]

theorem trace_rot1 :
    ∀ cs : ColSeq, trace (rot1 cs) = rot1 (trace cs)
  | [] => rfl
  | [c] => by
      simp [rot1, trace, ptrace, ctrace, sum]
  | c₁ :: c₂ :: cs => by
      have hlast : (cs ++ [c₁]).getLastD c₂ = c₁ := by
        exact List.getLastD_concat
      calc
        trace (rot1 (c₁ :: c₂ :: cs))
            = pairSums c₂ ((cs ++ [c₁]) ++ [c₂]) := by
                change trace (c₂ :: (cs ++ [c₁])) =
                  pairSums c₂ ((cs ++ [c₁]) ++ [c₂])
                rw [trace_cons]
        _ = pairSums c₂ (cs ++ [c₁]) ++ [(cs ++ [c₁]).getLastD c₂ + c₂] := by
                rw [pairSums_append_singleton]
        _ = pairSums c₂ (cs ++ [c₁]) ++ [c₁ + c₂] := by
                rw [hlast]
        _ = rot1 (trace (c₁ :: c₂ :: cs)) := by
                rw [trace_cons]
                rfl

/-- Reverse the adjacent pair sums of a path.  This is the list identity at
the core of Coq `trace_rev`. -/
theorem pairSums_reverse_cons (c d : Color) :
    ∀ cs : ColSeq,
      pairSums d (c :: cs).reverse =
        (cs.getLastD c + d) :: (pairSums c cs).reverse := by
  intro cs
  induction cs using List.reverseRecOn generalizing c d with
  | nil => simp [pairSums, Color.add_comm]
  | append_singleton a cs ih =>
      simp only [List.reverse_cons, List.reverse_append,
        List.reverse_nil, List.nil_append,
        List.singleton_append]
      rw [List.cons_append]
      rw [pairSums]
      change
        (d + cs) :: pairSums cs (a.reverse ++ [c]) =
          ((a ++ [cs]).getLastD c + d) ::
            (pairSums c (a ++ [cs])).reverse
      have ih' := ih c cs
      rw [List.reverse_cons] at ih'
      rw [ih']
      simp [pairSums_append_singleton, Color.add_comm]

/-- Reversing a cyclic trace turns it into the right-seeded trace of the
reversed colour sequence. -/
theorem reverse_trace_eq_urtrace_reverse (cs : ColSeq) :
    (trace cs).reverse = urtrace cs.reverse := by
  cases cs with
  | nil => rfl
  | cons c cs =>
      rw [trace_cons, pairSums_append_singleton]
      rw [List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      rw [List.reverse_cons]
      rw [show urtrace (cs.reverse ++ [c]) =
          pairSums c (cs.reverse ++ [c]) by
        simp [urtrace]]
      rw [← List.reverse_cons]
      rw [pairSums_reverse_cons]

/-- A cyclic trace is the one-step left rotation of its right-seeded trace. -/
theorem trace_eq_rot1_urtrace (cs : ColSeq) :
    trace cs = rot1 (urtrace cs) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
      cases cs with
      | nil => simp [trace, ptrace, ctrace, sum, urtrace, rot1]
      | cons d ds =>
          have hlast : (d :: ds).getLastD c =
              (d :: ds).getLastD Color.zero := by
            cases ds <;> simp [List.getLastD]
          rw [trace_cons, pairSums_append_singleton]
          simpa [urtrace, rot1, Color.add_comm] using
            congrArg (fun x => c + x) hlast

/-- Coq `trace_rev`. -/
theorem trace_reverse (cs : ColSeq) :
    trace cs.reverse = rot1 (trace cs).reverse := by
  calc
    trace cs.reverse = rot1 (urtrace cs.reverse) :=
      trace_eq_rot1_urtrace cs.reverse
    _ = rot1 (trace cs).reverse :=
      congrArg rot1 (reverse_trace_eq_urtrace_reverse cs).symm

@[simp]
theorem sum_ctrace (et : ColSeq) :
    sum (ctrace et) = Color.zero := by
  rw [ctrace, sum_append, sum_singleton, Color.add_self]

theorem countBit1_ctrace_bodd (et : ColSeq) :
    (countBit1 (ctrace et)).bodd = false := by
  rw [countBit1_bodd_eq_sum_bit1, sum_ctrace]
  rfl

theorem perm_sum (g : EdgePerm) (et : ColSeq) :
    sum (perm g et) = g (sum et) := by
  induction et with
  | nil => simp [perm, sum]
  | cons c cs ih =>
      calc
        sum (perm g (c :: cs)) = g c + sum (perm g cs) := rfl
        _ = g c + g (sum cs) := by rw [ih]
        _ = g (c + sum cs) := (EdgePerm.map_add g c (sum cs)).symm
        _ = g (sum (c :: cs)) := rfl

theorem perm_pairSums (g : EdgePerm) (c : Color) (cs : ColSeq) :
    pairSums (g c) (cs.map g) = (pairSums c cs).map g := by
  induction cs generalizing c with
  | nil => rfl
  | cons d ds ih =>
      simp [pairSums, EdgePerm.map_add, ih]

theorem perm_ptrace (g : EdgePerm) (cs : ColSeq) :
    ptrace (cs.map g) = (ptrace cs).map g := by
  cases cs with
  | nil => rfl
  | cons c cs =>
      exact perm_pairSums g c cs

theorem perm_ctrace (g : EdgePerm) (et : ColSeq) :
    ctrace (perm g et) = perm g (ctrace et) := by
  unfold ctrace
  rw [perm_sum]
  simp [perm]

theorem perm_trace (g : EdgePerm) (cs : ColSeq) :
    trace (cs.map g) = perm g (trace cs) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
      change ctrace (ptrace ((c :: cs).map g)) =
        perm g (ctrace (ptrace (c :: cs)))
      rw [perm_ptrace]
      change ctrace (perm g (ptrace (c :: cs))) =
        perm g (ctrace (ptrace (c :: cs)))
      rw [perm_ctrace]

@[simp]
theorem perm_id (et : ColSeq) :
    perm EdgePerm.p123 et = et := by
  induction et with
  | nil => rfl
  | cons c cs ih =>
      change EdgePerm.p123 c :: perm EdgePerm.p123 cs = c :: cs
      rw [ih]
      cases c <;> rfl

theorem perm_inv (g : EdgePerm) (et : ColSeq) :
    perm (EdgePerm.inv g) (perm g et) = et := by
  induction et with
  | nil => rfl
  | cons c cs ih =>
      calc
        perm (EdgePerm.inv g) (perm g (c :: cs)) =
            EdgePerm.inv g (g c) :: perm (EdgePerm.inv g) (perm g cs) := rfl
        _ = c :: cs := by rw [EdgePerm.inv_apply_apply, ih]

theorem perm_comp (g h : EdgePerm) (et : ColSeq) :
    perm (EdgePerm.comp g h) et = perm g (perm h et) := by
  induction et with
  | nil => rfl
  | cons c cs ih =>
      change EdgePerm.comp g h c :: perm (EdgePerm.comp g h) cs =
        g (h c) :: perm g (perm h cs)
      rw [ih, EdgePerm.comp_apply]

theorem perm_comp_apply (g h : EdgePerm) (et : ColSeq) :
    perm g (perm h et) = perm (EdgePerm.comp g h) et :=
  (perm_comp g h et).symm

theorem perm_zero_mem_iff (g : EdgePerm) (et : ColSeq) :
    Color.zero ∈ perm g et ↔ Color.zero ∈ et := by
  constructor
  · intro h
    rcases List.mem_map.1 h with ⟨c, hc, hczero⟩
    have hz : c = Color.zero := by
      apply EdgePerm.injective g
      rw [hczero, EdgePerm.apply_zero]
    simpa [hz] using hc
  · intro h
    exact List.mem_map.2 ⟨Color.zero, h, EdgePerm.apply_zero g⟩

theorem proper_perm_iff (g : EdgePerm) (et : ColSeq) :
    ProperTrace (perm g et) ↔ ProperTrace et := by
  cases et with
  | nil =>
      simp [ProperTrace, headColor, perm]
  | cons c cs =>
      cases g <;> cases c <;>
        simp [ProperTrace, headColor, perm, EdgePerm.apply]

theorem ttail_of_not_proper
    {et : ColSeq}
    (hbad : ¬ et.ProperTrace) :
    ttail et = [Color.zero] := by
  simp [ttail, hbad]

theorem ttail_cons_of_proper
    {c : Color} {cs : ColSeq}
    (hproper : ProperTrace (c :: cs)) :
    ttail (c :: cs) = perm (EdgePerm.edgeRot c) cs := by
  simp [ttail, hproper]

theorem mem_zero_ttail (et : ColSeq) :
    Color.zero ∈ ttail et ↔ ¬ et.ProperTrace ∨ Color.zero ∈ et := by
  cases et with
  | nil =>
      simp [ttail, ProperTrace, headColor]
  | cons c cs =>
      cases c <;>
        simp [ttail, ProperTrace, headColor, perm_zero_mem_iff]

theorem not_mem_zero_ttail_iff (et : ColSeq) :
    Color.zero ∉ ttail et ↔ et.ProperTrace ∧ Color.zero ∉ et := by
  rw [← not_iff_not]
  simp [mem_zero_ttail]

theorem mem_zero_etail_iff (et : ColSeq) :
    Color.zero ∈ etail et ↔ ¬ et.ProperTrace ∨ Color.zero ∈ et := by
  rw [etail, perm_zero_mem_iff, mem_zero_ttail]

theorem not_mem_zero_etail_iff (et : ColSeq) :
    Color.zero ∉ etail et ↔ et.ProperTrace ∧ Color.zero ∉ et := by
  rw [← not_iff_not]
  simp [mem_zero_etail_iff]

theorem evenTail_perm132_of_not_even
    {et : ColSeq}
    (heven : evenTail et = false) :
    evenTail (perm EdgePerm.p132 et) = true := by
  induction et with
  | nil =>
      simp [evenTail] at heven
  | cons c cs ih =>
      cases c <;> simp [evenTail, perm, EdgePerm.apply] at heven ⊢
      all_goals exact ih heven

theorem even_etail (et : ColSeq) :
    evenTail (etail et) = true := by
  by_cases heven : evenTrace et = true
  · simp [etail, etracePerm, heven]
    exact heven
  · have hfalse : evenTrace et = false := by
      cases h : evenTrace et with
      | false => rfl
      | true => exact False.elim (heven h)
    simp [etail, etracePerm, hfalse]
    exact evenTail_perm132_of_not_even hfalse

theorem etail_eq_ttail_of_evenTrace
    {et : ColSeq}
    (heven : evenTrace et = true) :
    etail et = ttail et := by
  simp [etail, etracePerm, heven, perm_id]

theorem ttail_perm132 (et : ColSeq) :
    ttail (perm EdgePerm.p132 et) = perm EdgePerm.p132 (ttail et) := by
  cases et with
  | nil =>
      rfl
  | cons c cs =>
      cases c <;>
        simp [ttail, ProperTrace, headColor, perm, EdgePerm.edgeRot,
          EdgePerm.apply, List.map_map]
      all_goals
        intro a _ha
        cases a <;> rfl

theorem ttail_etrace (et : ColSeq) :
    ttail (etrace et) = etail et := by
  by_cases heven : evenTrace et = true
  · simp [etrace, etracePerm, etail, heven]
  · have hfalse : evenTrace et = false := by
      cases h : evenTrace et with
      | false => rfl
      | true => exact False.elim (heven h)
    simp [etrace, etracePerm, etail, hfalse, ttail_perm132]

theorem even_etrace (et : ColSeq) :
    evenTrace (etrace et) = true := by
  unfold evenTrace
  rw [ttail_etrace]
  exact even_etail et

theorem proper_etrace_iff (et : ColSeq) :
    ProperTrace (etrace et) ↔ ProperTrace et := by
  simp [etrace, proper_perm_iff]

theorem mem_zero_etrace_iff (et : ColSeq) :
    Color.zero ∈ etrace et ↔ Color.zero ∈ et := by
  simp [etrace, perm_zero_mem_iff]

theorem not_mem_zero_etrace_iff (et : ColSeq) :
    Color.zero ∉ etrace et ↔ Color.zero ∉ et := by
  simpa using not_congr (mem_zero_etrace_iff et)

theorem etrace_idempotent (et : ColSeq) :
    etrace (etrace et) = etrace et := by
  change perm (etracePerm (etrace et)) (etrace et) = etrace et
  have hperm : etracePerm (etrace et) = EdgePerm.p123 := by
    simp [etracePerm, even_etrace]
  rw [hperm, perm_id]

theorem etail_etrace (et : ColSeq) :
    etail (etrace et) = etail et := by
  simp [etail, ttail_etrace, etracePerm, even_etrace]

theorem edgeRot_apply_self
    {c : Color}
    (hc : c ≠ Color.zero) :
    EdgePerm.edgeRot c c = Color.one := by
  cases c <;> simp [EdgePerm.edgeRot, EdgePerm.apply] at hc ⊢

@[simp]
theorem etracePerm_apply_one (et : ColSeq) :
    etracePerm et Color.one = Color.one := by
  by_cases h : evenTrace et = true <;>
    simp [etracePerm, h, EdgePerm.apply]

theorem etail_perm
    {et : ColSeq}
    (hproper : ProperTrace et) :
    ∃ g : EdgePerm, perm g et = Color.one :: etail et := by
  cases et with
  | nil =>
      simp [ProperTrace, headColor] at hproper
  | cons c cs =>
      refine ⟨EdgePerm.comp (etracePerm (c :: cs)) (EdgePerm.edgeRot c), ?_⟩
      have hc : c ≠ Color.zero := by
        simpa [ProperTrace, headColor] using hproper
      calc
        perm (EdgePerm.comp (etracePerm (c :: cs)) (EdgePerm.edgeRot c)) (c :: cs)
            = perm (etracePerm (c :: cs)) (perm (EdgePerm.edgeRot c) (c :: cs)) := by
                rw [perm_comp]
        _ = Color.one :: etail (c :: cs) := by
            simp [perm, etail, ttail, hproper, edgeRot_apply_self hc]

theorem perm132_eq_self_of_evenTail
    {et : ColSeq}
    (heven : evenTail et = true)
    (heven' : evenTail (perm EdgePerm.p132 et) = true) :
    perm EdgePerm.p132 et = et := by
  induction et with
  | nil => rfl
  | cons c cs ih =>
      cases c with
      | zero =>
          simp [perm, EdgePerm.apply] at heven heven' ⊢
          exact ih heven heven'
      | one =>
          simp [perm, EdgePerm.apply] at heven heven' ⊢
          exact ih heven heven'
      | two => simp [perm, EdgePerm.apply] at heven'
      | three => simp [evenTail] at heven

/-- Coq `etail_permt`: the normalized even tail is the canonical
representative of an edge trace under every global edge-color permutation. -/
theorem etail_perm_eq (g : EdgePerm) (et : ColSeq) :
    etail (perm g et) = etail et := by
  by_cases hproper : ProperTrace et
  · have hproper' : ProperTrace (perm g et) :=
      (proper_perm_iff g et).2 hproper
    rcases etail_perm hproper with ⟨h, hh⟩
    rcases etail_perm hproper' with ⟨h', hh'⟩
    let q := EdgePerm.comp (EdgePerm.comp h' g) (EdgePerm.inv h)
    have hq :
        perm q (Color.one :: etail et) =
          Color.one :: etail (perm g et) := by
      rw [← hh]
      simp only [q, perm_comp, perm_inv, hh']
    change q Color.one :: perm q (etail et) =
      Color.one :: etail (perm g et) at hq
    have hqhead : q Color.one = Color.one := (List.cons.inj hq).1
    have hqtail : perm q (etail et) = etail (perm g et) :=
      (List.cons.inj hq).2
    have hqclass : q = EdgePerm.p123 ∨ q = EdgePerm.p132 := by
      cases hqeq : q <;>
        simp [hqeq, EdgePerm.apply] at hqhead ⊢
    rcases hqclass with hqid | hswap
    · rw [hqid] at hqtail
      exact hqtail.symm.trans (perm_id (etail et))
    · rw [hswap] at hqtail
      have hfix : perm EdgePerm.p132 (etail et) = etail et :=
        perm132_eq_self_of_evenTail (even_etail et) (by
          rw [hqtail]
          exact even_etail (perm g et))
      exact hqtail.symm.trans hfix
  · have hproper' : ¬ ProperTrace (perm g et) := by
      simpa [proper_perm_iff] using hproper
    rw [etail, etail, ttail_of_not_proper hproper,
      ttail_of_not_proper hproper']
    simp [perm]

theorem etrace_of_even
    {et : ColSeq}
    (heven : evenTrace et = true) :
    etrace et = et := by
  simp [etrace, etracePerm, heven]

theorem etrace_of_not_even
    {et : ColSeq}
    (heven : evenTrace et = false) :
    etrace et = perm EdgePerm.p132 et := by
  simp [etrace, etracePerm, heven]

theorem evenTrace_perm_edgeRot (e : Color) (et : ColSeq) :
    evenTrace (perm (EdgePerm.edgeRot e) et) = evenTrace et := by
  cases et with
  | nil =>
      cases e <;> rfl
  | cons c cs =>
      cases e <;> cases c <;>
        simp [evenTrace, ttail, ProperTrace, headColor, perm,
          EdgePerm.edgeRot, EdgePerm.apply, List.map_map]
      all_goals
        induction cs with
        | nil => rfl
        | cons x xs ih =>
            cases x <;> simp [EdgePerm.apply, ih]

theorem evenTrace_perm132_of_not_even
    {et : ColSeq}
    (heven : evenTrace et = false) :
    evenTrace (perm EdgePerm.p132 et) = true := by
  unfold evenTrace at heven ⊢
  rw [ttail_perm132]
  exact evenTail_perm132_of_not_even heven

theorem etrace_perm132_of_not_even
    {et : ColSeq}
    (heven : evenTrace et = false) :
    etrace (perm EdgePerm.p132 et) = perm EdgePerm.p132 et :=
  etrace_of_even (evenTrace_perm132_of_not_even heven)

theorem etrace_involutive_p132 (et : ColSeq) :
    perm EdgePerm.p132 (perm EdgePerm.p132 et) = et :=
  perm_inv EdgePerm.p132 et

theorem exists_perm_from_etrace (g : EdgePerm) (et : ColSeq) :
    ∃ g' : EdgePerm, perm g' (etrace et) = perm g et := by
  refine ⟨EdgePerm.comp g (EdgePerm.inv (etracePerm et)), ?_⟩
  rw [etrace, perm_comp, perm_inv]

theorem length_perm (g : EdgePerm) (et : ColSeq) :
    (perm g et).length = et.length := by
  simp [perm]

theorem length_ttail_le (et : ColSeq) :
    (ttail et).length ≤ et.length + 1 := by
  by_cases h : et.ProperTrace
  · cases et with
    | nil =>
        simp [ProperTrace, headColor] at h
    | cons c cs =>
        simp [ttail, h, perm]
        exact Nat.le_trans (Nat.le_succ cs.length) (Nat.le_succ (cs.length + 1))
  · simp [ttail, h]

theorem length_ttail_of_proper
    {et : ColSeq}
    (hproper : et.ProperTrace) :
    (ttail et).length + 1 = et.length := by
  cases et with
  | nil =>
      simp [ProperTrace, headColor] at hproper
  | cons c cs =>
      simp [ttail, hproper, length_perm]

theorem length_etrace (et : ColSeq) :
    (etrace et).length = et.length := by
  simp [etrace, length_perm]

theorem length_etail (et : ColSeq) :
    (etail et).length = (ttail et).length := by
  simp [etail, length_perm]

theorem length_etail_of_proper
    {et : ColSeq}
    (hproper : et.ProperTrace) :
    (etail et).length + 1 = et.length := by
  rw [length_etail]
  exact length_ttail_of_proper hproper

theorem length_eptrace (cs : ColSeq) :
    (eptrace cs).length = (ttail (ptrace cs)).length := by
  simp [eptrace, length_etail]

theorem proper_ctrace_iff (et : ColSeq) :
    ProperTrace (ctrace et) ↔ ProperTrace et := by
  cases et with
  | nil =>
      simp [ProperTrace, headColor, ctrace, sum]
  | cons c cs =>
      simp [ProperTrace, headColor, ctrace]

theorem mem_zero_ctrace_iff (et : ColSeq) :
    Color.zero ∈ ctrace et ↔ sum et = Color.zero ∨ Color.zero ∈ et := by
  rw [ctrace]
  constructor
  · intro h
    simp at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h.symm
  · intro h
    simp
    rcases h with h | h
    · exact Or.inr h.symm
    · exact Or.inl h

theorem mem_zero_ctrace_perm_iff (g : EdgePerm) (et : ColSeq) :
    Color.zero ∈ ctrace (perm g et) ↔ Color.zero ∈ ctrace et := by
  rw [perm_ctrace, perm_zero_mem_iff]

theorem not_mem_zero_ctrace_perm_iff (g : EdgePerm) (et : ColSeq) :
    Color.zero ∉ ctrace (perm g et) ↔ Color.zero ∉ ctrace et := by
  simpa using not_congr (mem_zero_ctrace_perm_iff g et)

theorem mem_zero_ctrace_etrace_iff (et : ColSeq) :
    Color.zero ∈ ctrace (etrace et) ↔ Color.zero ∈ ctrace et := by
  simp [etrace, mem_zero_ctrace_perm_iff]

theorem not_mem_zero_ctrace_etrace_iff (et : ColSeq) :
    Color.zero ∉ ctrace (etrace et) ↔ Color.zero ∉ ctrace et := by
  simpa using not_congr (mem_zero_ctrace_etrace_iff et)

theorem ctrace_injective :
    Function.Injective ctrace := by
  intro et et' h
  have hdrop := congrArg List.dropLast h
  simpa [ctrace] using hdrop

theorem sum_trace (cs : ColSeq) :
    sum (trace cs) = Color.zero := by
  cases cs with
  | nil => rfl
  | cons c cs =>
      exact sum_ctrace (ptrace (c :: cs))

theorem trace_perm (g : EdgePerm) (cs : ColSeq) :
    trace (perm g cs) = perm g (trace cs) := by
  simpa [perm] using perm_trace g cs

theorem ctrace_dropLast_of_sum_zero
    {et : ColSeq}
    (hne : et ≠ [])
    (hsum : sum et = Color.zero) :
    ctrace et.dropLast = et := by
  have hlast : sum et.dropLast = et.getLast hne := by
    have hsum' := hsum
    rw [← List.dropLast_append_getLast hne, sum_append, sum_singleton] at hsum'
    exact (Color.add_eq_zero_iff_eq (sum et.dropLast) (et.getLast hne)).1 hsum'
  unfold ctrace
  rw [hlast, List.dropLast_append_getLast hne]

theorem ctrace_prevs_eq_of_sum_zero
    {e : Color} {et : ColSeq}
    (hsum : sum (e :: et) = Color.zero) :
    ctrace (prevs e et) = e :: et := by
  rw [prevs_tail_eq_dropLast]
  exact ctrace_dropLast_of_sum_zero (by simp) hsum

theorem ctrace_reverse_tail_eq_of_sum_zero
    {e : Color} {et : ColSeq}
    (hsum : sum (e :: et) = Color.zero) :
    ctrace et.reverse = (e :: et).reverse := by
  have he : sum et = e := by
    exact ((Color.add_eq_zero_iff_eq e (sum et)).1 (by
      simpa [sum] using hsum)).symm
  unfold ctrace
  rw [sum_reverse, he]
  simp only [List.reverse_cons]

theorem trace_untrace
    (c0 : Color) {et : ColSeq}
    (hsum : sum et = Color.zero) :
    trace (untrace c0 et) = et := by
  cases et with
  | nil => rfl
  | cons e es =>
      change ctrace (ptrace (untrace c0 (e :: es))) = e :: es
      rw [ptrace_untrace]
      exact ctrace_dropLast_of_sum_zero (by simp) hsum

theorem trace_add_left (a : Color) :
    ∀ cs : ColSeq, trace (cs.map (fun c => a + c)) = trace cs
  | [] => rfl
  | c :: cs => by
      change ctrace (ptrace ((c :: cs).map (fun d => a + d))) =
        ctrace (ptrace (c :: cs))
      rw [ptrace_add_left]

theorem eq_of_trace_eq_of_headColor_eq
    {cs ds : ColSeq}
    (htrace : trace cs = trace ds)
    (hhead : cs.headColor = ds.headColor) :
    cs = ds := by
  cases cs with
  | nil =>
      cases ds with
      | nil => rfl
      | cons d ds =>
          have hlen := congrArg List.length htrace
          simp [length_trace] at hlen
  | cons c cs =>
      cases ds with
      | nil =>
          have hlen := congrArg List.length htrace
          simp [length_trace] at hlen
      | cons d ds =>
          have hcd : c = d := by simpa [headColor] using hhead
          subst d
          calc
            c :: cs = untrace c (trace (c :: cs)) :=
              (untrace_trace c cs).symm
            _ = untrace c (trace (c :: ds)) := by rw [htrace]
            _ = c :: ds := untrace_trace c ds

/-- Coq's head-colour normalization in the converse of `colorable_patch`:
two lists with the same cyclic trace differ by the global xor shift determined
by their first colours. -/
theorem map_headShift_eq_of_trace_eq
    (cs ds : ColSeq) (htrace : trace cs = trace ds) :
    cs.map (fun c => (cs.headColor + ds.headColor) + c) = ds := by
  cases cs with
  | nil =>
      cases ds with
      | nil => rfl
      | cons d ds =>
          have hlen := congrArg List.length htrace
          simp [length_trace] at hlen
  | cons c cs =>
      cases ds with
      | nil =>
          have hlen := congrArg List.length htrace
          simp [length_trace] at hlen
      | cons d ds =>
          apply eq_of_trace_eq_of_headColor_eq
          · rw [trace_add_left]
            exact htrace
          · change (c + d) + c = d
            calc
              (c + d) + c = c + (d + c) :=
                Color.add_assoc c d c
              _ = c + (c + d) := by rw [Color.add_comm d c]
              _ = (c + c) + d :=
                (Color.add_assoc c c d).symm
              _ = d := by simp

end ColSeq

end FourColor

end Schematic.Math.GraphTheory
