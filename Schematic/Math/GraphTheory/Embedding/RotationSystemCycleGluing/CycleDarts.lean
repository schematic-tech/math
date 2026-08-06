import Schematic.Math.GraphTheory.PathsTrees
import Schematic.Math.GraphTheory.Embedding.RotationSystemGluing
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
Common-cycle gluing for graph rotation systems.

This file starts the second gluing operation in the
Makarychev--Skopenkov embedding argument.  The first operation, implemented in
`RotationSystemGluing`, moves a planar component through a cut vertex.  The
second operation joins two planar embeddings along a common facial cycle.

The definitions and lemmas below isolate the directed facial-cycle data and
prove the local rotation equation used by that join.  If the forward
orientation of a simple cycle is exactly one face orbit, then at every cycle
vertex the outgoing forward dart is followed in the node rotation by the
reverse of the incoming forward dart.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

/-- The forward-oriented darts along a fixed cycle walk. -/
def CycleForwardDart
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (e : OrientedEdge G) : Prop :=
  Exists fun i : Nat =>
    i < c.length ∧ e.tail = c.getVert i ∧ e.head = c.getVert (i + 1)

theorem cycleForwardDart_iff_mem_darts
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (e : OrientedEdge G) :
    CycleForwardDart c e ↔ orientedEdgeDartEquiv e ∈ c.darts := by
  constructor
  · rintro ⟨i, hi, htail, hhead⟩
    have hiDarts : i < c.darts.length := by
      simpa using hi
    have hget := c.darts_getElem_eq_getVert i hiDarts
    have heq : orientedEdgeDartEquiv e = c.darts[i] := by
      rw [hget]
      apply SimpleGraph.Dart.ext
      exact Prod.ext htail hhead
    rw [heq]
    exact c.darts.getElem_mem hiDarts
  · intro he
    rcases List.getElem_of_mem he with ⟨i, hi, hieq⟩
    have hget := c.darts_getElem_eq_getVert i hi
    have heq :
        orientedEdgeDartEquiv e =
          ⟨(c.getVert i, c.getVert (i + 1)), c.adj_getVert_succ (by
            simpa using hi)⟩ := by
      exact hieq.symm.trans hget
    refine ⟨i, by simpa using hi, ?_, ?_⟩
    · exact congrArg (fun d : G.Dart => d.fst) heq
    · exact congrArg (fun d : G.Dart => d.snd) heq

/-- The backward-oriented darts along a fixed cycle walk. -/
def CycleBackwardDart
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (e : OrientedEdge G) : Prop :=
  CycleForwardDart c e.symm

/-- The directed cycle dart at a specified position. -/
def cycleDartAt
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (i : Nat) (hi : i < c.length) :
    OrientedEdge G :=
  ⟨(c.getVert i, c.getVert (i + 1)), c.adj_getVert_succ hi⟩

@[simp]
theorem cycleDartAt_tail
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (i : Nat) (hi : i < c.length) :
    (cycleDartAt c i hi).tail = c.getVert i :=
  rfl

@[simp]
theorem cycleDartAt_head
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (i : Nat) (hi : i < c.length) :
    (cycleDartAt c i hi).head = c.getVert (i + 1) :=
  rfl

theorem cycleDartAt_forward
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (i : Nat) (hi : i < c.length) :
    CycleForwardDart c (cycleDartAt c i hi) :=
  ⟨i, hi, rfl, rfl⟩

/-- Forward cycle darts are determined by their tail vertex. -/
theorem cycleForwardDart_eq_of_tail_eq
    {V : Type u} {G : SimpleGraph V} {u : V}
    {c : G.Walk u u} (hc : c.IsCycle)
    {e f : OrientedEdge G}
    (he : CycleForwardDart c e)
    (hf : CycleForwardDart c f)
    (htail : e.tail = f.tail) :
    e = f := by
  rcases he with ⟨i, hi, heiTail, heiHead⟩
  rcases hf with ⟨j, hj, hfjTail, hfjHead⟩
  have hij : i = j := by
    apply hc.getVert_injOn'
    · simp only [Set.mem_setOf_eq]
      omega
    · simp only [Set.mem_setOf_eq]
      omega
    · exact heiTail.symm.trans (htail.trans hfjTail)
  subst j
  apply Subtype.ext
  exact Prod.ext htail (heiHead.trans hfjHead.symm)

/-- No directed edge of a simple cycle occurs in both orientations. -/
theorem cycleForwardDart_not_backward
    {V : Type u} {G : SimpleGraph V} {u : V}
    {c : G.Walk u u} (hc : c.IsCycle)
    {e : OrientedEdge G}
    (he : CycleForwardDart c e) :
    ¬ CycleBackwardDart c e := by
  rintro ⟨j, hj, hjTail, hjHead⟩
  rcases he with ⟨i, hi, hiTail, hiHead⟩
  have hfirst : c.getVert i = c.getVert (j + 1) := by
    calc
      c.getVert i = e.tail := hiTail.symm
      _ = e.symm.head := rfl
      _ = c.getVert (j + 1) := hjHead
  have hsecond : c.getVert (i + 1) = c.getVert j := by
    calc
      c.getVert (i + 1) = e.head := hiHead.symm
      _ = e.symm.tail := rfl
      _ = c.getVert j := hjTail
  have hfirstIndex :
      (j + 1 < c.length ∧ i = j + 1) ∨
        (j + 1 = c.length ∧ i = 0) := by
    by_cases hjLast : j + 1 = c.length
    · right
      refine ⟨hjLast, ?_⟩
      have hiZeroVert : c.getVert i = c.getVert 0 := by
        simpa [hjLast] using hfirst
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        have hlen := hc.three_le_length
        omega
      · exact hiZeroVert
    · left
      have hjSucc : j + 1 < c.length := by omega
      refine ⟨hjSucc, ?_⟩
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        omega
      · exact hfirst
  have hsecondIndex :
      (i + 1 < c.length ∧ i + 1 = j) ∨
        (i + 1 = c.length ∧ j = 0) := by
    by_cases hiLast : i + 1 = c.length
    · right
      refine ⟨hiLast, ?_⟩
      have hjZeroVert : c.getVert j = c.getVert 0 := by
        simpa [hiLast] using hsecond.symm
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        have hlen := hc.three_le_length
        omega
      · exact hjZeroVert
    · left
      have hiSucc : i + 1 < c.length := by omega
      refine ⟨hiSucc, ?_⟩
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        omega
      · exact hsecond
  rcases hfirstIndex with hfirstIndex | hfirstIndex <;>
    rcases hsecondIndex with hsecondIndex | hsecondIndex <;>
    have hlen := hc.three_le_length <;>
    omega

/-- Forward and backward cycle orientations are disjoint in either order. -/
theorem cycleBackwardDart_not_forward
    {V : Type u} {G : SimpleGraph V} {u : V}
    {c : G.Walk u u} (hc : c.IsCycle)
    {e : OrientedEdge G}
    (he : CycleBackwardDart c e) :
    ¬ CycleForwardDart c e :=
  fun hforward => cycleForwardDart_not_backward hc hforward he

/-- Reversing a closed walk exchanges its forward and backward dart
orientations. -/
theorem cycleForwardDart_reverse_iff_backward
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (e : OrientedEdge G) :
    CycleForwardDart c.reverse e ↔ CycleBackwardDart c e := by
  constructor
  · rintro ⟨i, hi, htail, hhead⟩
    rw [SimpleGraph.Walk.length_reverse] at hi
    simp only [SimpleGraph.Walk.getVert_reverse] at htail hhead
    let j := c.length - (i + 1)
    refine ⟨j, by dsimp [j]; omega, ?_, ?_⟩
    · simpa [j] using hhead
    · have hindex : j + 1 = c.length - i := by
        dsimp [j]
        omega
      simpa [hindex] using htail
  · rintro ⟨j, hj, htail, hhead⟩
    let i := c.length - (j + 1)
    refine
      ⟨i, by
        rw [SimpleGraph.Walk.length_reverse]
        dsimp [i]
        omega, ?_, ?_⟩
    · rw [SimpleGraph.Walk.getVert_reverse]
      have hindex : c.length - i = j + 1 := by
        dsimp [i]
        omega
      simpa [hindex] using hhead
    · rw [SimpleGraph.Walk.getVert_reverse]
      have hindex : c.length - (i + 1) = j := by
        dsimp [i]
        omega
      simpa [hindex] using htail

/-- The other orientation form of
`cycleForwardDart_reverse_iff_backward`. -/
theorem cycleBackwardDart_reverse_iff_forward
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (e : OrientedEdge G) :
    CycleBackwardDart c.reverse e ↔ CycleForwardDart c e := by
  simpa [CycleBackwardDart] using
    (cycleForwardDart_reverse_iff_backward c e.symm)

/-- Backward cycle darts are also determined by their tail vertex. -/
theorem cycleBackwardDart_eq_of_tail_eq
    {V : Type u} {G : SimpleGraph V} {u : V}
    {c : G.Walk u u} (hc : c.IsCycle)
    {e f : OrientedEdge G}
    (he : CycleBackwardDart c e)
    (hf : CycleBackwardDart c f)
    (htail : e.tail = f.tail) :
    e = f := by
  exact cycleForwardDart_eq_of_tail_eq hc.reverse
    ((cycleForwardDart_reverse_iff_backward c e).mpr he)
    ((cycleForwardDart_reverse_iff_backward c f).mpr hf)
    htail

/-- If a walk contains every edge of its graph, every dart is one of the two
orientations of that walk. -/
theorem cycleForward_or_backward_of_spanning
    {V : Type u} {C : SimpleGraph V} {u : V}
    (c : C.Walk u u)
    (hspan : c.toSubgraph.spanningCoe = C)
    (e : OrientedEdge C) :
    CycleForwardDart c e ∨ CycleBackwardDart c e := by
  have hadj : c.toSubgraph.Adj e.tail e.head := by
    change c.toSubgraph.spanningCoe.Adj e.tail e.head
    rw [hspan]
    exact e.adj
  rcases (SimpleGraph.Walk.toSubgraph_adj_iff c).mp hadj with
    ⟨i, hedge, hi⟩
  have horient :
      (c.getVert i = e.tail ∧ c.getVert (i + 1) = e.head) ∨
        (c.getVert i = e.head ∧ c.getVert (i + 1) = e.tail) := by
    simpa only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] using hedge
  rcases horient with horient | horient
  · left
    exact ⟨i, hi, horient.1.symm, horient.2.symm⟩
  · right
    exact ⟨i, hi, horient.1.symm, horient.2.symm⟩

/-- Every vertex on a simple cycle is the tail of a forward cycle dart. -/
theorem exists_cycleForwardDart_of_mem_support
    {V : Type u} {G : SimpleGraph V} {u v : V}
    {c : G.Walk u u} (hc : c.IsCycle)
    (hv : v ∈ c.support) :
    ∃ e : OrientedEdge G,
      CycleForwardDart c e ∧ e.tail = v := by
  rcases (SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv) with
    ⟨i, hiVert, hiLe⟩
  by_cases hi : i < c.length
  · exact
      ⟨cycleDartAt c i hi, cycleDartAt_forward c i hi,
        by simpa using hiVert⟩
  · have hiLength : i = c.length := by omega
    have hzero : c.getVert 0 = v := by
      calc
        c.getVert 0 = c.getVert c.length := by simp
        _ = v := by simpa [hiLength] using hiVert
    have hzeroLt : 0 < c.length := by
      have hlen := hc.three_le_length
      omega
    exact
      ⟨cycleDartAt c 0 hzeroLt,
        cycleDartAt_forward c 0 hzeroLt,
        by simpa using hzero⟩

/-- The first directed edge of a simple cycle. -/
def cycleFirstDart
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    OrientedEdge G :=
  ⟨(c.getVert 0, c.getVert 1),
    c.adj_getVert_succ (by
      have hlen := hc.three_le_length
      omega)⟩

@[simp]
theorem cycleFirstDart_tail
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    (cycleFirstDart c hc).tail = u := by
  change c.getVert 0 = u
  simp

theorem cycleForwardDart_first
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    CycleForwardDart c (cycleFirstDart c hc) := by
  exact ⟨0, by
    have hlen := hc.three_le_length
    omega, rfl, rfl⟩

theorem not_cycleForwardDart_first_symm
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    ¬ CycleForwardDart c (cycleFirstDart c hc).symm := by
  rintro ⟨i, hi, htail, hhead⟩
  have hnext_le : i + 1 <= c.length := by omega
  have hhead_endpoint : c.getVert (i + 1) = u := by
    simpa [cycleFirstDart, cycleDartAt, OrientedEdge.symm,
      OrientedEdge.head] using hhead.symm
  rcases (hc.getVert_endpoint_iff hnext_le).mp hhead_endpoint with hzero | hlast
  · omega
  · have hi_last : i = c.length - 1 := by omega
    have hbad : c.snd = c.penultimate := by
      change c.getVert 1 = c.getVert (c.length - 1)
      rw [← hi_last]
      simpa [cycleFirstDart, cycleDartAt, OrientedEdge.symm,
        OrientedEdge.tail, OrientedEdge.head] using htail
    exact hc.snd_ne_penultimate hbad

/-- The two directed face representatives carried by a simple cycle. -/
def cycleFaceDart
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    Fin 2 -> OrientedEdge G
  | 0 => cycleFirstDart c hc
  | _ => (cycleFirstDart c hc).symm

@[simp]
theorem cycleFaceDart_zero
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    cycleFaceDart c hc 0 = cycleFirstDart c hc :=
  rfl

@[simp]
theorem cycleFaceDart_one
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    cycleFaceDart c hc 1 = (cycleFirstDart c hc).symm :=
  rfl

/-- Either selected directed cycle-face dart has tail connected to the cycle
base point. -/
theorem cycleFaceDart_tail_reachable_start
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle)
    (i : Fin 2) :
    G.Reachable (cycleFaceDart c hc i).tail u := by
  fin_cases i
  · simp
  · have h01 : G.Adj (c.getVert 0) (c.getVert 1) :=
      c.adj_getVert_succ (by
        have hlen := hc.three_le_length
        omega)
    simpa [cycleFaceDart, cycleFirstDart, cycleDartAt] using
      h01.symm.reachable

/-- The cycle base point is connected to the tail of either selected
directed cycle-face dart. -/
theorem cycleFaceDart_start_reachable_tail
    {V : Type u} {G : SimpleGraph V}
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle)
    (i : Fin 2) :
    G.Reachable u (cycleFaceDart c hc i).tail := by
  fin_cases i
  · simp
  · have h01 : G.Adj (c.getVert 0) (c.getVert 1) :=
      c.adj_getVert_succ (by
        have hlen := hc.three_le_length
        omega)
    simpa [cycleFaceDart, cycleFirstDart, cycleDartAt] using h01.reachable


end FourColor

end Schematic.Math.GraphTheory
