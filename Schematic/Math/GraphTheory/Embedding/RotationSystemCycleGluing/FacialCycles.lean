import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.CycleDarts

/-! Facial simple cycles and their local rotation equations. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- A directed simple cycle bounds a face when its forward darts are exactly
the face orbit of its first dart. -/
def IsFacialCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) : Prop :=
  ∀ e : OrientedEdge G,
    CycleForwardDart c e ↔
      PermReachable (R.toHypermap).face (cycleFirstDart c hc) e

namespace IsFacialCycle

/-- The first dart of a simple cycle is forward-oriented. -/
theorem first
    {V : Type u} {G : SimpleGraph V} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle} :
    CycleForwardDart c (cycleFirstDart c hc) :=
  cycleForwardDart_first c hc

/-- The face successor of a forward facial-cycle dart is again a forward
cycle dart. -/
theorem face_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    {e : OrientedEdge G}
    (he : CycleForwardDart c e) :
    CycleForwardDart c ((R.toHypermap).face e) := by
  apply (hfacial ((R.toHypermap).face e)).mpr
  exact PermReachable.trans (R.toHypermap).face
    ((hfacial e).mp he)
    (PermReachable.forward (R.toHypermap).face e)

/-- The forward facial-cycle darts form one face orbit. -/
theorem reachable
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    {e f : OrientedEdge G}
    (he : CycleForwardDart c e)
    (hf : CycleForwardDart c f) :
    PermReachable (R.toHypermap).face e f := by
  exact PermReachable.trans (R.toHypermap).face
    (PermReachable.symm (R.toHypermap).face ((hfacial e).mp he))
    ((hfacial f).mp hf)

end IsFacialCycle

/-- The forward cycle dart entering the vertex at position `i`. -/
def cycleIncomingDart
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (hc : c.IsCycle)
    (i : Nat) (hi : i < c.length) :
    OrientedEdge G :=
  if hzero : i = 0 then
    cycleDartAt c (c.length - 1) (by
      have hlen := hc.three_le_length
      omega)
  else
    cycleDartAt c (i - 1) (by omega)

theorem cycleIncomingDart_forward
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (hc : c.IsCycle)
    (i : Nat) (hi : i < c.length) :
    CycleForwardDart c (cycleIncomingDart c hc i hi) := by
  unfold cycleIncomingDart
  split_ifs
  · exact cycleDartAt_forward c (c.length - 1) (by
      have hlen := hc.three_le_length
      omega)
  · exact cycleDartAt_forward c (i - 1) (by omega)

@[simp]
theorem cycleIncomingDart_head
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (hc : c.IsCycle)
    (i : Nat) (hi : i < c.length) :
    (cycleIncomingDart c hc i hi).head = c.getVert i := by
  unfold cycleIncomingDart
  split_ifs with hzero
  · subst i
    have hlast : (c.length - 1) + 1 = c.length := by
      have hlen := hc.three_le_length
      omega
    change c.getVert ((c.length - 1) + 1) = c.getVert 0
    rw [hlast, SimpleGraph.Walk.getVert_length,
      SimpleGraph.Walk.getVert_zero]
  · have hpred : (i - 1) + 1 = i := by omega
    change c.getVert ((i - 1) + 1) = c.getVert i
    rw [hpred]

@[simp]
theorem cycleIncomingDart_symm_tail
    {V : Type u} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (hc : c.IsCycle)
    (i : Nat) (hi : i < c.length) :
    (cycleIncomingDart c hc i hi).symm.tail = c.getVert i := by
  simp

/-- On a facial cycle, the incoming dart's face successor is the outgoing
dart at the same cycle vertex. -/
theorem IsFacialCycle.face_cycleIncomingDart
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    (i : Nat) (hi : i < c.length) :
    (R.toHypermap).face (cycleIncomingDart c hc i hi) =
      cycleDartAt c i hi := by
  apply cycleForwardDart_eq_of_tail_eq hc
  · exact hfacial.face_forward
      (cycleIncomingDart_forward c hc i hi)
  · exact cycleDartAt_forward c i hi
  · rw [RotationSystem.toHypermap_face_tail,
      cycleIncomingDart_head, cycleDartAt_tail]

/-- Local rotation equation for a facial cycle.  This is the exact successor
rewrite used when the two sides of a common cycle are spliced. -/
theorem IsFacialCycle.node_cycleDartAt
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    (i : Nat) (hi : i < c.length) :
    R.node (cycleDartAt c i hi) =
      (cycleIncomingDart c hc i hi).symm := by
  rw [← hfacial.face_cycleIncomingDart i hi]
  change
    R.node (R.node.symm (cycleIncomingDart c hc i hi).symm) =
      (cycleIncomingDart c hc i hi).symm
  simp

/-- The node successor of a forward dart on a facial cycle is the backward
dart at the same vertex. -/
theorem IsFacialCycle.node_forward_backward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    {e : OrientedEdge G}
    (he : CycleForwardDart c e) :
    CycleBackwardDart c (R.node e) := by
  rcases he with ⟨i, hi, htail, hhead⟩
  have heq : e = cycleDartAt c i hi := by
    apply Subtype.ext
    exact Prod.ext htail hhead
  rw [heq, hfacial.node_cycleDartAt i hi]
  simpa [CycleBackwardDart] using
    cycleIncomingDart_forward c hc i hi

/-- Equivalently, the inverse node successor of a backward facial-cycle dart
is forward. -/
theorem IsFacialCycle.node_symm_backward_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    {e : OrientedEdge G}
    (he : CycleBackwardDart c e) :
    CycleForwardDart c (R.node.symm e) := by
  have hforward :=
    hfacial.face_forward (e := e.symm) he
  simpa [RotationSystem.toHypermap, OrientedEdge.edgePerm] using hforward

/-- For the opposite facial orientation, node successors run from backward
boundary darts toward forward boundary darts. -/
theorem IsFacialCycle.node_backward_forward_of_reverse
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c.reverse hc.reverse)
    {e : OrientedEdge G}
    (he : CycleBackwardDart c e) :
    CycleForwardDart c (R.node e) := by
  exact (cycleBackwardDart_reverse_iff_forward c (R.node e)).mp
    (hfacial.node_forward_backward
      ((cycleForwardDart_reverse_iff_backward c e).mpr he))

/-- Inverse node successors for the opposite facial orientation run from
forward boundary darts toward backward boundary darts. -/
theorem IsFacialCycle.node_symm_forward_backward_of_reverse
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c.reverse hc.reverse)
    {e : OrientedEdge G}
    (he : CycleForwardDart c e) :
    CycleBackwardDart c (R.node.symm e) := by
  exact (cycleForwardDart_reverse_iff_backward c (R.node.symm e)).mp
    (hfacial.node_symm_backward_forward
      ((cycleBackwardDart_reverse_iff_forward c e).mpr he))

end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
