import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.CycleSumConstruction

/-! Face-orbit remainders after removing the two glued facial disks. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- The face orbit selected by a facial cycle. -/
noncomputable def selectedCycleFace
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    (R.toHypermap).FaceOrbit :=
  PermOrbit.of (R.toHypermap).face (cycleFirstDart c hc)

theorem faceOrbit_eq_selectedCycleFace_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    (e : OrientedEdge G) :
    PermOrbit.of (R.toHypermap).face e =
        selectedCycleFace R c hc ↔
      CycleForwardDart c e := by
  constructor
  · intro heq
    apply (hfacial e).mpr
    exact PermReachable.symm (R.toHypermap).face
      (Quotient.exact heq)
  · intro he
    exact (PermOrbit.of_eq_of (R.toHypermap).face
      ((hfacial e).mp he)).symm

theorem IsFacialCycle.not_forward_face_of_not_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    {e : OrientedEdge G}
    (he : ¬ CycleForwardDart c e) :
    ¬ CycleForwardDart c ((R.toHypermap).face e) := by
  intro hface
  apply he
  apply (hfacial e).mpr
  exact PermReachable.trans (R.toHypermap).face
    ((hfacial ((R.toHypermap).face e)).mp hface)
    (by
      simpa using
        PermReachable.backward (R.toHypermap).face
          ((R.toHypermap).face e))

theorem IsFacialCycle.not_forward_of_reachable_of_not_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    {e f : OrientedEdge G}
    (he : ¬ CycleForwardDart c e)
    (hef : PermReachable (R.toHypermap).face e f) :
    ¬ CycleForwardDart c f := by
  intro hf
  apply he
  apply (hfacial e).mpr
  exact PermReachable.trans (R.toHypermap).face
    ((hfacial f).mp hf)
    (PermReachable.symm (R.toHypermap).face hef)

theorem faceOrbit_ne_selectedCycleFace_of_not_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c hc)
    {e : OrientedEdge G}
    (he : ¬ CycleForwardDart c e) :
    PermOrbit.of (R.toHypermap).face e ≠
      selectedCycleFace R c hc := by
  intro heq
  exact he ((faceOrbit_eq_selectedCycleFace_iff hfacial e).mp heq)

theorem faceOrbit_ne_selectedReverseFace_of_not_backward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c.reverse hc.reverse)
    {e : OrientedEdge G}
    (he : ¬ CycleBackwardDart c e) :
    PermOrbit.of (R.toHypermap).face e ≠
      selectedCycleFace R c.reverse hc.reverse := by
  intro heq
  apply he
  exact (cycleForwardDart_reverse_iff_backward c e).mp
    ((faceOrbit_eq_selectedCycleFace_iff hfacial e).mp heq)

theorem IsFacialCycle.not_backward_face_of_not_backward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c.reverse hc.reverse)
    {e : OrientedEdge G}
    (he : ¬ CycleBackwardDart c e) :
    ¬ CycleBackwardDart c ((R.toHypermap).face e) := by
  have hnotForward :
      ¬ CycleForwardDart c.reverse e := by
    simpa [cycleForwardDart_reverse_iff_backward] using he
  have hnotForwardFace :=
    hfacial.not_forward_face_of_not_forward hnotForward
  simpa [cycleForwardDart_reverse_iff_backward] using hnotForwardFace

theorem IsFacialCycle.not_backward_of_reachable_of_not_backward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {u : V}
    {c : G.Walk u u} {hc : c.IsCycle}
    (hfacial : IsFacialCycle R c.reverse hc.reverse)
    {e f : OrientedEdge G}
    (he : ¬ CycleBackwardDart c e)
    (hef : PermReachable (R.toHypermap).face e f) :
    ¬ CycleBackwardDart c f := by
  have hnotForward :
      ¬ CycleForwardDart c.reverse e := by
    simpa [cycleForwardDart_reverse_iff_backward] using he
  have hnotForwardF :=
    hfacial.not_forward_of_reachable_of_not_forward hnotForward hef
  simpa [cycleForwardDart_reverse_iff_backward] using hnotForwardF

end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
