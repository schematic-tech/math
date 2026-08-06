import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.BoundaryArcs

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

def leftSide [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : Set V :=
  ComponentUnionMeeting S.graph P.leftBoundaryArc P.outside

def rightSide [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : Set V :=
  ComponentUnionMeeting S.graph P.rightBoundaryArc P.outside

@[simp]
theorem reverse_pathSet [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.pathSet = P.pathSet := by
  ext v
  simp [pathSet, reverse, SimpleGraph.Walk.support_reverse]

@[simp]
theorem reverse_outside [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.outside = P.outside := by
  ext v
  simp [outside, reverse, SimpleGraph.Walk.support_reverse]

@[simp]
theorem reverse_leftBoundaryArc [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.leftBoundaryArc = P.rightBoundaryArc := by
  rfl

@[simp]
theorem reverse_rightBoundaryArc [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.rightBoundaryArc = P.leftBoundaryArc := by
  rfl

@[simp]
theorem reverse_leftSide [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.leftSide = P.rightSide := by
  simp [leftSide, rightSide]

@[simp]
theorem reverse_rightSide [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.rightSide = P.leftSide := by
  simp [leftSide, rightSide]

def leftCutBoundarySet [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : Set V :=
  P.leftBoundaryArc ∪ P.pathSet

def rightCutBoundarySet [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : Set V :=
  P.rightBoundaryArc ∪ P.pathSet

@[simp]
theorem reverse_leftCutBoundarySet [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.reverse.leftCutBoundarySet = P.rightCutBoundarySet := by
  simp [leftCutBoundarySet, rightCutBoundarySet]

@[simp]
theorem reverse_rightCutBoundarySet [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.reverse.rightCutBoundarySet = P.leftCutBoundarySet := by
  simp [leftCutBoundarySet, rightCutBoundarySet]

theorem leftCutBoundarySet_finite [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftCutBoundarySet.Finite :=
  P.leftBoundaryArc_finite.union P.pathSet_finite

theorem rightCutBoundarySet_finite [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightCutBoundarySet.Finite :=
  P.rightBoundaryArc_finite.union P.pathSet_finite

noncomputable def leftCutBoundary [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : CyclicBoundary V :=
  CyclicBoundary.ofFiniteSet P.leftCutBoundarySet
    P.leftCutBoundarySet_finite

noncomputable def rightCutBoundary [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : CyclicBoundary V :=
  CyclicBoundary.ofFiniteSet P.rightCutBoundarySet
    P.rightCutBoundarySet_finite

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
