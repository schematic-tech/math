import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.CrossTransport

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem leftSide_disjoint_path {S : GeneralSociety V} {P : GMIX24CutPath S}
    (D : GMIX24Split S P) :
    Disjoint D.leftSide P.pathSet := by
  rw [Set.disjoint_left]
  intro v hvLeft hvPath
  exact (D.leftSide_subset_outside hvLeft).2 hvPath

theorem rightSide_disjoint_path {S : GeneralSociety V} {P : GMIX24CutPath S}
    (D : GMIX24Split S P) :
    Disjoint D.rightSide P.pathSet := by
  rw [Set.disjoint_left]
  intro v hvRight hvPath
  exact (D.rightSide_subset_outside hvRight).2 hvPath

theorem leftBoundaryArc_disjoint_right {S : GeneralSociety V}
    {P : GMIX24CutPath S} (D : GMIX24Split S P) :
    Disjoint D.rightBoundaryArc D.leftBoundaryArc := by
  simpa [disjoint_comm] using D.leftBoundaryArc_disjoint.symm

theorem left_right_support_inter_subset_pathSet
    {S : GeneralSociety V} {P : GMIX24CutPath S}
    (D : GMIX24Split S P) :
    D.leftSociety.graph.support ∩ D.rightSociety.graph.support ⊆
      P.pathSet := by
  intro v hv
  have hvLeft := D.leftSociety_vertices hv.1
  have hvRight := D.rightSociety_vertices hv.2
  rcases hvLeft with hvLeftSide | hvPath
  · rcases hvRight with hvRightSide | hvPath
    · exact False.elim
        (Set.disjoint_left.mp D.sides_disjoint hvLeftSide hvRightSide)
    · exact hvPath
  · exact hvPath

theorem canonicalOfNoCross_leftSociety_activeSet_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.activeSet ⊆
      P.leftSide ∪ P.pathSet := by
  intro v hv
  dsimp [GeneralSociety.activeSet] at hv
  rcases hv with hvSupport | hvBoundary
  · exact
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices
        hvSupport
  · have hvCut : v ∈ P.leftCutBoundarySet := by
      simpa using hvBoundary
    rcases hvCut with hvArc | hvPath
    · exact Or.inl (P.leftBoundaryArc_subset_leftSide hvArc)
    · exact Or.inr hvPath

theorem canonicalOfNoCross_rightSociety_activeSet_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.activeSet ⊆
      P.rightSide ∪ P.pathSet := by
  intro v hv
  dsimp [GeneralSociety.activeSet] at hv
  rcases hv with hvSupport | hvBoundary
  · exact
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_vertices
        hvSupport
  · have hvCut : v ∈ P.rightCutBoundarySet := by
      simpa using hvBoundary
    rcases hvCut with hvArc | hvPath
    · exact Or.inl (P.rightBoundaryArc_subset_rightSide hvArc)
    · exact Or.inr hvPath

theorem canonicalOfNoCross_leftSociety_activeSet_disjoint_rightSide
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    Disjoint
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.activeSet
      P.rightSide := by
  rw [Set.disjoint_left]
  intro v hvActive hvRight
  rcases
      GMIX24Split.canonicalOfNoCross_leftSociety_activeSet_subset_side_or_path
        P hno_cross hvActive with hvLeft | hvPath
  · exact Set.disjoint_left.mp
      (P.leftSide_disjoint_rightSide_of_no_cross hno_cross)
      hvLeft hvRight
  · exact (P.rightSide_subset_outside hvRight).2
      (by simpa [GMIX24CutPath.pathSet] using hvPath)

theorem canonicalOfNoCross_rightSociety_activeSet_disjoint_leftSide
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    Disjoint
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.activeSet
      P.leftSide := by
  rw [Set.disjoint_left]
  intro v hvActive hvLeft
  rcases
      GMIX24Split.canonicalOfNoCross_rightSociety_activeSet_subset_side_or_path
        P hno_cross hvActive with hvRight | hvPath
  · exact Set.disjoint_left.mp
      (P.leftSide_disjoint_rightSide_of_no_cross hno_cross).symm
      hvRight hvLeft
  · exact (P.leftSide_subset_outside hvLeft).2
      (by simpa [GMIX24CutPath.pathSet] using hvPath)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

