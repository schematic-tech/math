import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.EndpointChoiceIntersections

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

/-- An edge belongs to `G` and both of its endpoints lie in `region`. -/
def EdgeLocalizedTo (e : Sym2 V) (G : SimpleGraph V) (region : Set V) : Prop :=
  e ∈ G.edgeSet ∧ e.out.1 ∈ region ∧ e.out.2 ∈ region

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEdgeTag
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Prop :=
  let _ := C
  D.right_or_path.e ∈
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
    D.right_or_path.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
      D.right_or_path.e.out.2 ∈ P.rightSide ∪ P.pathSet

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightPathTag
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Prop :=
  let _ := C
  D.right_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
    D.right_or_path.e.out.1 ∈ P.pathSet ∧
      D.right_or_path.e.out.2 ∈ P.pathSet

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEdgeTag
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Prop :=
  let _ := C
  D.left_or_path.e ∈
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
    D.left_or_path.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
      D.left_or_path.e.out.2 ∈ P.leftSide ∪ P.pathSet

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftPathTag
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Prop :=
  let _ := C
  D.left_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
    D.left_or_path.e.out.1 ∈ P.pathSet ∧
      D.left_or_path.e.out.2 ∈ P.pathSet

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideLeftTag
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Prop :=
  let _ := C
  D.left_or_right.e ∈
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
    D.left_or_right.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
      D.left_or_right.e.out.2 ∈ P.leftSide ∪ P.pathSet

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideRightTag
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Prop :=
  let _ := C
  D.left_or_right.e ∈
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
    D.left_or_right.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
      D.left_or_right.e.out.2 ∈ P.rightSide ∪ P.pathSet

/-- Endpoint path on the right-or-path witness whose target is known to lie
on the cut path. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightPathEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  target : V
  path : S.graph.Walk C.z target
  isPath : path.IsPath
  support_subset :
    forall w : V, w ∈ path.support -> w ∈ D.right_or_path.supportSet
  target_mem_path : target ∈ P.pathSet

/-- Endpoint path on the left-or-path witness whose target is known to lie
on the cut path. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftPathEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  target : V
  path : S.graph.Walk C.z target
  isPath : path.IsPath
  support_subset :
    forall w : V, w ∈ path.support -> w ∈ D.left_or_path.supportSet
  target_mem_path : target ∈ P.pathSet

/-- Endpoint path on the left-or-right witness whose target is on the left
side or the cut path. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideLeftEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  target : V
  path : S.graph.Walk C.z target
  isPath : path.IsPath
  support_subset :
    forall w : V, w ∈ path.support -> w ∈ D.left_or_right.supportSet
  target_mem_left_or_path : target ∈ P.leftSide ∪ P.pathSet

/-- Endpoint path on the left-or-right witness whose target is on the right
side or the cut path. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideRightEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  target : V
  path : S.graph.Walk C.z target
  isPath : path.IsPath
  support_subset :
    forall w : V, w ∈ path.support -> w ∈ D.left_or_right.supportSet
  target_mem_right_or_path : target ∈ P.rightSide ∪ P.pathSet

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideLeftEndpointPath.mem_pathSet_of_mem_rightSide
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideLeftEndpointPath)
    (hright : E.target ∈ P.rightSide) :
    E.target ∈ P.pathSet := by
  rcases E.target_mem_left_or_path with hleft | hpath
  · exact False.elim
      (Set.disjoint_left.mp
        (P.leftSide_disjoint_rightSide_of_no_cross hno_cross) hleft hright)
  · exact hpath

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideRightEndpointPath.mem_pathSet_of_mem_leftSide
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideRightEndpointPath)
    (hleft : E.target ∈ P.leftSide) :
    E.target ∈ P.pathSet := by
  rcases E.target_mem_right_or_path with hright | hpath
  · exact False.elim
      (Set.disjoint_left.mp
        (P.leftSide_disjoint_rightSide_of_no_cross hno_cross) hleft hright)
  · exact hpath

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightPathEndpointPath.toRightEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightPathEndpointPath) :
    C.RightEndpointPath where
  target := R.target
  path := R.path
  isPath := R.isPath
  support_subset := R.support_subset
  target_mem := Or.inr R.target_mem_path

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftPathEndpointPath.toLeftEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftPathEndpointPath) :
    C.LeftEndpointPath where
  target := L.target
  path := L.path
  isPath := L.isPath
  support_subset := L.support_subset
  target_mem := Or.inr L.target_mem_path

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideLeftEndpointPath.toSideEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideLeftEndpointPath) :
    C.SideEndpointPath where
  target := E.target
  path := E.path
  isPath := E.isPath
  support_subset := E.support_subset
  target_mem := by
    rcases E.target_mem_left_or_path with hleft | hpath
    · exact Or.inl (Or.inl hleft)
    · exact Or.inr hpath

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideRightEndpointPath.toSideEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideRightEndpointPath) :
    C.SideEndpointPath where
  target := E.target
  path := E.path
  isPath := E.isPath
  support_subset := E.support_subset
  target_mem := by
    rcases E.target_mem_right_or_path with hright | hpath
    · exact Or.inl (Or.inr hright)
    · exact Or.inr hpath

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.rightFstPathEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (h : C.RightPathTag) :
    C.RightPathEndpointPath where
  target := D.right_or_path.e.out.1
  path := C.right_paths.fst_path
  isPath := C.right_paths.fst_isPath
  support_subset := C.right_paths.fst_support_subset
  target_mem_path := h.2.1

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.rightSndPathEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (h : C.RightPathTag) :
    C.RightPathEndpointPath where
  target := D.right_or_path.e.out.2
  path := C.right_paths.snd_path
  isPath := C.right_paths.snd_isPath
  support_subset := C.right_paths.snd_support_subset
  target_mem_path := h.2.2

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.leftFstPathEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (h : C.LeftPathTag) :
    C.LeftPathEndpointPath where
  target := D.left_or_path.e.out.1
  path := C.left_paths.fst_path
  isPath := C.left_paths.fst_isPath
  support_subset := C.left_paths.fst_support_subset
  target_mem_path := h.2.1

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.leftSndPathEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (h : C.LeftPathTag) :
    C.LeftPathEndpointPath where
  target := D.left_or_path.e.out.2
  path := C.left_paths.snd_path
  isPath := C.left_paths.snd_isPath
  support_subset := C.left_paths.snd_support_subset
  target_mem_path := h.2.2

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideFstLeftEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (h : C.SideLeftTag) :
    C.SideLeftEndpointPath where
  target := D.left_or_right.e.out.1
  path := C.side_paths.fst_path
  isPath := C.side_paths.fst_isPath
  support_subset := C.side_paths.fst_support_subset
  target_mem_left_or_path := h.2.1

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideSndLeftEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (h : C.SideLeftTag) :
    C.SideLeftEndpointPath where
  target := D.left_or_right.e.out.2
  path := C.side_paths.snd_path
  isPath := C.side_paths.snd_isPath
  support_subset := C.side_paths.snd_support_subset
  target_mem_left_or_path := h.2.2

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideFstRightEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (h : C.SideRightTag) :
    C.SideRightEndpointPath where
  target := D.left_or_right.e.out.1
  path := C.side_paths.fst_path
  isPath := C.side_paths.fst_isPath
  support_subset := C.side_paths.fst_support_subset
  target_mem_right_or_path := h.2.1

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideSndRightEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (h : C.SideRightTag) :
    C.SideRightEndpointPath where
  target := D.left_or_right.e.out.2
  path := C.side_paths.snd_path
  isPath := C.side_paths.snd_isPath
  support_subset := C.side_paths.snd_support_subset
  target_mem_right_or_path := h.2.2

/-- The canonical nontrivial right endpoint choice stays on the cut path when
the right-or-path tagged edge is a path edge. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialRightEndpointPath_target_mem_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    (h : C.RightPathTag) :
    C.nontrivialRightEndpointPath.endpoint.target ∈ P.pathSet := by
  classical
  unfold MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialRightEndpointPath
  by_cases hfst : D.right_or_path.e.out.1 = C.z
  · simpa [hfst,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.rightSndEndpointPath]
      using h.2.2
  · simpa [hfst,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.rightFstEndpointPath]
      using h.2.1

/-- The canonical nontrivial left endpoint choice stays on the cut path when
the left-or-path tagged edge is a path edge. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialLeftEndpointPath_target_mem_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    (h : C.LeftPathTag) :
    C.nontrivialLeftEndpointPath.endpoint.target ∈ P.pathSet := by
  classical
  unfold MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialLeftEndpointPath
  by_cases hfst : D.left_or_path.e.out.1 = C.z
  · simpa [hfst,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.leftSndEndpointPath]
      using h.2.2
  · simpa [hfst,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.leftFstEndpointPath]
      using h.2.1

/-- The canonical nontrivial side endpoint choice stays on the left side or
the cut path when the side tagged edge is left-localized. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialSideEndpointPath_target_mem_left_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    (h : C.SideLeftTag) :
    C.nontrivialSideEndpointPath.endpoint.target ∈ P.leftSide ∪ P.pathSet := by
  classical
  unfold MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialSideEndpointPath
  by_cases hfst : D.left_or_right.e.out.1 = C.z
  · simpa [hfst,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideSndEndpointPath]
      using h.2.2
  · simpa [hfst,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideFstEndpointPath]
      using h.2.1

/-- The canonical nontrivial side endpoint choice stays on the right side or
the cut path when the side tagged edge is right-localized. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialSideEndpointPath_target_mem_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    (h : C.SideRightTag) :
    C.nontrivialSideEndpointPath.endpoint.target ∈ P.rightSide ∪ P.pathSet := by
  classical
  unfold MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialSideEndpointPath
  by_cases hfst : D.left_or_right.e.out.1 = C.z
  · simpa [hfst,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideSndEndpointPath]
      using h.2.2
  · simpa [hfst,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideFstEndpointPath]
      using h.2.1

/-- The canonical nontrivial common-branch right endpoint choice is on the
cut path in the `pathRight` tag cases. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_right_target_mem_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (h : C.RightPathTag) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
      P.pathSet := by
  classical
  unfold MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices
  simpa using C.nontrivialRightEndpointPath_target_mem_path h

/-- The canonical nontrivial common-branch left endpoint choice is on the
cut path in the `pathLeft` tag cases. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_left_target_mem_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (h : C.LeftPathTag) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
      P.pathSet := by
  classical
  unfold MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices
  simpa using C.nontrivialLeftEndpointPath_target_mem_path h

/-- The canonical nontrivial common-branch side endpoint choice is on the
left side or cut path in the `sideLeft` tag cases. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_side_target_mem_left_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (h : C.SideLeftTag) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
      P.leftSide ∪ P.pathSet := by
  classical
  unfold MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices
  simpa using C.nontrivialSideEndpointPath_target_mem_left_or_path h

/-- The canonical nontrivial common-branch side endpoint choice is on the
right side or cut path in the `sideRight` tag cases. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_side_target_mem_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (h : C.SideRightTag) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
      P.rightSide ∪ P.pathSet := by
  classical
  unfold MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices
  simpa using C.nontrivialSideEndpointPath_target_mem_right_or_path h

/-- The canonical nontrivial common-branch right and left targets are
distinct. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_right_left_target_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ≠
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target := by
  classical
  exact
    (C.commonBranchNontrivialEndpointPathChoices A).right_left_target_ne A

/-- The canonical nontrivial common-branch right and side targets are
distinct. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_right_side_target_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ≠
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target := by
  classical
  exact
    (C.commonBranchNontrivialEndpointPathChoices A).right_side_target_ne A

/-- The canonical nontrivial common-branch left and side targets are
distinct. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_left_side_target_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ≠
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target := by
  classical
  exact
    (C.commonBranchNontrivialEndpointPathChoices A).left_side_target_ne A

/-- The canonical nontrivial right endpoint in a common-branch package either
has the clean right-side tail required by the source proof, or its target lies
on the cut path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_right_cleanTail_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.right.CleanTailToRightBoundaryArc ∨
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈ P.pathSet := by
  exact
    (C.commonBranchNontrivialEndpointPathChoices A).choices.right.cleanTailToRightBoundaryArc_or_pathSet

/-- The canonical nontrivial left endpoint in a common-branch package either
has the clean left-side tail required by the source proof, or its target lies
on the cut path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_left_cleanTail_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (C.commonBranchNontrivialEndpointPathChoices A).choices.left.CleanTailToLeftBoundaryArc ∨
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈ P.pathSet := by
  exact
    (C.commonBranchNontrivialEndpointPathChoices A).choices.left.cleanTailToLeftBoundaryArc_or_pathSet

/-- The canonical nontrivial side endpoint in a common-branch package either
has a clean tail to the side on which it lies, or its target lies on the cut
path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_side_cleanTail_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (((C.commonBranchNontrivialEndpointPathChoices A).choices.side.CleanTailToLeftBoundaryArc ∨
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.CleanTailToRightBoundaryArc) ∨
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈ P.pathSet) := by
  exact
    (C.commonBranchNontrivialEndpointPathChoices A).choices.side.cleanTailToBoundaryArc_or_pathSet


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
