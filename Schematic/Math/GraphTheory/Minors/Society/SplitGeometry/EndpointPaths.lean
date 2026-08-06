import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.TriangleCover

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Endpoint-path package for the common-branch mixed Kuratowski tag cases.

The three paths start at the common branch vertex `C.z` and run to one concrete
endpoint of each localized mixed host edge.  Their supports stay on the
corresponding strict-subdivision source-edge paths, so the common-branch
uniqueness lemmas make their internal vertices pairwise disjoint. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  right_target : V
  right_path : S.graph.Walk C.z right_target
  right_isPath : right_path.IsPath
  right_support_subset :
    forall w : V, w ∈ right_path.support -> w ∈ D.right_or_path.supportSet
  right_target_mem : right_target ∈ P.rightSide ∪ P.pathSet
  left_target : V
  left_path : S.graph.Walk C.z left_target
  left_isPath : left_path.IsPath
  left_support_subset :
    forall w : V, w ∈ left_path.support -> w ∈ D.left_or_path.supportSet
  left_target_mem : left_target ∈ P.leftSide ∪ P.pathSet
  side_target : V
  side_path : S.graph.Walk C.z side_target
  side_isPath : side_path.IsPath
  side_support_subset :
    forall w : V, w ∈ side_path.support -> w ∈ D.left_or_right.supportSet
  side_target_mem : side_target ∈ (P.leftSide ∪ P.rightSide) ∪ P.pathSet
  right_left_internal_disjoint :
    Disjoint (Walk.InternalVertices right_path) (Walk.InternalVertices left_path)
  right_side_internal_disjoint :
    Disjoint (Walk.InternalVertices right_path) (Walk.InternalVertices side_path)
  left_side_internal_disjoint :
    Disjoint (Walk.InternalVertices left_path) (Walk.InternalVertices side_path)

/-- One chosen endpoint path for the right-or-path localized mixed edge. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath
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
  target_mem : target ∈ P.rightSide ∪ P.pathSet

/-- One chosen endpoint path for the left-or-path localized mixed edge. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath
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
  target_mem : target ∈ P.leftSide ∪ P.pathSet

/-- One chosen endpoint path for the left-or-right localized mixed edge. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath
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
  target_mem : target ∈ (P.leftSide ∪ P.rightSide) ∪ P.pathSet

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.mem_pathSet_of_mem_leftSide
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath)
    (hleft : R.target ∈ P.leftSide) :
    R.target ∈ P.pathSet := by
  rcases R.target_mem with hright | hpath
  · exact False.elim
      (Set.disjoint_left.mp
        (P.leftSide_disjoint_rightSide_of_no_cross hno_cross) hleft hright)
  · exact hpath

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.mem_pathSet_of_mem_rightSide
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath)
    (hright : L.target ∈ P.rightSide) :
    L.target ∈ P.pathSet := by
  rcases L.target_mem with hleft | hpath
  · exact False.elim
      (Set.disjoint_left.mp
        (P.leftSide_disjoint_rightSide_of_no_cross hno_cross) hleft hright)
  · exact hpath

/-- The target of a selected right endpoint path lies on its tagged
strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.target_mem_supportSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath) :
    R.target ∈ D.right_or_path.supportSet :=
  R.support_subset R.target R.path.end_mem_support

/-- The target of a selected left endpoint path lies on its tagged
strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.target_mem_supportSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath) :
    L.target ∈ D.left_or_path.supportSet :=
  L.support_subset L.target L.path.end_mem_support

/-- The target of a selected side endpoint path lies on its tagged
strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.target_mem_supportSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath) :
    E.target ∈ D.left_or_right.supportSet :=
  E.support_subset E.target E.path.end_mem_support

/-- Segment on the right tagged source-edge support from a source branch
vertex to a selected right endpoint-path target. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.exists_support_path_from_source_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath)
    {v : W}
    (hv : v = D.right_or_path.x ∨ v = D.right_or_path.y) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex v) R.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.right_or_path.supportSet :=
  D.right_or_path.exists_support_path_between
    (D.right_or_path.branchVertex_mem_supportSet_of_endpoint hv)
    R.target_mem_supportSet

/-- Segment on the right tagged source-edge support from a source branch
vertex to any vertex on a selected right endpoint path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.exists_support_path_from_source_endpoint_to_path_vertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath)
    {v : W}
    (hv : v = D.right_or_path.x ∨ v = D.right_or_path.y)
    {x : V}
    (hx : x ∈ R.path.support) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex v) x =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.right_or_path.supportSet :=
  D.right_or_path.exists_support_path_between
    (D.right_or_path.branchVertex_mem_supportSet_of_endpoint hv)
    (R.support_subset x hx)

/-- Segment on the left tagged source-edge support from a source branch
vertex to a selected left endpoint-path target. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.exists_support_path_from_source_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath)
    {v : W}
    (hv : v = D.left_or_path.x ∨ v = D.left_or_path.y) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex v) L.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_path.supportSet :=
  D.left_or_path.exists_support_path_between
    (D.left_or_path.branchVertex_mem_supportSet_of_endpoint hv)
    L.target_mem_supportSet

/-- Segment on the left tagged source-edge support from a source branch
vertex to any vertex on a selected left endpoint path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.exists_support_path_from_source_endpoint_to_path_vertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath)
    {v : W}
    (hv : v = D.left_or_path.x ∨ v = D.left_or_path.y)
    {x : V}
    (hx : x ∈ L.path.support) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex v) x =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_path.supportSet :=
  D.left_or_path.exists_support_path_between
    (D.left_or_path.branchVertex_mem_supportSet_of_endpoint hv)
    (L.support_subset x hx)

/-- Segment on the side tagged source-edge support from a source branch vertex
to a selected side endpoint-path target. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.exists_support_path_from_source_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath)
    {v : W}
    (hv : v = D.left_or_right.x ∨ v = D.left_or_right.y) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex v) E.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_right.supportSet :=
  D.left_or_right.exists_support_path_between
    (D.left_or_right.branchVertex_mem_supportSet_of_endpoint hv)
    E.target_mem_supportSet

/-- Segment on the side tagged source-edge support from a source branch vertex
to any vertex on a selected side endpoint path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.exists_support_path_from_source_endpoint_to_path_vertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath)
    {v : W}
    (hv : v = D.left_or_right.x ∨ v = D.left_or_right.y)
    {x : V}
    (hx : x ∈ E.path.support) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex v) x =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_right.supportSet :=
  D.left_or_right.exists_support_path_between
    (D.left_or_right.branchVertex_mem_supportSet_of_endpoint hv)
    (E.support_subset x hx)

/-- Clean right-side tail from a selected right endpoint path to the right
boundary arc. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.exists_clean_tail_to_rightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath)
    (hright : R.target ∈ P.rightSide) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ R.path.support ∧
            a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ R.path.support -> w = x :=
  P.exists_clean_tail_from_path_target_to_rightBoundaryArc
    hno_cross R.path hright

/-- Clean left-side tail from a selected left endpoint path to the left
boundary arc. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.exists_clean_tail_to_leftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath)
    (hleft : L.target ∈ P.leftSide) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ L.path.support ∧
            a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ L.path.support -> w = x :=
  P.exists_clean_tail_from_path_target_to_leftBoundaryArc
    hno_cross L.path hleft

/-- Clean left-side tail from a selected side endpoint path to the left
boundary arc. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.exists_clean_tail_to_leftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath)
    (hleft : E.target ∈ P.leftSide) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ E.path.support ∧
            a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ E.path.support -> w = x :=
  P.exists_clean_tail_from_path_target_to_leftBoundaryArc
    hno_cross E.path hleft

/-- Clean right-side tail from a selected side endpoint path to the right
boundary arc. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.exists_clean_tail_to_rightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath)
    (hright : E.target ∈ P.rightSide) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ E.path.support ∧
            a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ E.path.support -> w = x :=
  P.exists_clean_tail_from_path_target_to_rightBoundaryArc
    hno_cross E.path hright

/-- A selected right endpoint either admits the clean right-side tail, or its
target is on the cut path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.clean_tail_to_rightBoundaryArc_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ R.path.support ∧
            a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ R.path.support -> w = x) ∨
      R.target ∈ P.pathSet := by
  rcases R.target_mem with hright | hpath
  · exact Or.inl (R.exists_clean_tail_to_rightBoundaryArc hright)
  · exact Or.inr hpath

/-- A selected left endpoint either admits the clean left-side tail, or its
target is on the cut path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.clean_tail_to_leftBoundaryArc_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ L.path.support ∧
            a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ L.path.support -> w = x) ∨
      L.target ∈ P.pathSet := by
  rcases L.target_mem with hleft | hpath
  · exact Or.inl (L.exists_clean_tail_to_leftBoundaryArc hleft)
  · exact Or.inr hpath

/-- A selected side endpoint admits a clean tail to the side on which its
target lies, unless the target is on the cut path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.clean_tail_to_boundaryArc_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath) :
    ((Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ E.path.support ∧
            a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ E.path.support -> w = x) ∨
      (Exists fun x : V =>
        Exists fun a : V =>
          Exists fun tail : S.graph.Walk x a =>
            x ∈ E.path.support ∧
              a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
                  (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                    Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                      forall w : V,
                        w ∈ tail.support -> w ∈ E.path.support -> w = x)) ∨
        E.target ∈ P.pathSet := by
  rcases E.target_mem with hside | hpath
  · rcases hside with hleft | hright
    · exact Or.inl (Or.inl (E.exists_clean_tail_to_leftBoundaryArc hleft))
    · exact Or.inl (Or.inr (E.exists_clean_tail_to_rightBoundaryArc hright))
  · exact Or.inr hpath


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
