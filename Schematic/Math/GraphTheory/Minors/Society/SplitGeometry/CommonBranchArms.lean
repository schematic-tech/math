import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.TaggedWitnesses

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- The common-support geometric datum for a mixed Kuratowski package,
together with the side/path tags of the three concrete host edges.

This is the source-proof shape needed after the pairwise strict-subdivision
alternatives have been reduced to a common source endpoint: the common endpoint
gives a common host vertex on all three supports, and the tags say which side of
the cut each host edge occupies. -/
def MixedEdgeTaggedSupportData.CommonSupportWithEndpointRegions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) : Prop :=
  Exists fun z : V =>
    z ∈ D.right_or_path.supportSet ∧
      z ∈ D.left_or_path.supportSet ∧
        z ∈ D.left_or_right.supportSet ∧
          (((D.right_or_path.e ∈
                (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
              D.right_or_path.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
              D.right_or_path.e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
              (D.right_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
                D.right_or_path.e.out.1 ∈ P.pathSet ∧
                D.right_or_path.e.out.2 ∈ P.pathSet)) ∧
            (((D.left_or_path.e ∈
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
                D.left_or_path.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                D.left_or_path.e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (D.left_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
                  D.left_or_path.e.out.1 ∈ P.pathSet ∧
                  D.left_or_path.e.out.2 ∈ P.pathSet)) ∧
              ((D.left_or_right.e ∈
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
                D.left_or_right.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                D.left_or_right.e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (D.left_or_right.e ∈
                  (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
                D.left_or_right.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                D.left_or_right.e.out.2 ∈ P.rightSide ∪ P.pathSet))))

/-- A common-support mixed package with actual strict-subdivision subpaths from
the common support vertex to both endpoints of each tagged host edge. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    Type _ where
  z : V
  z_right : z ∈ D.right_or_path.supportSet
  z_left : z ∈ D.left_or_path.supportSet
  z_side : z ∈ D.left_or_right.supportSet
  right_paths :
    GMIX24Split.TaggedSupportWitnessData.EndpointPathPair
      D.right_or_path z
  left_paths :
    GMIX24Split.TaggedSupportWitnessData.EndpointPathPair
      D.left_or_path z
  side_paths :
    GMIX24Split.TaggedSupportWitnessData.EndpointPathPair
      D.left_or_right z
  right_or_path_regions :
    ((D.right_or_path.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
        D.right_or_path.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
        D.right_or_path.e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
      (D.right_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
        D.right_or_path.e.out.1 ∈ P.pathSet ∧
        D.right_or_path.e.out.2 ∈ P.pathSet))
  left_or_path_regions :
    ((D.left_or_path.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
        D.left_or_path.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
        D.left_or_path.e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
      (D.left_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
        D.left_or_path.e.out.1 ∈ P.pathSet ∧
        D.left_or_path.e.out.2 ∈ P.pathSet))
  left_or_right_regions :
    ((D.left_or_right.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
        D.left_or_right.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
        D.left_or_right.e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
      (D.left_or_right.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
        D.left_or_right.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
        D.left_or_right.e.out.2 ∈ P.rightSide ∪ P.pathSet))

noncomputable def MixedEdgeTaggedSupportData.commonSupportEndpointPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK)
    (H : D.CommonSupportWithEndpointRegions) :
    D.CommonSupportEndpointPaths := by
  classical
  let z := Classical.choose H
  have hspec := Classical.choose_spec H
  have hzR : z ∈ D.right_or_path.supportSet := hspec.1
  have hzL : z ∈ D.left_or_path.supportSet := hspec.2.1
  have hzS : z ∈ D.left_or_right.supportSet := hspec.2.2.1
  have hR := hspec.2.2.2.1
  have hL := hspec.2.2.2.2.1
  have hS := hspec.2.2.2.2.2
  exact {
    z := z
    z_right := hzR
    z_left := hzL
    z_side := hzS
    right_paths := D.right_or_path.endpointPathPair hzR
    left_paths := D.left_or_path.endpointPathPair hzL
    side_paths := D.left_or_right.endpointPathPair hzS
    right_or_path_regions := hR
    left_or_path_regions := hL
    left_or_right_regions := hS
  }

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.right_otherSourceEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc : c = D.right_or_path.x ∨ c = D.right_or_path.y) :
    D.right_or_path.OtherSourceEndpointPath C.z c :=
  D.right_or_path.otherSourceEndpointPath C.z_right hc

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.left_otherSourceEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc : c = D.left_or_path.x ∨ c = D.left_or_path.y) :
    D.left_or_path.OtherSourceEndpointPath C.z c :=
  D.left_or_path.otherSourceEndpointPath C.z_left hc

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.side_otherSourceEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc : c = D.left_or_right.x ∨ c = D.left_or_right.y) :
    D.left_or_right.OtherSourceEndpointPath C.z c :=
  D.left_or_right.otherSourceEndpointPath C.z_side hc

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.right_left_otherSourceEndpoint_ne_of_not_same
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_right : c = D.right_or_path.x ∨ c = D.right_or_path.y)
    (hc_left : c = D.left_or_path.x ∨ c = D.left_or_path.y)
    (hne :
      Not ((D.right_or_path.x = D.left_or_path.x ∧
            D.right_or_path.y = D.left_or_path.y) ∨
          (D.right_or_path.x = D.left_or_path.y ∧
            D.right_or_path.y = D.left_or_path.x))) :
    (C.right_otherSourceEndpointPath hc_right).other ≠
      (C.left_otherSourceEndpointPath hc_left).other := by
  classical
  let R := C.right_otherSourceEndpointPath hc_right
  let L := C.left_otherSourceEndpointPath hc_left
  exact
    two_pair_other_endpoints_ne_of_not_same
      D.right_or_path.hxy.ne D.left_or_path.hxy.ne
      hc_right hc_left R.other_ne R.other_endpoint L.other_ne
      L.other_endpoint hne

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.right_side_otherSourceEndpoint_ne_of_not_same
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_right : c = D.right_or_path.x ∨ c = D.right_or_path.y)
    (hc_side : c = D.left_or_right.x ∨ c = D.left_or_right.y)
    (hne :
      Not ((D.right_or_path.x = D.left_or_right.x ∧
            D.right_or_path.y = D.left_or_right.y) ∨
          (D.right_or_path.x = D.left_or_right.y ∧
            D.right_or_path.y = D.left_or_right.x))) :
    (C.right_otherSourceEndpointPath hc_right).other ≠
      (C.side_otherSourceEndpointPath hc_side).other := by
  classical
  let R := C.right_otherSourceEndpointPath hc_right
  let E := C.side_otherSourceEndpointPath hc_side
  exact
    two_pair_other_endpoints_ne_of_not_same
      D.right_or_path.hxy.ne D.left_or_right.hxy.ne
      hc_right hc_side R.other_ne R.other_endpoint E.other_ne
      E.other_endpoint hne

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.left_side_otherSourceEndpoint_ne_of_not_same
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_left : c = D.left_or_path.x ∨ c = D.left_or_path.y)
    (hc_side : c = D.left_or_right.x ∨ c = D.left_or_right.y)
    (hne :
      Not ((D.left_or_path.x = D.left_or_right.x ∧
            D.left_or_path.y = D.left_or_right.y) ∨
          (D.left_or_path.x = D.left_or_right.y ∧
            D.left_or_path.y = D.left_or_right.x))) :
    (C.left_otherSourceEndpointPath hc_left).other ≠
      (C.side_otherSourceEndpointPath hc_side).other := by
  classical
  let L := C.left_otherSourceEndpointPath hc_left
  let E := C.side_otherSourceEndpointPath hc_side
  exact
    two_pair_other_endpoints_ne_of_not_same
      D.left_or_path.hxy.ne D.left_or_right.hxy.ne
      hc_left hc_side L.other_ne L.other_endpoint E.other_ne
      E.other_endpoint hne

/-- The common-source arm package extracted from a common support vertex.

When the three mixed Kuratowski source edges share a source endpoint `c` and
the three selected source edges are pairwise distinct, the common support
vertex is the branch vertex of `c`.  This package records the three support
subpaths from that branch vertex to the opposite source endpoints, plus the
pairwise distinctness of those opposite endpoints. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) (c : W) : Type _ where
  c_right : c = D.right_or_path.x ∨ c = D.right_or_path.y
  c_left : c = D.left_or_path.x ∨ c = D.left_or_path.y
  c_side : c = D.left_or_right.x ∨ c = D.left_or_right.y
  z_eq_branchVertex : C.z = (Classical.choice hK).branchVertex c
  right_arm : D.right_or_path.OtherSourceEndpointPath C.z c
  left_arm : D.left_or_path.OtherSourceEndpointPath C.z c
  side_arm : D.left_or_right.OtherSourceEndpointPath C.z c
  right_left_other_ne : right_arm.other ≠ left_arm.other
  right_side_other_ne : right_arm.other ≠ side_arm.other
  left_side_other_ne : left_arm.other ≠ side_arm.other

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchArmPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_right : c = D.right_or_path.x ∨ c = D.right_or_path.y)
    (hc_left : c = D.left_or_path.x ∨ c = D.left_or_path.y)
    (hc_side : c = D.left_or_right.x ∨ c = D.left_or_right.y)
    (h_right_left_not_same : Not D.rightLeftSame)
    (h_right_side_not_same : Not D.rightSideSame)
    (h_left_side_not_same : Not D.leftSideSame) :
    C.CommonBranchArmPaths c := by
  classical
  let R := C.right_otherSourceEndpointPath hc_right
  let L := C.left_otherSourceEndpointPath hc_left
  let E := C.side_otherSourceEndpointPath hc_side
  exact {
    c_right := hc_right
    c_left := hc_left
    c_side := hc_side
    z_eq_branchVertex :=
      D.right_or_path.support_inter_eq_common_branchVertex
        D.left_or_path
        (by
          simpa [MixedEdgeTaggedSupportData.rightLeftSame] using
            h_right_left_not_same)
        (two_pair_unique_common_endpoint_of_not_same
          D.right_or_path.hxy.ne D.left_or_path.hxy.ne
          hc_right hc_left
          (by
            simpa [MixedEdgeTaggedSupportData.rightLeftSame] using
              h_right_left_not_same))
        C.z_right C.z_left
    right_arm := R
    left_arm := L
    side_arm := E
    right_left_other_ne := by
      simpa [R, L] using
        C.right_left_otherSourceEndpoint_ne_of_not_same hc_right hc_left
          (by
            simpa [MixedEdgeTaggedSupportData.rightLeftSame] using
              h_right_left_not_same)
    right_side_other_ne := by
      simpa [R, E] using
        C.right_side_otherSourceEndpoint_ne_of_not_same hc_right hc_side
          (by
            simpa [MixedEdgeTaggedSupportData.rightSideSame] using
              h_right_side_not_same)
    left_side_other_ne := by
      simpa [L, E] using
        C.left_side_otherSourceEndpoint_ne_of_not_same hc_left hc_side
          (by
            simpa [MixedEdgeTaggedSupportData.leftSideSame] using
              h_left_side_not_same)
  }

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_other_branchVertex_ne_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (Classical.choice hK).branchVertex A.right_arm.other ≠
      (Classical.choice hK).branchVertex c := by
  intro h
  exact A.right_arm.other_ne
    ((Classical.choice hK).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_other_branchVertex_ne_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (Classical.choice hK).branchVertex A.left_arm.other ≠
      (Classical.choice hK).branchVertex c := by
  intro h
  exact A.left_arm.other_ne
    ((Classical.choice hK).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_other_branchVertex_ne_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (Classical.choice hK).branchVertex A.side_arm.other ≠
      (Classical.choice hK).branchVertex c := by
  intro h
  exact A.side_arm.other_ne
    ((Classical.choice hK).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_left_other_branchVertex_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (Classical.choice hK).branchVertex A.right_arm.other ≠
      (Classical.choice hK).branchVertex A.left_arm.other := by
  intro h
  exact A.right_left_other_ne
    ((Classical.choice hK).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_side_other_branchVertex_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (Classical.choice hK).branchVertex A.right_arm.other ≠
      (Classical.choice hK).branchVertex A.side_arm.other := by
  intro h
  exact A.right_side_other_ne
    ((Classical.choice hK).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_side_other_branchVertex_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    (Classical.choice hK).branchVertex A.left_arm.other ≠
      (Classical.choice hK).branchVertex A.side_arm.other := by
  intro h
  exact A.left_side_other_ne
    ((Classical.choice hK).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_arm_adj_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    K.Adj c A.right_arm.other := by
  rcases A.c_right with hc | hc <;>
    rcases A.right_arm.other_endpoint with hother | hother
  · exact False.elim (A.right_arm.other_ne (hother.trans hc.symm))
  · simpa [hc, hother] using D.right_or_path.hxy
  · simpa [hc, hother] using D.right_or_path.hxy.symm
  · exact False.elim (A.right_arm.other_ne (hother.trans hc.symm))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_arm_adj_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    K.Adj c A.left_arm.other := by
  rcases A.c_left with hc | hc <;>
    rcases A.left_arm.other_endpoint with hother | hother
  · exact False.elim (A.left_arm.other_ne (hother.trans hc.symm))
  · simpa [hc, hother] using D.left_or_path.hxy
  · simpa [hc, hother] using D.left_or_path.hxy.symm
  · exact False.elim (A.left_arm.other_ne (hother.trans hc.symm))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_arm_adj_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    K.Adj c A.side_arm.other := by
  rcases A.c_side with hc | hc <;>
    rcases A.side_arm.other_endpoint with hother | hother
  · exact False.elim (A.side_arm.other_ne (hother.trans hc.symm))
  · simpa [hc, hother] using D.left_or_right.hxy
  · simpa [hc, hother] using D.left_or_right.hxy.symm
  · exact False.elim (A.side_arm.other_ne (hother.trans hc.symm))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33_neighbor_eq_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c z : K33Vertex}
    (A : C.CommonBranchArmPaths c)
    (hz : K33Graph.Adj c z) :
    z = A.right_arm.other ∨ z = A.left_arm.other ∨
      z = A.side_arm.other := by
  exact
    K33Graph.neighbor_eq_of_three_distinct_adj
      A.right_arm_adj_common A.left_arm_adj_common A.side_arm_adj_common
      A.right_left_other_ne A.right_side_other_ne A.left_side_other_ne hz

/-- The two additional `K_{3,3}` source vertices on the same side as the
common branch.  These are the future common endpoints of the three rim paths in
the common-branch mixed obstruction. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33_exists_two_rim_sources
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (A : C.CommonBranchArmPaths c) :
    Exists fun leftSource : K33Vertex =>
      Exists fun rightSource : K33Vertex =>
        leftSource ≠ rightSource ∧ leftSource ≠ c ∧ rightSource ≠ c ∧
          K33Graph.Adj leftSource A.right_arm.other ∧
          K33Graph.Adj leftSource A.left_arm.other ∧
          K33Graph.Adj leftSource A.side_arm.other ∧
          K33Graph.Adj rightSource A.right_arm.other ∧
          K33Graph.Adj rightSource A.left_arm.other ∧
          K33Graph.Adj rightSource A.side_arm.other :=
  K33Graph.exists_two_same_side_common_neighbors
    A.right_arm_adj_common A.left_arm_adj_common A.side_arm_adj_common

/-- The six `K_{3,3}` strict-subdivision paths from the two same-side rim
sources to the three opposite common-branch arm sources. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (A : C.CommonBranchArmPaths c) : Type _ where
  leftSource : K33Vertex
  rightSource : K33Vertex
  left_ne_right : leftSource ≠ rightSource
  left_ne_common : leftSource ≠ c
  right_ne_common : rightSource ≠ c
  left_adj_right_arm : K33Graph.Adj leftSource A.right_arm.other
  left_adj_left_arm : K33Graph.Adj leftSource A.left_arm.other
  left_adj_side_arm : K33Graph.Adj leftSource A.side_arm.other
  right_adj_right_arm : K33Graph.Adj rightSource A.right_arm.other
  right_adj_left_arm : K33Graph.Adj rightSource A.left_arm.other
  right_adj_side_arm : K33Graph.Adj rightSource A.side_arm.other
  left_to_right_arm_path :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex leftSource)
      ((Classical.choice hK33).branchVertex A.right_arm.other)
  left_to_right_arm_isPath : left_to_right_arm_path.IsPath
  left_to_right_arm_support_subset :
    forall w : V, w ∈ left_to_right_arm_path.support ->
      w ∈ ((Classical.choice hK33).edgePath left_adj_right_arm).support
  left_to_left_arm_path :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex leftSource)
      ((Classical.choice hK33).branchVertex A.left_arm.other)
  left_to_left_arm_isPath : left_to_left_arm_path.IsPath
  left_to_left_arm_support_subset :
    forall w : V, w ∈ left_to_left_arm_path.support ->
      w ∈ ((Classical.choice hK33).edgePath left_adj_left_arm).support
  left_to_side_arm_path :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex leftSource)
      ((Classical.choice hK33).branchVertex A.side_arm.other)
  left_to_side_arm_isPath : left_to_side_arm_path.IsPath
  left_to_side_arm_support_subset :
    forall w : V, w ∈ left_to_side_arm_path.support ->
      w ∈ ((Classical.choice hK33).edgePath left_adj_side_arm).support
  right_to_right_arm_path :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex rightSource)
      ((Classical.choice hK33).branchVertex A.right_arm.other)
  right_to_right_arm_isPath : right_to_right_arm_path.IsPath
  right_to_right_arm_support_subset :
    forall w : V, w ∈ right_to_right_arm_path.support ->
      w ∈ ((Classical.choice hK33).edgePath right_adj_right_arm).support
  right_to_left_arm_path :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex rightSource)
      ((Classical.choice hK33).branchVertex A.left_arm.other)
  right_to_left_arm_isPath : right_to_left_arm_path.IsPath
  right_to_left_arm_support_subset :
    forall w : V, w ∈ right_to_left_arm_path.support ->
      w ∈ ((Classical.choice hK33).edgePath right_adj_left_arm).support
  right_to_side_arm_path :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex rightSource)
      ((Classical.choice hK33).branchVertex A.side_arm.other)
  right_to_side_arm_isPath : right_to_side_arm_path.IsPath
  right_to_side_arm_support_subset :
    forall w : V, w ∈ right_to_side_arm_path.support ->
      w ∈ ((Classical.choice hK33).edgePath right_adj_side_arm).support

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33_rimSourceEdgePaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (A : C.CommonBranchArmPaths c) :
    A.K33RimSourceEdgePaths := by
  classical
  let H := A.K33_exists_two_rim_sources
  let leftSource : K33Vertex := Classical.choose H
  let Hright := Classical.choose_spec H
  let rightSource : K33Vertex := Classical.choose Hright
  have Hspec := Classical.choose_spec Hright
  have hne : leftSource ≠ rightSource := Hspec.1
  have hleft_common : leftSource ≠ c := Hspec.2.1
  have hright_common : rightSource ≠ c := Hspec.2.2.1
  have hleft_right : K33Graph.Adj leftSource A.right_arm.other :=
    Hspec.2.2.2.1
  have hleft_left : K33Graph.Adj leftSource A.left_arm.other :=
    Hspec.2.2.2.2.1
  have hleft_side : K33Graph.Adj leftSource A.side_arm.other :=
    Hspec.2.2.2.2.2.1
  have hright_right : K33Graph.Adj rightSource A.right_arm.other :=
    Hspec.2.2.2.2.2.2.1
  have hright_left : K33Graph.Adj rightSource A.left_arm.other :=
    Hspec.2.2.2.2.2.2.2.1
  have hright_side : K33Graph.Adj rightSource A.side_arm.other :=
    Hspec.2.2.2.2.2.2.2.2
  exact {
    leftSource := leftSource
    rightSource := rightSource
    left_ne_right := hne
    left_ne_common := hleft_common
    right_ne_common := hright_common
    left_adj_right_arm := hleft_right
    left_adj_left_arm := hleft_left
    left_adj_side_arm := hleft_side
    right_adj_right_arm := hright_right
    right_adj_left_arm := hright_left
    right_adj_side_arm := hright_side
    left_to_right_arm_path :=
      (Classical.choice hK33).edgePath hleft_right
    left_to_right_arm_isPath :=
      (Classical.choice hK33).edgePath_isPath hleft_right
    left_to_right_arm_support_subset := by
      intro w hw
      simpa using hw
    left_to_left_arm_path :=
      (Classical.choice hK33).edgePath hleft_left
    left_to_left_arm_isPath :=
      (Classical.choice hK33).edgePath_isPath hleft_left
    left_to_left_arm_support_subset := by
      intro w hw
      simpa using hw
    left_to_side_arm_path :=
      (Classical.choice hK33).edgePath hleft_side
    left_to_side_arm_isPath :=
      (Classical.choice hK33).edgePath_isPath hleft_side
    left_to_side_arm_support_subset := by
      intro w hw
      simpa using hw
    right_to_right_arm_path :=
      (Classical.choice hK33).edgePath hright_right
    right_to_right_arm_isPath :=
      (Classical.choice hK33).edgePath_isPath hright_right
    right_to_right_arm_support_subset := by
      intro w hw
      simpa using hw
    right_to_left_arm_path :=
      (Classical.choice hK33).edgePath hright_left
    right_to_left_arm_isPath :=
      (Classical.choice hK33).edgePath_isPath hright_left
    right_to_left_arm_support_subset := by
      intro w hw
      simpa using hw
    right_to_side_arm_path :=
      (Classical.choice hK33).edgePath hright_side
    right_to_side_arm_isPath :=
      (Classical.choice hK33).edgePath_isPath hright_side
    right_to_side_arm_support_subset := by
      intro w hw
      simpa using hw
  }


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
