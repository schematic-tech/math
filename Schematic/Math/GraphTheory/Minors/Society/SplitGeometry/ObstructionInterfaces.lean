import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.CommonSource

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- The geometric branch obligations for one unpacked `K_{3,3}` mixed
Kuratowski package after source-combinatorial normalization. -/
structure MixedK33CaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  common_source_endpoint :
    D.CommonSourceEndpoint ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

/-- The geometric branch obligations for one unpacked `K_5` mixed
Kuratowski package after source-combinatorial normalization. -/
structure MixedK5CaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  common_source_endpoint :
    D.CommonSourceEndpoint ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  three_source_cover :
    D.K5ThreeSourceCover ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Region-localized geometric branch obligations for one unpacked
`K_{3,3}` mixed Kuratowski package.

This is stronger than `MixedK33CaseObstructions` only in the common-end branch:
the caller receives the common host support vertex together with the three
side/path endpoint tags, instead of the raw common source endpoint. -/
structure MixedK33RegionCaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  common_regions :
    D.CommonSupportWithEndpointRegions ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Region-localized geometric branch obligations for one unpacked `K_5`
mixed Kuratowski package.  The `K_5` triangle-source branch remains separate;
the common-source branch is passed to the caller as localized host support
data. -/
structure MixedK5RegionCaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  common_regions :
    D.CommonSupportWithEndpointRegions ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  three_source_cover :
    D.K5ThreeSourceCover ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Path-localized geometric branch obligations for one unpacked
`K_{3,3}` mixed Kuratowski package.

Compared with `MixedK33RegionCaseObstructions`, the common-end branch receives
the actual subpaths from the common support vertex to both endpoints of each
tagged host edge. -/
structure MixedK33PathCaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  common_paths :
    D.CommonSupportEndpointPaths ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Path-localized geometric branch obligations for one unpacked `K_5` mixed
Kuratowski package. -/
structure MixedK5PathCaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  common_paths :
    D.CommonSupportEndpointPaths ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  three_source_cover :
    D.K5ThreeSourceCover ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Source-normalized path-case obligations for a mixed `K_{3,3}` package.

This is sharper than `MixedK33PathCaseObstructions` in the common-support
branch.  The source combinatorics have already been discharged: the caller
only has to handle duplicated selected source edges, or the concrete
common-branch arm package from the shared branch vertex to the three opposite
source endpoints. -/
structure MixedK33ArmPathCaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_left_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.rightLeftSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.rightSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.leftSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  common_branch_arms :
    forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex),
      Nonempty (C.CommonBranchArmPaths c) ->
        Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Source-normalized path-case obligations for a mixed `K_5` package.  In
addition to the duplicated-source and common-branch-arm cases, the formal
triangle-source cover from the `K_5` source graph remains as a separate
branch. -/
structure MixedK5ArmPathCaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_left_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.rightLeftSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.rightSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.leftSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  common_branch_arms :
    forall (C : D.CommonSupportEndpointPaths) (c : Fin 5),
      Nonempty (C.CommonBranchArmPaths c) ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  three_source_cover :
    D.K5ThreeSourceCover ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Tag-normalized path-case obligations for a mixed `K_{3,3}` package.

This refines `MixedK33ArmPathCaseObstructions`: in the common-branch-arm
case, the caller handles the eight concrete side/path tag configurations
instead of receiving the unsplit arm package. -/
structure MixedK33ArmTagCaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_left_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.rightLeftSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.rightSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.leftSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  common_branch_tag_cases :
    forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex),
      C.CommonBranchArmTagObstructions c

/-- Tag-normalized path-case obligations for a mixed `K_5` package. -/
structure MixedK5ArmTagCaseObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5) : Prop where
  right_left_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_disjoint :
    Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_disjoint :
    Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
      Nonempty S.Cross ∨ Nonempty S.Tripod
  right_left_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.rightLeftSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  right_side_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.rightSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  left_side_duplicate :
    forall _C : D.CommonSupportEndpointPaths,
      D.leftSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod
  common_branch_tag_cases :
    forall (C : D.CommonSupportEndpointPaths) (c : Fin 5),
      C.CommonBranchArmTagObstructions c
  three_source_cover :
    D.K5ThreeSourceCover ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Assemble a full `K_{3,3}` arm/tag obstruction package from the source
path-target alternatives and the residual clean-tail constructors.

The pairwise disjoint-support and duplicated-source alternatives are still
geometric inputs at this level.  The common-branch branch is no longer a
black-box obligation: it is delegated to
`CommonBranchArmTagObstructions.of_K33_path_targets_or_residual`, which is the
formal version of the source proof's side-tripod construction. -/
theorem MixedK33ArmTagCaseObstructions.of_K33_path_targets_or_residual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    (h_right_left_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_disjoint :
      Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_left_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.rightLeftSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.rightSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.leftSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hR_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hSideLeft_res :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        let F := A.K33_rimSourceEdgePaths
        forall
          (R :
            P.SupportAttachedCleanTailToRightBoundaryArc
              D.right_or_path.supportSet (F.rimAttach 0))
          (L :
            P.SupportAttachedCleanTailToLeftBoundaryArc
              D.left_or_path.supportSet (F.rimAttach 1))
          (U :
            P.SupportAttachedCleanTailToLeftBoundaryArc
              D.left_or_right.supportSet (F.rimAttach 2)),
            (Classical.choice hK33).branchVertex c ∉ R.attach.support ->
            (Classical.choice hK33).branchVertex c ∉ L.attach.support ->
            (Classical.choice hK33).branchVertex c ∉ U.attach.support ->
              F.SupportAttachedCleanTailsSideLeftResidual R L U)
    (hSideRight_res :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        let F := A.K33_rimSourceEdgePaths
        forall
          (R :
            P.SupportAttachedCleanTailToRightBoundaryArc
              D.right_or_path.supportSet (F.rimAttach 0))
          (L :
            P.SupportAttachedCleanTailToLeftBoundaryArc
              D.left_or_path.supportSet (F.rimAttach 1))
          (U :
            P.SupportAttachedCleanTailToRightBoundaryArc
              D.left_or_right.supportSet (F.rimAttach 2)),
            (Classical.choice hK33).branchVertex c ∉ R.attach.support ->
            (Classical.choice hK33).branchVertex c ∉ L.attach.support ->
            (Classical.choice hK33).branchVertex c ∉ U.attach.support ->
              F.SupportAttachedCleanTailsSideRightResidual R L U) :
    GMIX24Split.MixedK33ArmTagCaseObstructions D where
  right_left_disjoint := h_right_left_disjoint
  right_side_disjoint := h_right_side_disjoint
  left_side_disjoint := h_left_side_disjoint
  right_left_duplicate := h_right_left_duplicate
  right_side_duplicate := h_right_side_duplicate
  left_side_duplicate := h_left_side_duplicate
  common_branch_tag_cases := by
    intro C c
    exact
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.of_K33_path_targets_or_residual
        (hR_path C c) (hL_path C c) (hU_path C c)
        (hSideLeft_res C c) (hSideRight_res C c)

/-- Assemble a full `K_{3,3}` arm/tag obstruction package from the
source-local path-target alternatives and direct no-path side obstructions.

This is the public source-facing variant used by
`MixedK33SourceGeometricObstructions`.  The residual clean-tail machinery
above remains available as an internal way to prove a no-path obstruction, but
the outer GM IX `(2.4)` obligation is the geometric contradiction itself. -/
theorem MixedK33ArmTagCaseObstructions.of_K33_path_targets_or_no_path_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    (h_right_left_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_disjoint :
      Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_left_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.rightLeftSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.rightSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.leftSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hR_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hSideLeft_no_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        C.SideLeftTag ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∉
            P.pathSet ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∉
            P.pathSet ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∉
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hSideRight_no_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        C.SideRightTag ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∉
            P.pathSet ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∉
            P.pathSet ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∉
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod) :
    GMIX24Split.MixedK33ArmTagCaseObstructions D where
  right_left_disjoint := h_right_left_disjoint
  right_side_disjoint := h_right_side_disjoint
  left_side_disjoint := h_left_side_disjoint
  right_left_duplicate := h_right_left_duplicate
  right_side_duplicate := h_right_side_duplicate
  left_side_duplicate := h_left_side_duplicate
  common_branch_tag_cases := by
    intro C c
    exact
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.of_K33_path_targets_or_no_path_obstructions
        (hR_path C c) (hL_path C c) (hU_path C c)
        (hSideLeft_no_path C c) (hSideRight_no_path C c)

/-- Variant of
`MixedK33ArmTagCaseObstructions.of_K33_path_targets_or_residual` whose
side-left and side-right inputs are the natural full leg-separation packages.

This is the preferred source-proof interface: the componentwise residual data
are recovered automatically from the stronger support-attached separation
statements. -/
theorem MixedK33ArmTagCaseObstructions.of_K33_path_targets_or_legSeparation
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    (h_right_left_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_disjoint :
      Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_left_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.rightLeftSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.rightSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.leftSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hR_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hSideLeft_sep :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        let F := A.K33_rimSourceEdgePaths
        forall
          (R :
            P.SupportAttachedCleanTailToRightBoundaryArc
              D.right_or_path.supportSet (F.rimAttach 0))
          (L :
            P.SupportAttachedCleanTailToLeftBoundaryArc
              D.left_or_path.supportSet (F.rimAttach 1))
          (U :
            P.SupportAttachedCleanTailToLeftBoundaryArc
              D.left_or_right.supportSet (F.rimAttach 2)),
            (Classical.choice hK33).branchVertex c ∉ R.attach.support ->
            (Classical.choice hK33).branchVertex c ∉ L.attach.support ->
            (Classical.choice hK33).branchVertex c ∉ U.attach.support ->
              F.SupportAttachedCleanTailLegSeparationSideLeft R L U)
    (hSideRight_sep :
      forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
        (A : C.CommonBranchArmPaths c),
        let F := A.K33_rimSourceEdgePaths
        forall
          (R :
            P.SupportAttachedCleanTailToRightBoundaryArc
              D.right_or_path.supportSet (F.rimAttach 0))
          (L :
            P.SupportAttachedCleanTailToLeftBoundaryArc
              D.left_or_path.supportSet (F.rimAttach 1))
          (U :
            P.SupportAttachedCleanTailToRightBoundaryArc
              D.left_or_right.supportSet (F.rimAttach 2)),
            (Classical.choice hK33).branchVertex c ∉ R.attach.support ->
            (Classical.choice hK33).branchVertex c ∉ L.attach.support ->
            (Classical.choice hK33).branchVertex c ∉ U.attach.support ->
              F.SupportAttachedCleanTailLegSeparationSideRight R L U) :
    GMIX24Split.MixedK33ArmTagCaseObstructions D :=
  MixedK33ArmTagCaseObstructions.of_K33_path_targets_or_residual
    h_right_left_disjoint h_right_side_disjoint h_left_side_disjoint
    h_right_left_duplicate h_right_side_duplicate h_left_side_duplicate
    hR_path hL_path hU_path
    (by
      intro C c A
      dsimp only
      intro R L U hR hL hU
      exact
        MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideLeftResidual.of_legSeparation
          (F := A.K33_rimSourceEdgePaths) (R := R) (L := L) (U := U)
          (hSideLeft_sep C c A R L U hR hL hU))
    (by
      intro C c A
      dsimp only
      intro R L U hR hL hU
      exact
        MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideRightResidual.of_legSeparation
          (F := A.K33_rimSourceEdgePaths) (R := R) (L := L) (U := U)
          (hSideRight_sep C c A R L U hR hL hU))

/-- Assemble a full `K_5` arm/tag obstruction package from the source-local
fourth-source and triangle-cover geometric constructors.

The `K_5` common-branch branch has a different source geometry from the
`K_{3,3}` branch: the three arms and their common endpoint leave a fourth
source vertex.  `K5FourthSourceEdgePaths` is the path-equipped form of that
fourth-source data.  The triangle-cover branch is similarly converted to the
path-equipped `K5TriangleCoverExtraPaths` package before being handed to the
caller. -/
theorem MixedK5ArmTagCaseObstructions.of_K5_fourth_source_or_triangle_cover
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (h_right_left_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_disjoint :
      Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_left_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.rightLeftSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.rightSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_duplicate :
      forall _C : D.CommonSupportEndpointPaths,
        D.leftSideSame -> Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_common_fourth :
      forall (C : D.CommonSupportEndpointPaths) (c : Fin 5)
        (A : C.CommonBranchArmPaths c),
          A.K5FourthSourceEdgePaths ->
            Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_triangle_cover :
      D.K5TriangleCoverExtraPaths ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    GMIX24Split.MixedK5ArmTagCaseObstructions D where
  right_left_disjoint := h_right_left_disjoint
  right_side_disjoint := h_right_side_disjoint
  left_side_disjoint := h_left_side_disjoint
  right_left_duplicate := h_right_left_duplicate
  right_side_duplicate := h_right_side_duplicate
  left_side_duplicate := h_left_side_duplicate
  common_branch_tag_cases := by
    intro C c
    apply
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.of_side_obstructions
    · intro A _
      exact h_common_fourth C c A A.K5_fourthSourceEdgePaths
    · intro A _
      exact h_common_fourth C c A A.K5_fourthSourceEdgePaths
  three_source_cover := by
    intro hcover
    exact h_triangle_cover
      (MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.of_cover hcover)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
