import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.ObstructionInterfaces

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Source-geometric obligations for one mixed `K_{3,3}` package.

This is the final local shape of the `K_{3,3}` rural-gluing obstruction used
by the source route.  Pairwise disjoint and duplicate-source alternatives are
kept explicit; the common-branch case is reduced to the three selected
endpoint path hits and the side-left/side-right residual clean-tail packages.

The older version of this interface asked for residual facts for arbitrary
support-attached tails.  That is stronger than the printed GM IX `(2.4)`
argument and is not the right statement: the source proof only needs the
direct no-path side-left and side-right contradictions after the three
path-target alternatives have been eliminated. -/
structure MixedK33SourceGeometricObstructions
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
  right_target_on_path :
    forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
      (A : C.CommonBranchArmPaths c),
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  left_target_on_path :
    forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
      (A : C.CommonBranchArmPaths c),
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  side_target_on_path :
    forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
      (A : C.CommonBranchArmPaths c),
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  sideLeft_no_path :
    forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
      (A : C.CommonBranchArmPaths c),
      C.SideLeftTag ->
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∉
          P.pathSet ->
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∉
          P.pathSet ->
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∉
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  sideRight_no_path :
    forall (C : D.CommonSupportEndpointPaths) (c : K33Vertex)
      (A : C.CommonBranchArmPaths c),
      C.SideRightTag ->
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∉
          P.pathSet ->
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∉
          P.pathSet ->
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∉
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Build the source-geometric `K_{3,3}` package from the stronger
support-attached clean-tail leg-separation facts.

This is the direct bridge from the residual clean-tail machinery to the
source-facing no-path clauses.  Once the three nontrivial endpoint targets are
off the cut path, the existing `K33RimSourceEdgePaths` constructor supplies the
forbidden ambient tripod from the side-left or side-right leg-separation
package. -/
theorem MixedK33SourceGeometricObstructions.of_K33_path_targets_or_legSeparation
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
    GMIX24Split.MixedK33SourceGeometricObstructions D where
  right_left_disjoint := h_right_left_disjoint
  right_side_disjoint := h_right_side_disjoint
  left_side_disjoint := h_left_side_disjoint
  right_left_duplicate := h_right_left_duplicate
  right_side_duplicate := h_right_side_duplicate
  left_side_duplicate := h_left_side_duplicate
  right_target_on_path := hR_path
  left_target_on_path := hL_path
  side_target_on_path := hU_path
  sideLeft_no_path := by
    intro C c A hSide hR_not_path hL_not_path hU_not_path
    let F := A.K33_rimSourceEdgePaths
    exact Or.inr
      (F.exists_tripod_sideLeft_of_no_path_targets_and_residual
        hSide hR_not_path hL_not_path hU_not_path
        (by
          intro R L U hR_avoid hL_avoid hU_avoid
          exact
            MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideLeftResidual.of_legSeparation
              (F := F) (R := R) (L := L) (U := U)
              (hSideLeft_sep C c A R L U hR_avoid hL_avoid hU_avoid)))
  sideRight_no_path := by
    intro C c A hSide hR_not_path hL_not_path hU_not_path
    let F := A.K33_rimSourceEdgePaths
    exact Or.inr
      (F.exists_tripod_sideRight_of_no_path_targets_and_residual
        hSide hR_not_path hL_not_path hU_not_path
        (by
          intro R L U hR_avoid hL_avoid hU_avoid
          exact
            MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideRightResidual.of_legSeparation
              (F := F) (R := R) (L := L) (U := U)
              (hSideRight_sep C c A R L U hR_avoid hL_avoid hU_avoid)))

/-- Source-geometric obligations for one mixed `K_5` package.

The common-branch arm case is reduced to the fourth-source path package, and
the triangle-source cover branch is reduced to its path-equipped extra-edge
package. -/
structure MixedK5SourceGeometricObstructions
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
  common_fourth :
    forall (C : D.CommonSupportEndpointPaths) (c : Fin 5)
      (A : C.CommonBranchArmPaths c),
        A.K5FourthSourceEdgePaths ->
          Nonempty S.Cross ∨ Nonempty S.Tripod
  triangle_cover :
    D.K5TriangleCoverExtraPaths ->
      Nonempty S.Cross ∨ Nonempty S.Tripod

theorem MixedK33SourceGeometricObstructions.to_arm_tag_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    (C : GMIX24Split.MixedK33SourceGeometricObstructions D) :
    GMIX24Split.MixedK33ArmTagCaseObstructions D :=
  MixedK33ArmTagCaseObstructions.of_K33_path_targets_or_no_path_obstructions
    C.right_left_disjoint C.right_side_disjoint C.left_side_disjoint
    C.right_left_duplicate C.right_side_duplicate C.left_side_duplicate
    C.right_target_on_path C.left_target_on_path C.side_target_on_path
    C.sideLeft_no_path C.sideRight_no_path

theorem MixedK5SourceGeometricObstructions.to_arm_tag_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (C : GMIX24Split.MixedK5SourceGeometricObstructions D) :
    GMIX24Split.MixedK5ArmTagCaseObstructions D :=
  MixedK5ArmTagCaseObstructions.of_K5_fourth_source_or_triangle_cover
    C.right_left_disjoint C.right_side_disjoint C.left_side_disjoint
    C.right_left_duplicate C.right_side_duplicate C.left_side_duplicate
    C.common_fourth C.triangle_cover

theorem MixedEdgeTaggedSupportData.K33_obstruction_of_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (C : GMIX24Split.MixedK33CaseObstructions D) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K33_obstruction_of_support_disjoint_or_common_source_endpoint
    C.right_left_disjoint C.right_side_disjoint C.left_side_disjoint
    C.common_source_endpoint

theorem MixedEdgeTaggedSupportData.K5_obstruction_of_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (C : GMIX24Split.MixedK5CaseObstructions D) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K5_obstruction_of_support_disjoint_or_common_source_endpoint_or_three_cover
    C.right_left_disjoint C.right_side_disjoint C.left_side_disjoint
    C.common_source_endpoint C.three_source_cover

theorem MixedK33ArmTagCaseObstructions.to_arm_path_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    (C : GMIX24Split.MixedK33ArmTagCaseObstructions D) :
    GMIX24Split.MixedK33ArmPathCaseObstructions D where
  right_left_disjoint := C.right_left_disjoint
  right_side_disjoint := C.right_side_disjoint
  left_side_disjoint := C.left_side_disjoint
  right_left_duplicate := C.right_left_duplicate
  right_side_duplicate := C.right_side_duplicate
  left_side_duplicate := C.left_side_duplicate
  common_branch_arms := by
    intro H c hA
    exact (C.common_branch_tag_cases H c).eliminate hA

theorem MixedK5ArmTagCaseObstructions.to_arm_path_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (C : GMIX24Split.MixedK5ArmTagCaseObstructions D) :
    GMIX24Split.MixedK5ArmPathCaseObstructions D where
  right_left_disjoint := C.right_left_disjoint
  right_side_disjoint := C.right_side_disjoint
  left_side_disjoint := C.left_side_disjoint
  right_left_duplicate := C.right_left_duplicate
  right_side_duplicate := C.right_side_duplicate
  left_side_duplicate := C.left_side_duplicate
  common_branch_arms := by
    intro H c hA
    exact (C.common_branch_tag_cases H c).eliminate hA
  three_source_cover := C.three_source_cover

theorem MixedK33ArmPathCaseObstructions.to_path_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    (C : GMIX24Split.MixedK33ArmPathCaseObstructions D) :
    GMIX24Split.MixedK33PathCaseObstructions D where
  right_left_disjoint := C.right_left_disjoint
  right_side_disjoint := C.right_side_disjoint
  left_side_disjoint := C.left_side_disjoint
  common_paths := by
    intro H
    rcases D.K33_common_paths_duplicate_or_commonBranchArmPaths H with
      hRL | hrest
    · exact C.right_left_duplicate H hRL
    rcases hrest with hRS | hrest
    · exact C.right_side_duplicate H hRS
    rcases hrest with hLS | harms
    · exact C.left_side_duplicate H hLS
    rcases harms with ⟨c, hdata⟩
    exact C.common_branch_arms H c hdata

theorem MixedK5ArmPathCaseObstructions.to_path_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (C : GMIX24Split.MixedK5ArmPathCaseObstructions D) :
    GMIX24Split.MixedK5PathCaseObstructions D where
  right_left_disjoint := C.right_left_disjoint
  right_side_disjoint := C.right_side_disjoint
  left_side_disjoint := C.left_side_disjoint
  common_paths := by
    intro H
    rcases
        D.K5_common_paths_duplicate_or_commonBranchArmPaths_or_three_cover H
      with hsource | hcover
    · rcases hsource with hRL | hrest
      · exact C.right_left_duplicate H hRL
      rcases hrest with hRS | hrest
      · exact C.right_side_duplicate H hRS
      rcases hrest with hLS | harms
      · exact C.left_side_duplicate H hLS
      rcases harms with ⟨c, hdata⟩
      exact C.common_branch_arms H c hdata
    · exact C.three_source_cover hcover
  three_source_cover := C.three_source_cover

theorem MixedK33RegionCaseObstructions.to_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    (C : GMIX24Split.MixedK33RegionCaseObstructions D) :
    GMIX24Split.MixedK33CaseObstructions D where
  right_left_disjoint := C.right_left_disjoint
  right_side_disjoint := C.right_side_disjoint
  left_side_disjoint := C.left_side_disjoint
  common_source_endpoint := fun hcommon =>
    C.common_regions
      (D.commonSupportWithEndpointRegions_of_common_source_endpoint hcommon)

theorem MixedK5RegionCaseObstructions.to_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (C : GMIX24Split.MixedK5RegionCaseObstructions D) :
    GMIX24Split.MixedK5CaseObstructions D where
  right_left_disjoint := C.right_left_disjoint
  right_side_disjoint := C.right_side_disjoint
  left_side_disjoint := C.left_side_disjoint
  common_source_endpoint := fun hcommon =>
    C.common_regions
      (D.commonSupportWithEndpointRegions_of_common_source_endpoint hcommon)
  three_source_cover := C.three_source_cover

theorem MixedK33PathCaseObstructions.to_region_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    (C : GMIX24Split.MixedK33PathCaseObstructions D) :
    GMIX24Split.MixedK33RegionCaseObstructions D where
  right_left_disjoint := C.right_left_disjoint
  right_side_disjoint := C.right_side_disjoint
  left_side_disjoint := C.left_side_disjoint
  common_regions := fun H =>
    C.common_paths (D.commonSupportEndpointPaths H)

theorem MixedK5PathCaseObstructions.to_region_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (C : GMIX24Split.MixedK5PathCaseObstructions D) :
    GMIX24Split.MixedK5RegionCaseObstructions D where
  right_left_disjoint := C.right_left_disjoint
  right_side_disjoint := C.right_side_disjoint
  left_side_disjoint := C.left_side_disjoint
  common_regions := fun H =>
    C.common_paths (D.commonSupportEndpointPaths H)
  three_source_cover := C.three_source_cover

theorem MixedEdgeTaggedSupportData.K33_obstruction_of_region_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (C : GMIX24Split.MixedK33RegionCaseObstructions D) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K33_obstruction_of_case_obstructions C.to_case_obstructions

theorem MixedEdgeTaggedSupportData.K5_obstruction_of_region_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (C : GMIX24Split.MixedK5RegionCaseObstructions D) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K5_obstruction_of_case_obstructions C.to_case_obstructions

theorem MixedEdgeTaggedSupportData.K33_obstruction_of_path_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (C : GMIX24Split.MixedK33PathCaseObstructions D) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K33_obstruction_of_region_case_obstructions
    C.to_region_case_obstructions

theorem MixedEdgeTaggedSupportData.K5_obstruction_of_path_case_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (C : GMIX24Split.MixedK5PathCaseObstructions D) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K5_obstruction_of_region_case_obstructions
    C.to_region_case_obstructions

theorem MixedEdgeTaggedSupportData.K33_obstruction_of_source_geometric_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (C : GMIX24Split.MixedK33SourceGeometricObstructions D) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K33_obstruction_of_path_case_obstructions
    C.to_arm_tag_case_obstructions.to_arm_path_case_obstructions.to_path_case_obstructions

theorem MixedEdgeTaggedSupportData.K5_obstruction_of_source_geometric_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (C : GMIX24Split.MixedK5SourceGeometricObstructions D) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K5_obstruction_of_path_case_obstructions
    C.to_arm_tag_case_obstructions.to_arm_path_case_obstructions.to_path_case_obstructions

/-- Source-geometric `K_{3,3}` obstructions rule out mixed-edge leakage in a
cross-free, tripod-free ambient society.

This is the named rural-gluing handoff used by the GeneralSociety route: a
positive source obstruction is converted into the negative no-mixed condition
expected by Kuratowski localization. -/
theorem no_mixed_edge_witnesses_of_K33_source_geometric_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hK33 : ContainsStrictSubdivision K33Graph S.graph)
    (hsource :
      forall D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33,
        GMIX24Split.MixedK33SourceGeometricObstructions D) :
    Not
      (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK33 ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK33 ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK33) := by
  intro hmixed
  let H : GMIX24Split.MixedEdgeTaggedSupportWitnesses P hno_cross hK33 := {
    right_or_path :=
      GMIX24Split.modelEdgeInRightOrPath_tagged_support_localization
        P hno_cross hmixed.1
    left_or_path :=
      GMIX24Split.modelEdgeInLeftOrPath_tagged_support_localization
        P hno_cross hmixed.2.1
    left_or_right :=
      GMIX24Split.modelEdgeInLeftOrRight_tagged_support_localization
        P hno_cross hmixed.2.2
  }
  rcases
      GMIX24Split.mixedEdgeTaggedSupportData_of_witnesses
        P hno_cross H
    with ⟨D⟩
  rcases D.K33_obstruction_of_source_geometric_obstructions (hsource D) with
    hcross | htripod
  · exact hno_cross hcross
  · exact hno_tripod htripod

/-- Source-geometric `K_5` obstructions rule out mixed-edge leakage in a
cross-free, tripod-free ambient society. -/
theorem no_mixed_edge_witnesses_of_K5_source_geometric_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hK5 : ContainsStrictSubdivision K5Graph S.graph)
    (hsource :
      forall D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5,
        GMIX24Split.MixedK5SourceGeometricObstructions D) :
    Not
      (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK5 ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK5 ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK5) := by
  intro hmixed
  let H : GMIX24Split.MixedEdgeTaggedSupportWitnesses P hno_cross hK5 := {
    right_or_path :=
      GMIX24Split.modelEdgeInRightOrPath_tagged_support_localization
        P hno_cross hmixed.1
    left_or_path :=
      GMIX24Split.modelEdgeInLeftOrPath_tagged_support_localization
        P hno_cross hmixed.2.1
    left_or_right :=
      GMIX24Split.modelEdgeInLeftOrRight_tagged_support_localization
        P hno_cross hmixed.2.2
  }
  rcases
      GMIX24Split.mixedEdgeTaggedSupportData_of_witnesses
        P hno_cross H
    with ⟨D⟩
  rcases D.K5_obstruction_of_source_geometric_obstructions (hsource D) with
    hcross | htripod
  · exact hno_cross hcross
  · exact hno_tripod htripod

theorem MixedEdgeTaggedSupportData.K33_obstruction_of_common_support_meet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (h_right_left_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_disjoint :
      Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_common_support :
      (Exists fun z : V =>
        z ∈ D.right_or_path.supportSet ∧
          z ∈ D.left_or_path.supportSet ∧
            z ∈ D.left_or_right.supportSet) ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K33_obstruction_of_support_disjoint_or_common_source_endpoint
    h_right_left_disjoint h_right_side_disjoint h_left_side_disjoint
    (fun hcommon => h_common_support
      (D.supports_meet_of_common_source_endpoint hcommon))

theorem MixedEdgeTaggedSupportData.K5_obstruction_of_common_support_meet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (h_right_left_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_disjoint :
      Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_common_support :
      (Exists fun z : V =>
        z ∈ D.right_or_path.supportSet ∧
          z ∈ D.left_or_path.supportSet ∧
            z ∈ D.left_or_right.supportSet) ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_three_cover :
      D.K5ThreeSourceCover ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K5_obstruction_of_support_disjoint_or_common_source_endpoint_or_three_cover
    h_right_left_disjoint h_right_side_disjoint h_left_side_disjoint
    (fun hcommon => h_common_support
      (D.supports_meet_of_common_source_endpoint hcommon))
    h_three_cover

theorem MixedEdgeTaggedSupportData.K33_obstruction_of_common_support_endpoint_regions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (h_right_left_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_disjoint :
      Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_common_regions :
      D.CommonSupportWithEndpointRegions ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K33_obstruction_of_support_disjoint_or_common_source_endpoint
    h_right_left_disjoint h_right_side_disjoint h_left_side_disjoint
    (fun hcommon => h_common_regions
      (D.commonSupportWithEndpointRegions_of_common_source_endpoint hcommon))

theorem MixedEdgeTaggedSupportData.K5_obstruction_of_common_support_endpoint_regions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (h_right_left_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_right_side_disjoint :
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_left_side_disjoint :
      Disjoint D.left_or_path.supportSet D.left_or_right.supportSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_common_regions :
      D.CommonSupportWithEndpointRegions ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_three_cover :
      D.K5ThreeSourceCover ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod :=
  D.K5_obstruction_of_support_disjoint_or_common_source_endpoint_or_three_cover
    h_right_left_disjoint h_right_side_disjoint h_left_side_disjoint
    (fun hcommon => h_common_regions
      (D.commonSupportWithEndpointRegions_of_common_source_endpoint hcommon))
    h_three_cover


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
