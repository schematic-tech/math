import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.SubdivisionIntersections

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- The rim path through the right/common-branch arm in the `K_{3,3}` mixed
common-branch obstruction. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_arm_rim_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex F.leftSource)
      ((Classical.choice hK33).branchVertex F.rightSource) :=
  F.left_to_right_arm_path.append F.right_to_right_arm_path.reverse

/-- The rim path through the left/common-branch arm in the `K_{3,3}` mixed
common-branch obstruction. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_arm_rim_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex F.leftSource)
      ((Classical.choice hK33).branchVertex F.rightSource) :=
  F.left_to_left_arm_path.append F.right_to_left_arm_path.reverse

/-- The rim path through the side/common-branch arm in the `K_{3,3}` mixed
common-branch obstruction. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_arm_rim_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex F.leftSource)
      ((Classical.choice hK33).branchVertex F.rightSource) :=
  F.left_to_side_arm_path.append F.right_to_side_arm_path.reverse

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_arm_rim_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    F.right_arm_rim_path.IsPath := by
  classical
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    F.left_to_right_arm_isPath F.right_to_right_arm_isPath.reverse ?_
  intro z hzLeft hzRightRev
  have hzRight : z ∈ F.right_to_right_arm_path.support := by
    rw [SimpleGraph.Walk.support_reverse] at hzRightRev
    exact List.mem_reverse.mp hzRightRev
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_arm_rim_path]
    using F.left_right_arm_inter_right_right_arm_eq_right_arm hzLeft hzRight

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_arm_rim_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    F.left_arm_rim_path.IsPath := by
  classical
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    F.left_to_left_arm_isPath F.right_to_left_arm_isPath.reverse ?_
  intro z hzLeft hzRightRev
  have hzRight : z ∈ F.right_to_left_arm_path.support := by
    rw [SimpleGraph.Walk.support_reverse] at hzRightRev
    exact List.mem_reverse.mp hzRightRev
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_arm_rim_path]
    using F.left_left_arm_inter_right_left_arm_eq_left_arm hzLeft hzRight

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_arm_rim_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    F.side_arm_rim_path.IsPath := by
  classical
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    F.left_to_side_arm_isPath F.right_to_side_arm_isPath.reverse ?_
  intro z hzLeft hzRightRev
  have hzRight : z ∈ F.right_to_side_arm_path.support := by
    rw [SimpleGraph.Walk.support_reverse] at hzRightRev
    exact List.mem_reverse.mp hzRightRev
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_arm_rim_path]
    using F.left_side_arm_inter_right_side_arm_eq_side_arm hzLeft hzRight

/-- The common branch vertex of two incident subdivision-edge paths is an
internal vertex of their end-to-end concatenation. -/
theorem branchVertex_mem_walk_append_reverse_internal
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G) {left right center : W}
    (first : G.Walk (M.branchVertex left) (M.branchVertex center))
    (second : G.Walk (M.branchVertex right) (M.branchVertex center))
    (hleft : K.Adj left center) (hright : K.Adj right center) :
    M.branchVertex center ∈
      Walk.InternalVertices (first.append second.reverse) := by
  refine ⟨?_, ?_, ?_⟩
  · exact SimpleGraph.Walk.subset_support_append_left
      first second.reverse first.end_mem_support
  · intro h
    exact hleft.ne ((M.branchVertex_injective h).symm)
  · intro h
    exact hright.ne ((M.branchVertex_injective h).symm)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_arm_branch_mem_rim_internal
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    (Classical.choice hK33).branchVertex A.right_arm.other ∈
      Walk.InternalVertices F.right_arm_rim_path := by
  exact branchVertex_mem_walk_append_reverse_internal
    (Classical.choice hK33) F.left_to_right_arm_path
      F.right_to_right_arm_path F.left_adj_right_arm F.right_adj_right_arm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_arm_branch_mem_rim_internal
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    (Classical.choice hK33).branchVertex A.left_arm.other ∈
      Walk.InternalVertices F.left_arm_rim_path := by
  exact branchVertex_mem_walk_append_reverse_internal
    (Classical.choice hK33) F.left_to_left_arm_path
      F.right_to_left_arm_path F.left_adj_left_arm F.right_adj_left_arm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_arm_branch_mem_rim_internal
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    (Classical.choice hK33).branchVertex A.side_arm.other ∈
      Walk.InternalVertices F.side_arm_rim_path := by
  exact branchVertex_mem_walk_append_reverse_internal
    (Classical.choice hK33) F.left_to_side_arm_path
      F.right_to_side_arm_path F.left_adj_side_arm F.right_adj_side_arm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_arm_rim_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hz : z ∈ F.right_arm_rim_path.support) :
    z ∈ F.left_to_right_arm_path.support ∨
      z ∈ F.right_to_right_arm_path.support := by
  classical
  change z ∈
      (F.left_to_right_arm_path.append
        F.right_to_right_arm_path.reverse).support at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzLeft | hzRightRev
  · exact Or.inl hzLeft
  · right
    rw [SimpleGraph.Walk.support_reverse] at hzRightRev
    exact List.mem_reverse.mp hzRightRev

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_arm_rim_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hz : z ∈ F.left_arm_rim_path.support) :
    z ∈ F.left_to_left_arm_path.support ∨
      z ∈ F.right_to_left_arm_path.support := by
  classical
  change z ∈
      (F.left_to_left_arm_path.append
        F.right_to_left_arm_path.reverse).support at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzLeft | hzRightRev
  · exact Or.inl hzLeft
  · right
    rw [SimpleGraph.Walk.support_reverse] at hzRightRev
    exact List.mem_reverse.mp hzRightRev

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_arm_rim_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hz : z ∈ F.side_arm_rim_path.support) :
    z ∈ F.left_to_side_arm_path.support ∨
      z ∈ F.right_to_side_arm_path.support := by
  classical
  change z ∈
      (F.left_to_side_arm_path.append
        F.right_to_side_arm_path.reverse).support at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzLeft | hzRightRev
  · exact Or.inl hzLeft
  · right
    rw [SimpleGraph.Walk.support_reverse] at hzRightRev
    exact List.mem_reverse.mp hzRightRev

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_left_rims_internal_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.right_arm_rim_path)
      (Walk.InternalVertices F.left_arm_rim_path) := by
  rw [Set.disjoint_left]
  intro z hzRightRim hzLeftRim
  rcases F.right_arm_rim_support_cases hzRightRim.1 with
    hzRightLeft | hzRightRight
  · rcases F.left_arm_rim_support_cases hzLeftRim.1 with
      hzLeftLeft | hzLeftRight
    · exact hzRightRim.2.1
        (F.left_right_arm_inter_left_left_arm_eq_leftSource
          hzRightLeft hzLeftLeft)
    · exact Set.disjoint_left.mp
        F.left_right_arm_support_disjoint_right_left_arm
        hzRightLeft hzLeftRight
  · rcases F.left_arm_rim_support_cases hzLeftRim.1 with
      hzLeftLeft | hzLeftRight
    · exact Set.disjoint_left.mp
        F.left_left_arm_support_disjoint_right_right_arm.symm
        hzRightRight hzLeftLeft
    · exact hzRightRim.2.2
        (F.right_right_arm_inter_right_left_arm_eq_rightSource
          hzRightRight hzLeftRight)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_side_rims_internal_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.right_arm_rim_path)
      (Walk.InternalVertices F.side_arm_rim_path) := by
  rw [Set.disjoint_left]
  intro z hzRightRim hzSideRim
  rcases F.right_arm_rim_support_cases hzRightRim.1 with
    hzRightLeft | hzRightRight
  · rcases F.side_arm_rim_support_cases hzSideRim.1 with
      hzSideLeft | hzSideRight
    · exact hzRightRim.2.1
        (F.left_right_arm_inter_left_side_arm_eq_leftSource
          hzRightLeft hzSideLeft)
    · exact Set.disjoint_left.mp
        F.left_right_arm_support_disjoint_right_side_arm
        hzRightLeft hzSideRight
  · rcases F.side_arm_rim_support_cases hzSideRim.1 with
      hzSideLeft | hzSideRight
    · exact Set.disjoint_left.mp
        F.left_side_arm_support_disjoint_right_right_arm.symm
        hzRightRight hzSideLeft
    · exact hzRightRim.2.2
        (F.right_right_arm_inter_right_side_arm_eq_rightSource
          hzRightRight hzSideRight)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_side_rims_internal_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_arm_rim_path)
      (Walk.InternalVertices F.side_arm_rim_path) := by
  rw [Set.disjoint_left]
  intro z hzLeftRim hzSideRim
  rcases F.left_arm_rim_support_cases hzLeftRim.1 with
    hzLeftLeft | hzLeftRight
  · rcases F.side_arm_rim_support_cases hzSideRim.1 with
      hzSideLeft | hzSideRight
    · exact hzLeftRim.2.1
        (F.left_left_arm_inter_left_side_arm_eq_leftSource
          hzLeftLeft hzSideLeft)
    · exact Set.disjoint_left.mp
        F.left_left_arm_support_disjoint_right_side_arm
        hzLeftLeft hzSideRight
  · rcases F.side_arm_rim_support_cases hzSideRim.1 with
      hzSideLeft | hzSideRight
    · exact Set.disjoint_left.mp
        F.left_side_arm_support_disjoint_right_left_arm.symm
        hzLeftRight hzSideLeft
    · exact hzLeftRim.2.2
        (F.right_left_arm_inter_right_side_arm_eq_rightSource
          hzLeftRight hzSideRight)

/-- The three same-side `K_{3,3}` rims as a `Fin 3`-indexed family. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) (i : Fin 3) :
    S.graph.Walk
      ((Classical.choice hK33).branchVertex F.leftSource)
      ((Classical.choice hK33).branchVertex F.rightSource) :=
  if i = 0 then F.right_arm_rim_path
  else if i = 1 then F.left_arm_rim_path
  else F.side_arm_rim_path

/-- The three opposite-branch attachment vertices for the `K_{3,3}` rim
family. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (_F : A.K33RimSourceEdgePaths) (i : Fin 3) : V :=
  if i = 0 then (Classical.choice hK33).branchVertex A.right_arm.other
  else if i = 1 then (Classical.choice hK33).branchVertex A.left_arm.other
  else (Classical.choice hK33).branchVertex A.side_arm.other

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) (i : Fin 3) :
    (F.rim i).IsPath := by
  fin_cases i <;>
    simp [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim,
      F.right_arm_rim_isPath, F.left_arm_rim_isPath, F.side_arm_rim_isPath]

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach_mem_rim
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) (i : Fin 3) :
    F.rimAttach i ∈ Walk.InternalVertices (F.rim i) := by
  fin_cases i <;>
    simp [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach,
      F.right_arm_branch_mem_rim_internal,
      F.left_arm_branch_mem_rim_internal,
      F.side_arm_branch_mem_rim_internal]

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rims_internal_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (Walk.InternalVertices (F.rim i))
      (Walk.InternalVertices (F.rim j)) := by
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using F.right_left_rims_internal_disjoint
  · simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using F.right_side_rims_internal_disjoint
  · simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using F.right_left_rims_internal_disjoint.symm
  · simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using F.left_side_rims_internal_disjoint
  · simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using F.right_side_rims_internal_disjoint.symm
  · simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using F.left_side_rims_internal_disjoint.symm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.leftSource_branchVertex_ne_rightSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    (Classical.choice hK33).branchVertex F.leftSource ≠
      (Classical.choice hK33).branchVertex F.rightSource := by
  intro h
  exact F.left_ne_right ((Classical.choice hK33).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach_injective
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Function.Injective F.rimAttach := by
  classical
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach] at hij ⊢
  · exact False.elim
      (A.right_left_other_ne
        ((Classical.choice hK33).branchVertex_injective hij))
  · exact False.elim
      (A.right_side_other_ne
        ((Classical.choice hK33).branchVertex_injective hij))
  · exact False.elim
      (A.right_left_other_ne
        ((Classical.choice hK33).branchVertex_injective hij.symm))
  · exact False.elim
      (A.left_side_other_ne
        ((Classical.choice hK33).branchVertex_injective hij))
  · exact False.elim
      (A.right_side_other_ne
        ((Classical.choice hK33).branchVertex_injective hij.symm))
  · exact False.elim
      (A.left_side_other_ne
        ((Classical.choice hK33).branchVertex_injective hij.symm))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach_ne_leftSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) (i : Fin 3) :
    F.rimAttach i ≠
      (Classical.choice hK33).branchVertex F.leftSource := by
  intro h
  exact (F.rimAttach_mem_rim i).2.1 h

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach_ne_rightSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) (i : Fin 3) :
    F.rimAttach i ≠
      (Classical.choice hK33).branchVertex F.rightSource := by
  intro h
  exact (F.rimAttach_mem_rim i).2.2 h

/-- Turn the completed `K_{3,3}` same-side rim skeleton into an actual
general-society tripod once the three boundary legs have been constructed.

This is the direct bridge needed by the mixed Kuratowski obstruction proof:
the rim paths, their internal attachments, endpoint distinctness, and
pairwise rim-disjointness are all supplied by the strict-subdivision source
geometry; only the side/path-to-boundary legs remain as tag-case data. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.toTripodWithLegs
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (boundary : Fin 3 -> V)
    (hboundary_mem : forall i : Fin 3, boundary i ∈ S.boundarySet)
    (hboundary_injective : Function.Injective boundary)
    (leg : forall i : Fin 3, S.graph.Walk (F.rimAttach i) (boundary i))
    (hleg_isPath : forall i : Fin 3, (leg i).IsPath)
    (hlegs_pairwise_disjoint :
      forall i j : Fin 3, i ≠ j ->
        Disjoint {v : V | v ∈ (leg i).support}
          {v : V | v ∈ (leg j).support})
    (hlegs_meet_rims_only_at_attach :
      forall i j : Fin 3, forall v : V,
        v ∈ (leg i).support ->
          v ∈ (F.rim j).support ->
            v = F.rimAttach i) :
    S.Tripod where
  left := (Classical.choice hK33).branchVertex F.leftSource
  right := (Classical.choice hK33).branchVertex F.rightSource
  left_ne_right := F.leftSource_branchVertex_ne_rightSource
  rim := F.rim
  rim_isPath := F.rim_isPath
  attach := F.rimAttach
  attach_mem_rim := F.rimAttach_mem_rim
  boundary := boundary
  boundary_mem := hboundary_mem
  boundary_injective := hboundary_injective
  leg := leg
  leg_isPath := hleg_isPath
  rim_internals_disjoint := F.rims_internal_disjoint
  legs_pairwise_disjoint := hlegs_pairwise_disjoint
  legs_meet_rims_only_at_attach := hlegs_meet_rims_only_at_attach


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
