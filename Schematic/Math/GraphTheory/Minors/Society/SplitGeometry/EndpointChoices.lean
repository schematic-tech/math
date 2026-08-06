import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.AttachedCleanTails

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- A right-or-path endpoint path whose target is not the common start
vertex. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.NontrivialRightEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  endpoint : C.RightEndpointPath
  target_ne_z : endpoint.target ≠ C.z

/-- A left-or-path endpoint path whose target is not the common start vertex. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.NontrivialLeftEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  endpoint : C.LeftEndpointPath
  target_ne_z : endpoint.target ≠ C.z

/-- A left-or-right endpoint path whose target is not the common start
vertex. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.NontrivialSideEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  endpoint : C.SideEndpointPath
  target_ne_z : endpoint.target ≠ C.z

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialRightEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.NontrivialRightEndpointPath := by
  classical
  by_cases hfst : D.right_or_path.e.out.1 = C.z
  · refine ⟨C.rightSndEndpointPath, ?_⟩
    intro hsnd
    exact D.right_or_path.out_fst_ne_out_snd (hfst.trans hsnd.symm)
  · exact ⟨C.rightFstEndpointPath, hfst⟩

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialLeftEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.NontrivialLeftEndpointPath := by
  classical
  by_cases hfst : D.left_or_path.e.out.1 = C.z
  · refine ⟨C.leftSndEndpointPath, ?_⟩
    intro hsnd
    exact D.left_or_path.out_fst_ne_out_snd (hfst.trans hsnd.symm)
  · exact ⟨C.leftFstEndpointPath, hfst⟩

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.nontrivialSideEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.NontrivialSideEndpointPath := by
  classical
  by_cases hfst : D.left_or_right.e.out.1 = C.z
  · refine ⟨C.sideSndEndpointPath, ?_⟩
    intro hsnd
    exact D.left_or_right.out_fst_ne_out_snd (hfst.trans hsnd.symm)
  · exact ⟨C.sideFstEndpointPath, hfst⟩

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.NontrivialRightEndpointPath.path_not_nil
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.NontrivialRightEndpointPath) :
    Not R.endpoint.path.Nil :=
  SimpleGraph.Walk.not_nil_of_ne R.target_ne_z.symm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.NontrivialLeftEndpointPath.path_not_nil
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.NontrivialLeftEndpointPath) :
    Not L.endpoint.path.Nil :=
  SimpleGraph.Walk.not_nil_of_ne L.target_ne_z.symm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.NontrivialSideEndpointPath.path_not_nil
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.NontrivialSideEndpointPath) :
    Not E.endpoint.path.Nil :=
  SimpleGraph.Walk.not_nil_of_ne E.target_ne_z.symm

/-- Three independently chosen localized endpoint paths for a common-branch
mixed Kuratowski package.  This is the reusable version of
`CommonBranchEndpointPaths`: later tag cases may choose either concrete host
edge endpoint on each of the three source-edge supports. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  right : C.RightEndpointPath
  left : C.LeftEndpointPath
  side : C.SideEndpointPath
  right_left_internal_disjoint :
    Disjoint (Walk.InternalVertices right.path) (Walk.InternalVertices left.path)
  right_side_internal_disjoint :
    Disjoint (Walk.InternalVertices right.path) (Walk.InternalVertices side.path)
  left_side_internal_disjoint :
    Disjoint (Walk.InternalVertices left.path) (Walk.InternalVertices side.path)

/-- Endpoint choices whose three targets are all genuinely away from the
common branch vertex. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchNontrivialEndpointPathChoices
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) : Type _ where
  choices : C.CommonBranchEndpointPathChoices
  right_target_ne_z : choices.right.target ≠ C.z
  left_target_ne_z : choices.left.target ≠ C.z
  side_target_ne_z : choices.side.target ≠ C.z

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchNontrivialEndpointPathChoices.right_path_not_nil
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.CommonBranchNontrivialEndpointPathChoices) :
    Not E.choices.right.path.Nil :=
  SimpleGraph.Walk.not_nil_of_ne E.right_target_ne_z.symm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchNontrivialEndpointPathChoices.left_path_not_nil
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.CommonBranchNontrivialEndpointPathChoices) :
    Not E.choices.left.path.Nil :=
  SimpleGraph.Walk.not_nil_of_ne E.left_target_ne_z.symm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchNontrivialEndpointPathChoices.side_path_not_nil
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.CommonBranchNontrivialEndpointPathChoices) :
    Not E.choices.side.path.Nil :=
  SimpleGraph.Walk.not_nil_of_ne E.side_target_ne_z.symm

def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.toEndpointPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.CommonBranchEndpointPathChoices) :
    C.CommonBranchEndpointPaths where
  right_target := E.right.target
  right_path := E.right.path
  right_isPath := E.right.isPath
  right_support_subset := E.right.support_subset
  right_target_mem := E.right.target_mem
  left_target := E.left.target
  left_path := E.left.path
  left_isPath := E.left.isPath
  left_support_subset := E.left.support_subset
  left_target_mem := E.left.target_mem
  side_target := E.side.target
  side_path := E.side.path
  side_isPath := E.side.isPath
  side_support_subset := E.side.support_subset
  side_target_mem := E.side.target_mem
  right_left_internal_disjoint := E.right_left_internal_disjoint
  right_side_internal_disjoint := E.right_side_internal_disjoint
  left_side_internal_disjoint := E.left_side_internal_disjoint

/-- Build the three selected endpoint paths for any choice of first/second
endpoints.  The only intersection proof is the common-branch uniqueness of
the underlying strict-subdivision source-edge supports. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchEndpointPathChoices
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (R : C.RightEndpointPath)
    (L : C.LeftEndpointPath)
    (E : C.SideEndpointPath) :
    C.CommonBranchEndpointPathChoices := by
  classical
  refine {
    right := R
    left := L
    side := E
    right_left_internal_disjoint := ?_
    right_side_internal_disjoint := ?_
    left_side_internal_disjoint := ?_
  }
  · rw [Set.disjoint_left]
    intro w hwRight hwLeft
    have hcommon :
        w = (Classical.choice hK).branchVertex c :=
      A.right_left_support_paths_inter_eq_common
        R.support_subset L.support_subset hwRight.1 hwLeft.1
    exact hwRight.2.1 (by simpa [A.z_eq_branchVertex] using hcommon)
  · rw [Set.disjoint_left]
    intro w hwRight hwSide
    have hcommon :
        w = (Classical.choice hK).branchVertex c :=
      A.right_side_support_paths_inter_eq_common
        R.support_subset E.support_subset hwRight.1 hwSide.1
    exact hwRight.2.1 (by simpa [A.z_eq_branchVertex] using hcommon)
  · rw [Set.disjoint_left]
    intro w hwLeft hwSide
    have hcommon :
        w = (Classical.choice hK).branchVertex c :=
      A.left_side_support_paths_inter_eq_common
        L.support_subset E.support_subset hwLeft.1 hwSide.1
    exact hwLeft.2.1 (by simpa [A.z_eq_branchVertex] using hcommon)

/-- Choose nontrivial concrete endpoints on all three localized host edges in
a common-branch arm package. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    C.CommonBranchNontrivialEndpointPathChoices := by
  classical
  let R := C.nontrivialRightEndpointPath
  let L := C.nontrivialLeftEndpointPath
  let E := C.nontrivialSideEndpointPath
  exact {
    choices := C.commonBranchEndpointPathChoices A R.endpoint L.endpoint E.endpoint
    right_target_ne_z := R.target_ne_z
    left_target_ne_z := L.target_ne_z
    side_target_ne_z := E.target_ne_z
  }

/-- If two selected endpoint paths in a common-branch package end at the same
host vertex, that endpoint is the common branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.right_left_target_eq_z_of_eq
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    (hEq : E.right.target = E.left.target) :
    E.right.target = C.z := by
  have hcommon :
      E.right.target = (Classical.choice hK).branchVertex c :=
    A.right_left_support_paths_inter_eq_common
      E.right.support_subset E.left.support_subset
      E.right.path.end_mem_support
      (by simp [hEq])
  exact hcommon.trans A.z_eq_branchVertex.symm

/-- If the right and side selected endpoint paths end at the same host vertex,
that endpoint is the common branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.right_side_target_eq_z_of_eq
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    (hEq : E.right.target = E.side.target) :
    E.right.target = C.z := by
  have hcommon :
      E.right.target = (Classical.choice hK).branchVertex c :=
    A.right_side_support_paths_inter_eq_common
      E.right.support_subset E.side.support_subset
      E.right.path.end_mem_support
      (by simp [hEq])
  exact hcommon.trans A.z_eq_branchVertex.symm

/-- If the left and side selected endpoint paths end at the same host vertex,
that endpoint is the common branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.left_side_target_eq_z_of_eq
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    (hEq : E.left.target = E.side.target) :
    E.left.target = C.z := by
  have hcommon :
      E.left.target = (Classical.choice hK).branchVertex c :=
    A.left_side_support_paths_inter_eq_common
      E.left.support_subset E.side.support_subset
      E.left.path.end_mem_support
      (by simp [hEq])
  exact hcommon.trans A.z_eq_branchVertex.symm

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
