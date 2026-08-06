import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.CleanTailResiduals

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Source split for the side-left common-branch `K_{3,3}` arm case.

The source proof first handles the cases where one of the three selected
endpoint paths meets the cut path.  If none does, the clean-tail residual
constructor above gives an ambient tripod. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.obstruction_sideLeft_of_path_targets_or_residual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (hSide : C.SideLeftTag)
    (hR_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hres :
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
            F.SupportAttachedCleanTailsSideLeftResidual R L U) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  by_cases hR :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
        P.pathSet
  · exact hR_path hR
  by_cases hL :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
        P.pathSet
  · exact hL_path hL
  by_cases hU :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
        P.pathSet
  · exact hU_path hU
  exact Or.inr
    (F.exists_tripod_sideLeft_of_no_path_targets_and_residual
      hSide hR hL hU hres)

/-- Source split for the side-right common-branch `K_{3,3}` arm case. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.obstruction_sideRight_of_path_targets_or_residual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (hSide : C.SideRightTag)
    (hR_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hres :
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
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  by_cases hR :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
        P.pathSet
  · exact hR_path hR
  by_cases hL :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
        P.pathSet
  · exact hL_path hL
  by_cases hU :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
        P.pathSet
  · exact hU_path hU
  exact Or.inr
    (F.exists_tripod_sideRight_of_no_path_targets_and_residual
      hSide hR hL hU hres)

/-- Arm-package version of
`K33RimSourceEdgePaths.obstruction_sideLeft_of_path_targets_or_residual`.

The two rim sources and six rim paths are taken from the strict subdivision
automatically. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33_obstruction_sideLeft_of_path_targets_or_residual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (A : C.CommonBranchArmPaths c)
    (hSide : C.SideLeftTag)
    (hR_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hres :
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
            F.SupportAttachedCleanTailsSideLeftResidual R L U) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  let F := A.K33_rimSourceEdgePaths
  exact
    F.obstruction_sideLeft_of_path_targets_or_residual
      hSide hR_path hL_path hU_path hres

/-- Arm-package version of
`K33RimSourceEdgePaths.obstruction_sideRight_of_path_targets_or_residual`. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33_obstruction_sideRight_of_path_targets_or_residual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (A : C.CommonBranchArmPaths c)
    (hSide : C.SideRightTag)
    (hR_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
          P.pathSet ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hres :
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
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  let F := A.K33_rimSourceEdgePaths
  exact
    F.obstruction_sideRight_of_path_targets_or_residual
      hSide hR_path hL_path hU_path hres

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchChoices_right_left_sideLeft
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (_hR : C.RightEdgeTag)
    (_hL : C.LeftEdgeTag)
    (hS : C.SideLeftTag) :
    C.CommonBranchEndpointPathChoices :=
  C.commonBranchEndpointPathChoices A
    C.rightFstEndpointPath
    C.leftFstEndpointPath
    ((C.sideFstLeftEndpointPath hS).toSideEndpointPath)

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchChoices_right_left_sideRight
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (_hR : C.RightEdgeTag)
    (_hL : C.LeftEdgeTag)
    (hS : C.SideRightTag) :
    C.CommonBranchEndpointPathChoices :=
  C.commonBranchEndpointPathChoices A
    C.rightFstEndpointPath
    C.leftFstEndpointPath
    ((C.sideFstRightEndpointPath hS).toSideEndpointPath)

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchChoices_right_pathLeft_sideLeft
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (_hR : C.RightEdgeTag)
    (hL : C.LeftPathTag)
    (hS : C.SideLeftTag) :
    C.CommonBranchEndpointPathChoices :=
  C.commonBranchEndpointPathChoices A
    C.rightFstEndpointPath
    ((C.leftFstPathEndpointPath hL).toLeftEndpointPath)
    ((C.sideFstLeftEndpointPath hS).toSideEndpointPath)

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchChoices_right_pathLeft_sideRight
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (_hR : C.RightEdgeTag)
    (hL : C.LeftPathTag)
    (hS : C.SideRightTag) :
    C.CommonBranchEndpointPathChoices :=
  C.commonBranchEndpointPathChoices A
    C.rightFstEndpointPath
    ((C.leftFstPathEndpointPath hL).toLeftEndpointPath)
    ((C.sideFstRightEndpointPath hS).toSideEndpointPath)

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchChoices_pathRight_left_sideLeft
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (hR : C.RightPathTag)
    (_hL : C.LeftEdgeTag)
    (hS : C.SideLeftTag) :
    C.CommonBranchEndpointPathChoices :=
  C.commonBranchEndpointPathChoices A
    ((C.rightFstPathEndpointPath hR).toRightEndpointPath)
    C.leftFstEndpointPath
    ((C.sideFstLeftEndpointPath hS).toSideEndpointPath)

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchChoices_pathRight_left_sideRight
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (hR : C.RightPathTag)
    (_hL : C.LeftEdgeTag)
    (hS : C.SideRightTag) :
    C.CommonBranchEndpointPathChoices :=
  C.commonBranchEndpointPathChoices A
    ((C.rightFstPathEndpointPath hR).toRightEndpointPath)
    C.leftFstEndpointPath
    ((C.sideFstRightEndpointPath hS).toSideEndpointPath)

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchChoices_pathRight_pathLeft_sideLeft
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (hR : C.RightPathTag)
    (hL : C.LeftPathTag)
    (hS : C.SideLeftTag) :
    C.CommonBranchEndpointPathChoices :=
  C.commonBranchEndpointPathChoices A
    ((C.rightFstPathEndpointPath hR).toRightEndpointPath)
    ((C.leftFstPathEndpointPath hL).toLeftEndpointPath)
    ((C.sideFstLeftEndpointPath hS).toSideEndpointPath)

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchChoices_pathRight_pathLeft_sideRight
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (hR : C.RightPathTag)
    (hL : C.LeftPathTag)
    (hS : C.SideRightTag) :
    C.CommonBranchEndpointPathChoices :=
  C.commonBranchEndpointPathChoices A
    ((C.rightFstPathEndpointPath hR).toRightEndpointPath)
    ((C.leftFstPathEndpointPath hL).toLeftEndpointPath)
    ((C.sideFstRightEndpointPath hS).toSideEndpointPath)

set_option linter.unusedVariables false in
/-- The eight concrete tag cases for a common-branch mixed Kuratowski arm
package.

The source proof's final mixed branch is not just "three arms from a common
branch vertex"; it also uses whether the selected host edge on each arm lies
in the right side, left side, the cut path, or the opposite side.  This
structure makes that finite split explicit and keeps the common-branch
obligation from hiding the real geometric cases. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) (c : W) : Prop where
  right_left_sideLeft :
    forall A : C.CommonBranchArmPaths c,
      C.RightEdgeTag -> C.LeftEdgeTag -> C.SideLeftTag ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  right_left_sideRight :
    forall A : C.CommonBranchArmPaths c,
      C.RightEdgeTag -> C.LeftEdgeTag -> C.SideRightTag ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  right_pathLeft_sideLeft :
    forall A : C.CommonBranchArmPaths c,
      C.RightEdgeTag -> C.LeftPathTag -> C.SideLeftTag ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  right_pathLeft_sideRight :
    forall A : C.CommonBranchArmPaths c,
      C.RightEdgeTag -> C.LeftPathTag -> C.SideRightTag ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  pathRight_left_sideLeft :
    forall A : C.CommonBranchArmPaths c,
      C.RightPathTag -> C.LeftEdgeTag -> C.SideLeftTag ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  pathRight_left_sideRight :
    forall A : C.CommonBranchArmPaths c,
      C.RightPathTag -> C.LeftEdgeTag -> C.SideRightTag ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  pathRight_pathLeft_sideLeft :
    forall A : C.CommonBranchArmPaths c,
      C.RightPathTag -> C.LeftPathTag -> C.SideLeftTag ->
        Nonempty S.Cross ∨ Nonempty S.Tripod
  pathRight_pathLeft_sideRight :
    forall A : C.CommonBranchArmPaths c,
      C.RightPathTag -> C.LeftPathTag -> C.SideRightTag ->
        Nonempty S.Cross ∨ Nonempty S.Tripod

/-- Build the eight tag cases from handlers that depend only on the selected
side tag.  The right/left edge-versus-path tags are often bookkeeping once
the three arm paths have been constructed; this constructor prevents every
such argument from spelling out the same eight-field product. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.of_side_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (hleft : ∀ _ : C.CommonBranchArmPaths c,
      C.SideLeftTag → Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hright : ∀ _ : C.CommonBranchArmPaths c,
      C.SideRightTag → Nonempty S.Cross ∨ Nonempty S.Tripod) :
    C.CommonBranchArmTagObstructions c where
  right_left_sideLeft := fun A _ _ hS => hleft A hS
  right_left_sideRight := fun A _ _ hS => hright A hS
  right_pathLeft_sideLeft := fun A _ _ hS => hleft A hS
  right_pathLeft_sideRight := fun A _ _ hS => hright A hS
  pathRight_left_sideLeft := fun A _ _ hS => hleft A hS
  pathRight_left_sideRight := fun A _ _ hS => hright A hS
  pathRight_pathLeft_sideLeft := fun A _ _ hS => hleft A hS
  pathRight_pathLeft_sideRight := fun A _ _ hS => hright A hS

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.eliminate
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (O : C.CommonBranchArmTagObstructions c)
    (hA : Nonempty (C.CommonBranchArmPaths c)) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  rcases hA with ⟨A⟩
  rcases C.right_or_path_regions with hR | hRp
  · rcases C.left_or_path_regions with hL | hLp
    · rcases C.left_or_right_regions with hS | hS
      · exact O.right_left_sideLeft A
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEdgeTag] using hR)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEdgeTag] using hL)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideLeftTag] using hS)
      · exact O.right_left_sideRight A
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEdgeTag] using hR)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEdgeTag] using hL)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideRightTag] using hS)
    · rcases C.left_or_right_regions with hS | hS
      · exact O.right_pathLeft_sideLeft A
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEdgeTag] using hR)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftPathTag] using hLp)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideLeftTag] using hS)
      · exact O.right_pathLeft_sideRight A
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEdgeTag] using hR)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftPathTag] using hLp)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideRightTag] using hS)
  · rcases C.left_or_path_regions with hL | hLp
    · rcases C.left_or_right_regions with hS | hS
      · exact O.pathRight_left_sideLeft A
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightPathTag] using hRp)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEdgeTag] using hL)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideLeftTag] using hS)
      · exact O.pathRight_left_sideRight A
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightPathTag] using hRp)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEdgeTag] using hL)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideRightTag] using hS)
    · rcases C.left_or_right_regions with hS | hS
      · exact O.pathRight_pathLeft_sideLeft A
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightPathTag] using hRp)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftPathTag] using hLp)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideLeftTag] using hS)
      · exact O.pathRight_pathLeft_sideRight A
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightPathTag] using hRp)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftPathTag] using hLp)
          (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideRightTag] using hS)

/-- Assemble the eight `K_{3,3}` common-branch tag cases from the source-local
path-target obstructions and the two clean-tail residual packages.

This is the finite tag-case layer used by the source GM IX `(2.4)` route: the
right/left/path tags only select which concrete endpoint paths are under
discussion; the actual work is uniform in the arm package. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.of_K33_path_targets_or_residual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (hR_path :
      forall A : C.CommonBranchArmPaths c,
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      forall A : C.CommonBranchArmPaths c,
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      forall A : C.CommonBranchArmPaths c,
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hSideLeft_res :
      forall A : C.CommonBranchArmPaths c,
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
      forall A : C.CommonBranchArmPaths c,
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
    C.CommonBranchArmTagObstructions c :=
  MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.of_side_obstructions
    (fun A hS =>
      A.K33_obstruction_sideLeft_of_path_targets_or_residual
        hS (hR_path A) (hL_path A) (hU_path A) (hSideLeft_res A))
    (fun A hS =>
      A.K33_obstruction_sideRight_of_path_targets_or_residual
        hS (hR_path A) (hL_path A) (hU_path A) (hSideRight_res A))

/-- Assemble the eight `K_{3,3}` common-branch tag cases from the three
path-target alternatives and the two direct no-path side obstructions.

This is the source-facing version of the common-branch split.  The printed
GM IX `(2.4)` rural-gluing argument does not quantify over arbitrary clean
tails; it first handles the cases where a selected endpoint hits the cut path,
and otherwise constructs the forbidden ambient tripod from the side-left or
side-right no-path configuration. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.of_K33_path_targets_or_no_path_obstructions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (hR_path :
      forall A : C.CommonBranchArmPaths c,
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hL_path :
      forall A : C.CommonBranchArmPaths c,
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hU_path :
      forall A : C.CommonBranchArmPaths c,
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hSideLeft_no_path :
      forall A : C.CommonBranchArmPaths c,
        C.SideLeftTag ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∉
            P.pathSet ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∉
            P.pathSet ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∉
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod)
    (hSideRight_no_path :
      forall A : C.CommonBranchArmPaths c,
        C.SideRightTag ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∉
            P.pathSet ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∉
            P.pathSet ->
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∉
            P.pathSet ->
          Nonempty S.Cross ∨ Nonempty S.Tripod) :
    C.CommonBranchArmTagObstructions c := by
  apply MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmTagObstructions.of_side_obstructions
  · intro A hS
    by_cases hRtarget :
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
          P.pathSet
    · exact hR_path A hRtarget
    by_cases hLtarget :
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
          P.pathSet
    · exact hL_path A hLtarget
    by_cases hUtarget :
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
          P.pathSet
    · exact hU_path A hUtarget
    exact hSideLeft_no_path A hS hRtarget hLtarget hUtarget
  · intro A hS
    by_cases hRtarget :
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
          P.pathSet
    · exact hR_path A hRtarget
    by_cases hLtarget :
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
          P.pathSet
    · exact hL_path A hLtarget
    by_cases hUtarget :
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
          P.pathSet
    · exact hU_path A hUtarget
    exact hSideRight_no_path A hS hRtarget hLtarget hUtarget


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
