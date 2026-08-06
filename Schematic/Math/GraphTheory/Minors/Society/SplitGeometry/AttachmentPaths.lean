import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.EndpointTags

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Bundled clean-tail/path alternatives for the canonical nontrivial endpoint
choices in a common-branch package. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchNontrivialEndpointPathChoices_cleanTailAlternatives
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    ((C.commonBranchNontrivialEndpointPathChoices A).choices.right.CleanTailToRightBoundaryArc ∨
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈ P.pathSet) ∧
      ((C.commonBranchNontrivialEndpointPathChoices A).choices.left.CleanTailToLeftBoundaryArc ∨
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈ P.pathSet) ∧
        (((C.commonBranchNontrivialEndpointPathChoices A).choices.side.CleanTailToLeftBoundaryArc ∨
            (C.commonBranchNontrivialEndpointPathChoices A).choices.side.CleanTailToRightBoundaryArc) ∨
          (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈ P.pathSet) := by
  exact ⟨
    C.commonBranchNontrivialEndpointPathChoices_right_cleanTail_or_pathSet A,
    C.commonBranchNontrivialEndpointPathChoices_left_cleanTail_or_pathSet A,
    C.commonBranchNontrivialEndpointPathChoices_side_cleanTail_or_pathSet A⟩

/-- In a common-branch arm package, any selected right endpoint can be reached
from the right rim-attachment branch vertex by a path segment contained in the
same strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_right_attach_to_endpoint_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.right_arm.other)
        E.right.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.right_or_path.supportSet :=
  E.right.exists_support_path_from_source_endpoint A.right_arm.other_endpoint

/-- In a common-branch arm package, any vertex on a selected right endpoint
path can be reached from the right rim-attachment branch vertex within the
same strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_right_attach_to_endpoint_path_vertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    {x : V}
    (hx : x ∈ E.right.path.support) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.right_arm.other) x =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.right_or_path.supportSet :=
  E.right.exists_support_path_from_source_endpoint_to_path_vertex
    A.right_arm.other_endpoint hx

/-- In a common-branch arm package, any selected left endpoint can be reached
from the left rim-attachment branch vertex by a path segment contained in the
same strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_left_attach_to_endpoint_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.left_arm.other)
        E.left.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_path.supportSet :=
  E.left.exists_support_path_from_source_endpoint A.left_arm.other_endpoint

/-- In a common-branch arm package, any vertex on a selected left endpoint path
can be reached from the left rim-attachment branch vertex within the same
strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_left_attach_to_endpoint_path_vertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    {x : V}
    (hx : x ∈ E.left.path.support) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.left_arm.other) x =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_path.supportSet :=
  E.left.exists_support_path_from_source_endpoint_to_path_vertex
    A.left_arm.other_endpoint hx

/-- In a common-branch arm package, any selected side endpoint can be reached
from the side rim-attachment branch vertex by a path segment contained in the
same strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_side_attach_to_endpoint_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.side_arm.other)
        E.side.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_right.supportSet :=
  E.side.exists_support_path_from_source_endpoint A.side_arm.other_endpoint

/-- In a common-branch arm package, any vertex on a selected side endpoint path
can be reached from the side rim-attachment branch vertex within the same
strict-subdivision source-edge support. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_side_attach_to_endpoint_path_vertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    {x : V}
    (hx : x ∈ E.side.path.support) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.side_arm.other) x =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_right.supportSet :=
  E.side.exists_support_path_from_source_endpoint_to_path_vertex
    A.side_arm.other_endpoint hx

/-- Attachment-to-endpoint support segment for the canonical nontrivial right
choice. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_right_attach_to_nontrivial_endpoint_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.right_arm.other)
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.right_or_path.supportSet :=
  A.exists_right_attach_to_endpoint_path
    (C.commonBranchNontrivialEndpointPathChoices A).choices

/-- Attachment-to-endpoint support segment for the canonical nontrivial left
choice. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_left_attach_to_nontrivial_endpoint_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.left_arm.other)
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_path.supportSet :=
  A.exists_left_attach_to_endpoint_path
    (C.commonBranchNontrivialEndpointPathChoices A).choices

/-- Attachment-to-endpoint support segment for the canonical nontrivial side
choice. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_side_attach_to_nontrivial_endpoint_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.side_arm.other)
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target =>
      q.IsPath ∧
        forall w : V, w ∈ q.support -> w ∈ D.left_or_right.supportSet :=
  A.exists_side_attach_to_endpoint_path
    (C.commonBranchNontrivialEndpointPathChoices A).choices

/-- Attachment-to-endpoint support segment for the canonical nontrivial right
choice, avoiding the common branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_right_attach_to_nontrivial_endpoint_path_avoiding_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.right_arm.other)
        (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target =>
      q.IsPath ∧
        (forall w : V, w ∈ q.support -> w ∈ D.right_or_path.supportSet) ∧
          (Classical.choice hK).branchVertex c ∉ q.support := by
  classical
  let E := C.commonBranchNontrivialEndpointPathChoices A
  exact
    D.right_or_path.exists_support_path_from_other_endpoint_avoiding_common
      A.c_right A.right_arm.other_endpoint
      (by
        intro h
        exact A.right_arm.other_ne h.symm)
      E.choices.right.target_mem_supportSet
      (by
        intro h
        exact E.right_target_ne_z
          (h.trans A.z_eq_branchVertex.symm))

/-- Attachment-to-endpoint support segment for the canonical nontrivial left
choice, avoiding the common branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_left_attach_to_nontrivial_endpoint_path_avoiding_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.left_arm.other)
        (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target =>
      q.IsPath ∧
        (forall w : V, w ∈ q.support -> w ∈ D.left_or_path.supportSet) ∧
          (Classical.choice hK).branchVertex c ∉ q.support := by
  classical
  let E := C.commonBranchNontrivialEndpointPathChoices A
  exact
    D.left_or_path.exists_support_path_from_other_endpoint_avoiding_common
      A.c_left A.left_arm.other_endpoint
      (by
        intro h
        exact A.left_arm.other_ne h.symm)
      E.choices.left.target_mem_supportSet
      (by
        intro h
        exact E.left_target_ne_z
          (h.trans A.z_eq_branchVertex.symm))

/-- Attachment-to-endpoint support segment for the canonical nontrivial side
choice, avoiding the common branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.exists_side_attach_to_nontrivial_endpoint_path_avoiding_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex A.side_arm.other)
        (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target =>
      q.IsPath ∧
        (forall w : V, w ∈ q.support -> w ∈ D.left_or_right.supportSet) ∧
          (Classical.choice hK).branchVertex c ∉ q.support := by
  classical
  let E := C.commonBranchNontrivialEndpointPathChoices A
  exact
    D.left_or_right.exists_support_path_from_other_endpoint_avoiding_common
      A.c_side A.side_arm.other_endpoint
      (by
        intro h
        exact A.side_arm.other_ne h.symm)
      E.choices.side.target_mem_supportSet
      (by
        intro h
        exact E.side_target_ne_z
          (h.trans A.z_eq_branchVertex.symm))

/-- A right common-branch endpoint whose target lies on the right side gives a
support-attached clean tail from the corresponding `K_{3,3}` rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_right_supportAttachedCleanTailToRightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (E : C.CommonBranchEndpointPathChoices)
    (htarget : E.right.target ∈ P.rightSide) :
    Nonempty
      (P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0)) := by
  classical
  rcases A.exists_right_attach_to_endpoint_path E with ⟨q, hq_path, hq_support⟩
  simpa
    [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using
      P.exists_supportAttachedCleanTailToRightBoundaryArc
        hno_cross q hq_path hq_support htarget

/-- A left common-branch endpoint whose target lies on the left side gives a
support-attached clean tail from the corresponding `K_{3,3}` rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_left_supportAttachedCleanTailToLeftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (E : C.CommonBranchEndpointPathChoices)
    (htarget : E.left.target ∈ P.leftSide) :
    Nonempty
      (P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1)) := by
  classical
  rcases A.exists_left_attach_to_endpoint_path E with ⟨q, hq_path, hq_support⟩
  simpa
    [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using
      P.exists_supportAttachedCleanTailToLeftBoundaryArc
        hno_cross q hq_path hq_support htarget

/-- A side common-branch endpoint whose target lies on the left side gives a
support-attached clean tail from the side rim attachment to the left boundary
arc. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_side_supportAttachedCleanTailToLeftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (E : C.CommonBranchEndpointPathChoices)
    (htarget : E.side.target ∈ P.leftSide) :
    Nonempty
      (P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)) := by
  classical
  rcases A.exists_side_attach_to_endpoint_path E with ⟨q, hq_path, hq_support⟩
  simpa
    [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using
      P.exists_supportAttachedCleanTailToLeftBoundaryArc
        hno_cross q hq_path hq_support htarget

/-- A side common-branch endpoint whose target lies on the right side gives a
support-attached clean tail from the side rim attachment to the right boundary
arc. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_side_supportAttachedCleanTailToRightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (E : C.CommonBranchEndpointPathChoices)
    (htarget : E.side.target ∈ P.rightSide) :
    Nonempty
      (P.SupportAttachedCleanTailToRightBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)) := by
  classical
  rcases A.exists_side_attach_to_endpoint_path E with ⟨q, hq_path, hq_support⟩
  simpa
    [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using
      P.exists_supportAttachedCleanTailToRightBoundaryArc
        hno_cross q hq_path hq_support htarget

/-- The canonical nontrivial right endpoint gives a support-attached right
tail whose attachment segment avoids the common branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_right_supportAttachedCleanTailToRightBoundaryArc_nontrivial_attach_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (htarget :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∈
        P.rightSide) :
    Exists fun R :
        P.SupportAttachedCleanTailToRightBoundaryArc
          D.right_or_path.supportSet (F.rimAttach 0) =>
      (Classical.choice hK33).branchVertex c ∉ R.attach.support := by
  classical
  rcases A.exists_right_attach_to_nontrivial_endpoint_path_avoiding_common with
    ⟨q, hq_path, hq_support, hq_avoid⟩
  simpa
    [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using
      P.exists_supportAttachedCleanTailToRightBoundaryArc_attach_avoids
        hno_cross q hq_path hq_support htarget hq_avoid

/-- The canonical nontrivial left endpoint gives a support-attached left tail
whose attachment segment avoids the common branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_left_supportAttachedCleanTailToLeftBoundaryArc_nontrivial_attach_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (htarget :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∈
        P.leftSide) :
    Exists fun L :
        P.SupportAttachedCleanTailToLeftBoundaryArc
          D.left_or_path.supportSet (F.rimAttach 1) =>
      (Classical.choice hK33).branchVertex c ∉ L.attach.support := by
  classical
  rcases A.exists_left_attach_to_nontrivial_endpoint_path_avoiding_common with
    ⟨q, hq_path, hq_support, hq_avoid⟩
  simpa
    [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using
      P.exists_supportAttachedCleanTailToLeftBoundaryArc_attach_avoids
        hno_cross q hq_path hq_support htarget hq_avoid

/-- The canonical nontrivial side endpoint gives a support-attached side tail
to the left boundary arc whose attachment segment avoids the common branch
vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_side_supportAttachedCleanTailToLeftBoundaryArc_nontrivial_attach_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (htarget :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
        P.leftSide) :
    Exists fun U :
        P.SupportAttachedCleanTailToLeftBoundaryArc
          D.left_or_right.supportSet (F.rimAttach 2) =>
      (Classical.choice hK33).branchVertex c ∉ U.attach.support := by
  classical
  rcases A.exists_side_attach_to_nontrivial_endpoint_path_avoiding_common with
    ⟨q, hq_path, hq_support, hq_avoid⟩
  simpa
    [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using
      P.exists_supportAttachedCleanTailToLeftBoundaryArc_attach_avoids
        hno_cross q hq_path hq_support htarget hq_avoid

/-- The canonical nontrivial side endpoint gives a support-attached side tail
to the right boundary arc whose attachment segment avoids the common branch
vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_side_supportAttachedCleanTailToRightBoundaryArc_nontrivial_attach_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (htarget :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∈
        P.rightSide) :
    Exists fun U :
        P.SupportAttachedCleanTailToRightBoundaryArc
          D.left_or_right.supportSet (F.rimAttach 2) =>
      (Classical.choice hK33).branchVertex c ∉ U.attach.support := by
  classical
  rcases A.exists_side_attach_to_nontrivial_endpoint_path_avoiding_common with
    ⟨q, hq_path, hq_support, hq_avoid⟩
  simpa
    [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using
      P.exists_supportAttachedCleanTailToRightBoundaryArc_attach_avoids
        hno_cross q hq_path hq_support htarget hq_avoid

/-- In the side-left tag case, if the canonical nontrivial right, left, and
side targets are all away from the cut path, then all three support-attached
clean tails exist and each attachment segment avoids the common branch
vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_supportAttachedCleanTailsSideLeft_nontrivial_attach_avoids_common_of_no_path_targets
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (hSide : C.SideLeftTag)
    (hR_not_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∉
        P.pathSet)
    (hL_not_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∉
        P.pathSet)
    (hU_not_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∉
        P.pathSet) :
    Exists fun R :
        P.SupportAttachedCleanTailToRightBoundaryArc
          D.right_or_path.supportSet (F.rimAttach 0) =>
      Exists fun L :
        P.SupportAttachedCleanTailToLeftBoundaryArc
          D.left_or_path.supportSet (F.rimAttach 1) =>
      Exists fun U :
        P.SupportAttachedCleanTailToLeftBoundaryArc
          D.left_or_right.supportSet (F.rimAttach 2) =>
        (Classical.choice hK33).branchVertex c ∉ R.attach.support ∧
          (Classical.choice hK33).branchVertex c ∉ L.attach.support ∧
            (Classical.choice hK33).branchVertex c ∉ U.attach.support := by
  classical
  let E := C.commonBranchNontrivialEndpointPathChoices A
  have hR_right : E.choices.right.target ∈ P.rightSide := by
    rcases E.choices.right.target_mem with hright | hpath
    · exact hright
    · exact False.elim (hR_not_path (by simpa [E] using hpath))
  have hL_left : E.choices.left.target ∈ P.leftSide := by
    rcases E.choices.left.target_mem with hleft | hpath
    · exact hleft
    · exact False.elim (hL_not_path (by simpa [E] using hpath))
  have hU_left : E.choices.side.target ∈ P.leftSide := by
    have hmem :
        E.choices.side.target ∈ P.leftSide ∪ P.pathSet := by
      simpa [E] using
        C.commonBranchNontrivialEndpointPathChoices_side_target_mem_left_or_path
          A hSide
    rcases hmem with hleft | hpath
    · exact hleft
    · exact False.elim (hU_not_path (by simpa [E] using hpath))
  rcases F.exists_right_supportAttachedCleanTailToRightBoundaryArc_nontrivial_attach_avoids_common
      hR_right with ⟨R, hR_avoid⟩
  rcases F.exists_left_supportAttachedCleanTailToLeftBoundaryArc_nontrivial_attach_avoids_common
      hL_left with ⟨L, hL_avoid⟩
  rcases F.exists_side_supportAttachedCleanTailToLeftBoundaryArc_nontrivial_attach_avoids_common
      hU_left with ⟨U, hU_avoid⟩
  exact ⟨R, L, U, hR_avoid, hL_avoid, hU_avoid⟩

/-- Side-right analogue of
`exists_supportAttachedCleanTailsSideLeft_nontrivial_attach_avoids_common_of_no_path_targets`. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_supportAttachedCleanTailsSideRight_nontrivial_attach_avoids_common_of_no_path_targets
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (hSide : C.SideRightTag)
    (hR_not_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.right.target ∉
        P.pathSet)
    (hL_not_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.left.target ∉
        P.pathSet)
    (hU_not_path :
      (C.commonBranchNontrivialEndpointPathChoices A).choices.side.target ∉
        P.pathSet) :
    Exists fun R :
        P.SupportAttachedCleanTailToRightBoundaryArc
          D.right_or_path.supportSet (F.rimAttach 0) =>
      Exists fun L :
        P.SupportAttachedCleanTailToLeftBoundaryArc
          D.left_or_path.supportSet (F.rimAttach 1) =>
      Exists fun U :
        P.SupportAttachedCleanTailToRightBoundaryArc
          D.left_or_right.supportSet (F.rimAttach 2) =>
        (Classical.choice hK33).branchVertex c ∉ R.attach.support ∧
          (Classical.choice hK33).branchVertex c ∉ L.attach.support ∧
            (Classical.choice hK33).branchVertex c ∉ U.attach.support := by
  classical
  let E := C.commonBranchNontrivialEndpointPathChoices A
  have hR_right : E.choices.right.target ∈ P.rightSide := by
    rcases E.choices.right.target_mem with hright | hpath
    · exact hright
    · exact False.elim (hR_not_path (by simpa [E] using hpath))
  have hL_left : E.choices.left.target ∈ P.leftSide := by
    rcases E.choices.left.target_mem with hleft | hpath
    · exact hleft
    · exact False.elim (hL_not_path (by simpa [E] using hpath))
  have hU_right : E.choices.side.target ∈ P.rightSide := by
    have hmem :
        E.choices.side.target ∈ P.rightSide ∪ P.pathSet := by
      simpa [E] using
        C.commonBranchNontrivialEndpointPathChoices_side_target_mem_right_or_path
          A hSide
    rcases hmem with hright | hpath
    · exact hright
    · exact False.elim (hU_not_path (by simpa [E] using hpath))
  rcases F.exists_right_supportAttachedCleanTailToRightBoundaryArc_nontrivial_attach_avoids_common
      hR_right with ⟨R, hR_avoid⟩
  rcases F.exists_left_supportAttachedCleanTailToLeftBoundaryArc_nontrivial_attach_avoids_common
      hL_left with ⟨L, hL_avoid⟩
  rcases F.exists_side_supportAttachedCleanTailToRightBoundaryArc_nontrivial_attach_avoids_common
      hU_right with ⟨U, hU_avoid⟩
  exact ⟨R, L, U, hR_avoid, hL_avoid, hU_avoid⟩


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
