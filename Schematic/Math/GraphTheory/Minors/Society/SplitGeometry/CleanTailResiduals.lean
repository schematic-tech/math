import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.AttachmentPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Right and left support-attachment segments in a common-branch `K_{3,3}`
package are disjoint once the right attachment avoids the common branch. -/
private theorem supportSets_disjoint_of_inter_eq_avoided
    {first second : Set V} {common : V}
    (hinter :
      forall v : V, v ∈ first -> v ∈ second -> v = common)
    (havoid : common ∉ first) :
    Disjoint first second := by
  rw [Set.disjoint_left]
  intro v hvFirst hvSecond
  exact havoid (by simpa [hinter v hvFirst hvSecond] using hvFirst)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_left_attach_support_disjoint_of_right_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    (R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0))
    (L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1))
    (hR_avoid :
      (Classical.choice hK33).branchVertex c ∉ R.attach.support) :
    Disjoint {v : V | v ∈ R.attach.support}
      {v : V | v ∈ L.attach.support} := by
  exact
    supportSets_disjoint_of_inter_eq_avoided
      (fun v hvR hvL =>
        A.right_left_support_paths_inter_eq_common
          R.attach_support_subset L.attach_support_subset hvR hvL)
      hR_avoid

/-- Right and side-left support-attachment segments in a common-branch
`K_{3,3}` package are disjoint once the right attachment avoids the common
branch. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_sideLeft_attach_support_disjoint_of_right_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    (R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0))
    (U :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2))
    (hR_avoid :
      (Classical.choice hK33).branchVertex c ∉ R.attach.support) :
    Disjoint {v : V | v ∈ R.attach.support}
      {v : V | v ∈ U.attach.support} := by
  exact
    supportSets_disjoint_of_inter_eq_avoided
      (fun v hvR hvU =>
        A.right_side_support_paths_inter_eq_common
          R.attach_support_subset U.attach_support_subset hvR hvU)
      hR_avoid

/-- Left and side-left support-attachment segments in a common-branch
`K_{3,3}` package are disjoint once the left attachment avoids the common
branch. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_sideLeft_attach_support_disjoint_of_left_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    (L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1))
    (U :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2))
    (hL_avoid :
      (Classical.choice hK33).branchVertex c ∉ L.attach.support) :
    Disjoint {v : V | v ∈ L.attach.support}
      {v : V | v ∈ U.attach.support} := by
  exact
    supportSets_disjoint_of_inter_eq_avoided
      (fun v hvL hvU =>
        A.left_side_support_paths_inter_eq_common
          L.attach_support_subset U.attach_support_subset hvL hvU)
      hL_avoid

/-- Right and side-right support-attachment segments in a common-branch
`K_{3,3}` package are disjoint once the right attachment avoids the common
branch. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_sideRight_attach_support_disjoint_of_right_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    (R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0))
    (U :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2))
    (hR_avoid :
      (Classical.choice hK33).branchVertex c ∉ R.attach.support) :
    Disjoint {v : V | v ∈ R.attach.support}
      {v : V | v ∈ U.attach.support} := by
  exact
    supportSets_disjoint_of_inter_eq_avoided
      (fun v hvR hvU =>
        A.right_side_support_paths_inter_eq_common
          R.attach_support_subset U.attach_support_subset hvR hvU)
      hR_avoid

/-- Left and side-right support-attachment segments in a common-branch
`K_{3,3}` package are disjoint once the left attachment avoids the common
branch. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_sideRight_attach_support_disjoint_of_left_avoids_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    (L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1))
    (U :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2))
    (hL_avoid :
      (Classical.choice hK33).branchVertex c ∉ L.attach.support) :
    Disjoint {v : V | v ∈ L.attach.support}
      {v : V | v ∈ U.attach.support} := by
  exact
    supportSets_disjoint_of_inter_eq_avoided
      (fun v hvL hvU =>
        A.left_side_support_paths_inter_eq_common
          L.attach_support_subset U.attach_support_subset hvL hvU)
      hL_avoid

/-- The remaining side-left residual data after the three nontrivial
common-branch arms have been converted into support-attached clean tails.

The support-attachment disjointness forced by the strict-subdivision common
branch is not included here; it is derived by the eliminator below.  What
remains is exactly the local source work: attachment-tail separation, the
same-side tail separation, and tail-rim normalization.  The same-side
boundary ends are distinct automatically from the same-side tail separation. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideLeftResidual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0))
    (L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1))
    (U :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)) : Prop where
  right_attach_left_tail :
    Disjoint {v : V | v ∈ R.attach.support}
      {v : V | v ∈ L.tail.support}
  right_tail_left_attach :
    Disjoint {v : V | v ∈ R.tail.support}
      {v : V | v ∈ L.attach.support}
  right_attach_side_tail :
    Disjoint {v : V | v ∈ R.attach.support}
      {v : V | v ∈ U.tail.support}
  right_tail_side_attach :
    Disjoint {v : V | v ∈ R.tail.support}
      {v : V | v ∈ U.attach.support}
  left_attach_side_tail :
    Disjoint {v : V | v ∈ L.attach.support}
      {v : V | v ∈ U.tail.support}
  left_tail_side_attach :
    Disjoint {v : V | v ∈ L.tail.support}
      {v : V | v ∈ U.attach.support}
  left_tail_side_tail :
    Disjoint {v : V | v ∈ L.tail.support}
      {v : V | v ∈ U.tail.support}
  right_tail_rim :
    forall j : Fin 3, forall v : V,
      v ∈ R.tail.support -> v ∈ (F.rim j).support ->
        v = F.rimAttach 0
  left_tail_rim :
    forall j : Fin 3, forall v : V,
      v ∈ L.tail.support -> v ∈ (F.rim j).support ->
        v = F.rimAttach 1
  side_tail_rim :
    forall j : Fin 3, forall v : V,
      v ∈ U.tail.support -> v ∈ (F.rim j).support ->
        v = F.rimAttach 2

/-- Side-right analogue of
`SupportAttachedCleanTailsSideLeftResidual`. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideRightResidual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0))
    (L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1))
    (U :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)) : Prop where
  right_attach_left_tail :
    Disjoint {v : V | v ∈ R.attach.support}
      {v : V | v ∈ L.tail.support}
  right_tail_left_attach :
    Disjoint {v : V | v ∈ R.tail.support}
      {v : V | v ∈ L.attach.support}
  right_attach_side_tail :
    Disjoint {v : V | v ∈ R.attach.support}
      {v : V | v ∈ U.tail.support}
  right_tail_side_attach :
    Disjoint {v : V | v ∈ R.tail.support}
      {v : V | v ∈ U.attach.support}
  left_attach_side_tail :
    Disjoint {v : V | v ∈ L.attach.support}
      {v : V | v ∈ U.tail.support}
  left_tail_side_attach :
    Disjoint {v : V | v ∈ L.tail.support}
      {v : V | v ∈ U.attach.support}
  right_tail_side_tail :
    Disjoint {v : V | v ∈ R.tail.support}
      {v : V | v ∈ U.tail.support}
  right_tail_rim :
    forall j : Fin 3, forall v : V,
      v ∈ R.tail.support -> v ∈ (F.rim j).support ->
        v = F.rimAttach 0
  left_tail_rim :
    forall j : Fin 3, forall v : V,
      v ∈ L.tail.support -> v ∈ (F.rim j).support ->
        v = F.rimAttach 1
  side_tail_rim :
    forall j : Fin 3, forall v : V,
      v ∈ U.tail.support -> v ∈ (F.rim j).support ->
        v = F.rimAttach 2

/-- Build the side-left clean-tail residual package from its component
separation and tail-rim facts. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideLeftResidual.of_parts
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    {R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0)}
    {L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1)}
    {U :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)}
    (h_right_attach_left_tail :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ L.tail.support})
    (h_right_tail_left_attach :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ L.attach.support})
    (h_right_attach_side_tail :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ U.tail.support})
    (h_right_tail_side_attach :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ U.attach.support})
    (h_left_attach_side_tail :
      Disjoint {v : V | v ∈ L.attach.support}
        {v : V | v ∈ U.tail.support})
    (h_left_tail_side_attach :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ U.attach.support})
    (h_left_tail_side_tail :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ U.tail.support})
    (h_right_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ R.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 0)
    (h_left_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ L.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 1)
    (h_side_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ U.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 2) :
    F.SupportAttachedCleanTailsSideLeftResidual R L U where
  right_attach_left_tail := h_right_attach_left_tail
  right_tail_left_attach := h_right_tail_left_attach
  right_attach_side_tail := h_right_attach_side_tail
  right_tail_side_attach := h_right_tail_side_attach
  left_attach_side_tail := h_left_attach_side_tail
  left_tail_side_attach := h_left_tail_side_attach
  left_tail_side_tail := h_left_tail_side_tail
  right_tail_rim := h_right_tail_rim
  left_tail_rim := h_left_tail_rim
  side_tail_rim := h_side_tail_rim

/-- Build the side-right clean-tail residual package from its component
separation and tail-rim facts. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideRightResidual.of_parts
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    {R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0)}
    {L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1)}
    {U :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)}
    (h_right_attach_left_tail :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ L.tail.support})
    (h_right_tail_left_attach :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ L.attach.support})
    (h_right_attach_side_tail :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ U.tail.support})
    (h_right_tail_side_attach :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ U.attach.support})
    (h_left_attach_side_tail :
      Disjoint {v : V | v ∈ L.attach.support}
        {v : V | v ∈ U.tail.support})
    (h_left_tail_side_attach :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ U.attach.support})
    (h_right_tail_side_tail :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ U.tail.support})
    (h_right_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ R.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 0)
    (h_left_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ L.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 1)
    (h_side_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ U.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 2) :
    F.SupportAttachedCleanTailsSideRightResidual R L U where
  right_attach_left_tail := h_right_attach_left_tail
  right_tail_left_attach := h_right_tail_left_attach
  right_attach_side_tail := h_right_attach_side_tail
  right_tail_side_attach := h_right_tail_side_attach
  left_attach_side_tail := h_left_attach_side_tail
  left_tail_side_attach := h_left_tail_side_attach
  right_tail_side_tail := h_right_tail_side_tail
  right_tail_rim := h_right_tail_rim
  left_tail_rim := h_left_tail_rim
  side_tail_rim := h_side_tail_rim

/-- A full side-left support-attached leg-separation package implies the
componentwise residual package used by the later source split. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideLeftResidual.of_legSeparation
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    {R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0)}
    {L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1)}
    {U :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)}
    (H : F.SupportAttachedCleanTailLegSeparationSideLeft R L U) :
    F.SupportAttachedCleanTailsSideLeftResidual R L U where
  right_attach_left_tail := by
    rw [Set.disjoint_left]
    intro v hvR hvL
    exact Set.disjoint_left.mp H.right_left
      (R.attach_mem_walk_support hvR) (L.tail_mem_walk_support hvL)
  right_tail_left_attach := by
    rw [Set.disjoint_left]
    intro v hvR hvL
    exact Set.disjoint_left.mp H.right_left
      (R.tail_mem_walk_support hvR) (L.attach_mem_walk_support hvL)
  right_attach_side_tail := by
    rw [Set.disjoint_left]
    intro v hvR hvU
    exact Set.disjoint_left.mp H.right_side
      (R.attach_mem_walk_support hvR) (U.tail_mem_walk_support hvU)
  right_tail_side_attach := by
    rw [Set.disjoint_left]
    intro v hvR hvU
    exact Set.disjoint_left.mp H.right_side
      (R.tail_mem_walk_support hvR) (U.attach_mem_walk_support hvU)
  left_attach_side_tail := by
    rw [Set.disjoint_left]
    intro v hvL hvU
    exact Set.disjoint_left.mp H.left_side
      (L.attach_mem_walk_support hvL) (U.tail_mem_walk_support hvU)
  left_tail_side_attach := by
    rw [Set.disjoint_left]
    intro v hvL hvU
    exact Set.disjoint_left.mp H.left_side
      (L.tail_mem_walk_support hvL) (U.attach_mem_walk_support hvU)
  left_tail_side_tail := by
    rw [Set.disjoint_left]
    intro v hvL hvU
    exact Set.disjoint_left.mp H.left_side
      (L.tail_mem_walk_support hvL) (U.tail_mem_walk_support hvU)
  right_tail_rim := by
    intro j v hvTail hvRim
    exact H.right_meets_rims_only_at_attach j v
      (R.tail_mem_walk_support hvTail) hvRim
  left_tail_rim := by
    intro j v hvTail hvRim
    exact H.left_meets_rims_only_at_attach j v
      (L.tail_mem_walk_support hvTail) hvRim
  side_tail_rim := by
    intro j v hvTail hvRim
    exact H.side_meets_rims_only_at_attach j v
      (U.tail_mem_walk_support hvTail) hvRim

/-- A full side-right support-attached leg-separation package implies the
componentwise residual package used by the later source split. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailsSideRightResidual.of_legSeparation
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    {R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0)}
    {L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1)}
    {U :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)}
    (H : F.SupportAttachedCleanTailLegSeparationSideRight R L U) :
    F.SupportAttachedCleanTailsSideRightResidual R L U where
  right_attach_left_tail := by
    rw [Set.disjoint_left]
    intro v hvR hvL
    exact Set.disjoint_left.mp H.right_left
      (R.attach_mem_walk_support hvR) (L.tail_mem_walk_support hvL)
  right_tail_left_attach := by
    rw [Set.disjoint_left]
    intro v hvR hvL
    exact Set.disjoint_left.mp H.right_left
      (R.tail_mem_walk_support hvR) (L.attach_mem_walk_support hvL)
  right_attach_side_tail := by
    rw [Set.disjoint_left]
    intro v hvR hvU
    exact Set.disjoint_left.mp H.right_side
      (R.attach_mem_walk_support hvR) (U.tail_mem_walk_support hvU)
  right_tail_side_attach := by
    rw [Set.disjoint_left]
    intro v hvR hvU
    exact Set.disjoint_left.mp H.right_side
      (R.tail_mem_walk_support hvR) (U.attach_mem_walk_support hvU)
  left_attach_side_tail := by
    rw [Set.disjoint_left]
    intro v hvL hvU
    exact Set.disjoint_left.mp H.left_side
      (L.attach_mem_walk_support hvL) (U.tail_mem_walk_support hvU)
  left_tail_side_attach := by
    rw [Set.disjoint_left]
    intro v hvL hvU
    exact Set.disjoint_left.mp H.left_side
      (L.tail_mem_walk_support hvL) (U.attach_mem_walk_support hvU)
  right_tail_side_tail := by
    rw [Set.disjoint_left]
    intro v hvR hvU
    exact Set.disjoint_left.mp H.right_side
      (R.tail_mem_walk_support hvR) (U.tail_mem_walk_support hvU)
  right_tail_rim := by
    intro j v hvTail hvRim
    exact H.right_meets_rims_only_at_attach j v
      (R.tail_mem_walk_support hvTail) hvRim
  left_tail_rim := by
    intro j v hvTail hvRim
    exact H.left_meets_rims_only_at_attach j v
      (L.tail_mem_walk_support hvTail) hvRim
  side_tail_rim := by
    intro j v hvTail hvRim
    exact H.side_meets_rims_only_at_attach j v
      (U.tail_mem_walk_support hvTail) hvRim

/-- In the side-left `K_{3,3}` common-branch case, the residual clean-tail
package plus the already-normalized support-attachment geometry gives the full
leg-separation package needed to insert the three tails into the rim skeleton.

This extracts the core assembly used by the no-path source constructor, so the
remaining `K_{3,3}` source obligation can target the residual clean-tail facts
directly. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailLegSeparationSideLeft.of_residual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    {R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0)}
    {L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1)}
    {U :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)}
    (hR_avoid :
      (Classical.choice hK33).branchVertex c ∉ R.attach.support)
    (hL_avoid :
      (Classical.choice hK33).branchVertex c ∉ L.attach.support)
    (H : F.SupportAttachedCleanTailsSideLeftResidual R L U) :
    F.SupportAttachedCleanTailLegSeparationSideLeft R L U :=
  F.supportAttachedCleanTailLegSeparationSideLeft_of_parts R L U
    (F.right_left_attach_support_disjoint_of_right_avoids_common
      R L hR_avoid)
    H.right_attach_left_tail
    H.right_tail_left_attach
    (R.tail_disjoint_left_tail hno_cross L)
    (F.right_sideLeft_attach_support_disjoint_of_right_avoids_common
      R U hR_avoid)
    H.right_attach_side_tail
    H.right_tail_side_attach
    (R.tail_disjoint_left_tail hno_cross U)
    (F.left_sideLeft_attach_support_disjoint_of_left_avoids_common
      L U hL_avoid)
    H.left_attach_side_tail
    H.left_tail_side_attach
    H.left_tail_side_tail
    H.right_tail_rim H.left_tail_rim H.side_tail_rim

/-- Side-right version of
`SupportAttachedCleanTailLegSeparationSideLeft.of_residual`. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailLegSeparationSideRight.of_residual
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    {F : A.K33RimSourceEdgePaths}
    {R :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.right_or_path.supportSet (F.rimAttach 0)}
    {L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1)}
    {U :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2)}
    (hR_avoid :
      (Classical.choice hK33).branchVertex c ∉ R.attach.support)
    (hL_avoid :
      (Classical.choice hK33).branchVertex c ∉ L.attach.support)
    (H : F.SupportAttachedCleanTailsSideRightResidual R L U) :
    F.SupportAttachedCleanTailLegSeparationSideRight R L U :=
  F.supportAttachedCleanTailLegSeparationSideRight_of_parts R L U
    (F.right_left_attach_support_disjoint_of_right_avoids_common
      R L hR_avoid)
    H.right_attach_left_tail
    H.right_tail_left_attach
    (R.tail_disjoint_left_tail hno_cross L)
    (F.right_sideRight_attach_support_disjoint_of_right_avoids_common
      R U hR_avoid)
    H.right_attach_side_tail
    H.right_tail_side_attach
    H.right_tail_side_tail
    (F.left_sideRight_attach_support_disjoint_of_left_avoids_common
      L U hL_avoid)
    H.left_attach_side_tail
    H.left_tail_side_attach
    (L.tail_disjoint_right_tail hno_cross U)
    H.right_tail_rim H.left_tail_rim H.side_tail_rim

/-- In the side-left common-branch `K_{3,3}` case, non-path canonical targets
plus the residual local separation/contact facts assemble the source-proof
tripod. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_tripod_sideLeft_of_no_path_targets_and_residual
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
        P.pathSet)
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
    Nonempty S.Tripod := by
  classical
  rcases F.exists_supportAttachedCleanTailsSideLeft_nontrivial_attach_avoids_common_of_no_path_targets
      hSide hR_not_path hL_not_path hU_not_path with
    ⟨R, L, U, hR_avoid, hL_avoid, hU_avoid⟩
  have H := hres R L U hR_avoid hL_avoid hU_avoid
  have hsep :
      F.SupportAttachedCleanTailLegSeparationSideLeft R L U :=
    GMIX24Split.MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailLegSeparationSideLeft.of_residual
      hR_avoid hL_avoid H
  have hLU : L.a ≠ U.a := by
    intro h
    exact Set.disjoint_left.mp H.left_tail_side_tail
      L.tail.end_mem_support
      (by simp [h])
  exact F.exists_tripodWithSupportAttachedCleanTailsSideLeft
    R L U hLU hsep

/-- Side-right version of
`exists_tripod_sideLeft_of_no_path_targets_and_residual`. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_tripod_sideRight_of_no_path_targets_and_residual
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
        P.pathSet)
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
    Nonempty S.Tripod := by
  classical
  rcases F.exists_supportAttachedCleanTailsSideRight_nontrivial_attach_avoids_common_of_no_path_targets
      hSide hR_not_path hL_not_path hU_not_path with
    ⟨R, L, U, hR_avoid, hL_avoid, hU_avoid⟩
  have H := hres R L U hR_avoid hL_avoid hU_avoid
  have hsep :
      F.SupportAttachedCleanTailLegSeparationSideRight R L U :=
    GMIX24Split.MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailLegSeparationSideRight.of_residual
      hR_avoid hL_avoid H
  have hRU : R.a ≠ U.a := by
    intro h
    exact Set.disjoint_left.mp H.right_tail_side_tail
      R.tail.end_mem_support
      (by simp [h])
  exact F.exists_tripodWithSupportAttachedCleanTailsSideRight
    R L U hRU hsep


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
