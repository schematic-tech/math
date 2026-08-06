import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- The selected right and left endpoint paths in a common-branch package have
no support intersection away from the common host vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.right_left_support_inter_eq_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    {w : V}
    (hwRight : w ∈ E.right.path.support)
    (hwLeft : w ∈ E.left.path.support) :
    w = C.z := by
  have hcommon :
      w = (Classical.choice hK).branchVertex c :=
    A.right_left_support_paths_inter_eq_common
      E.right.support_subset E.left.support_subset hwRight hwLeft
  exact hcommon.trans A.z_eq_branchVertex.symm

/-- The selected right and side endpoint paths in a common-branch package have
no support intersection away from the common host vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.right_side_support_inter_eq_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    {w : V}
    (hwRight : w ∈ E.right.path.support)
    (hwSide : w ∈ E.side.path.support) :
    w = C.z := by
  have hcommon :
      w = (Classical.choice hK).branchVertex c :=
    A.right_side_support_paths_inter_eq_common
      E.right.support_subset E.side.support_subset hwRight hwSide
  exact hcommon.trans A.z_eq_branchVertex.symm

/-- The selected left and side endpoint paths in a common-branch package have
no support intersection away from the common host vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.left_side_support_inter_eq_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices)
    {w : V}
    (hwLeft : w ∈ E.left.path.support)
    (hwSide : w ∈ E.side.path.support) :
    w = C.z := by
  have hcommon :
      w = (Classical.choice hK).branchVertex c :=
      A.left_side_support_paths_inter_eq_common
      E.left.support_subset E.side.support_subset hwLeft hwSide
  exact hcommon.trans A.z_eq_branchVertex.symm

/-- Away from the common host vertex, the selected right and left endpoint
paths in a common-branch package are disjoint. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.right_left_support_disjoint_off_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices) :
    Disjoint
      {w : V | w ∈ E.right.path.support ∧ w ≠ C.z}
      {w : V | w ∈ E.left.path.support ∧ w ≠ C.z} := by
  rw [Set.disjoint_left]
  intro w hwRight hwLeft
  exact hwRight.2
    (E.right_left_support_inter_eq_z A hwRight.1 hwLeft.1)

/-- Away from the common host vertex, the selected right and side endpoint
paths in a common-branch package are disjoint. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.right_side_support_disjoint_off_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices) :
    Disjoint
      {w : V | w ∈ E.right.path.support ∧ w ≠ C.z}
      {w : V | w ∈ E.side.path.support ∧ w ≠ C.z} := by
  rw [Set.disjoint_left]
  intro w hwRight hwSide
  exact hwRight.2
    (E.right_side_support_inter_eq_z A hwRight.1 hwSide.1)

/-- Away from the common host vertex, the selected left and side endpoint
paths in a common-branch package are disjoint. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchEndpointPathChoices.left_side_support_disjoint_off_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchEndpointPathChoices) :
    Disjoint
      {w : V | w ∈ E.left.path.support ∧ w ≠ C.z}
      {w : V | w ∈ E.side.path.support ∧ w ≠ C.z} := by
  rw [Set.disjoint_left]
  intro w hwLeft hwSide
  exact hwLeft.2
    (E.left_side_support_inter_eq_z A hwLeft.1 hwSide.1)

/-- The leg-separation obligations for inserting attached clean tails into the
`K_{3,3}` rim skeleton when the side leg exits to the left boundary arc. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.AttachedCleanTailLegSeparationSideLeft
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {E : C.CommonBranchEndpointPathChoices}
    (R : E.right.AttachedCleanTailToRightBoundaryArc (F.rimAttach 0))
    (L : E.left.AttachedCleanTailToLeftBoundaryArc (F.rimAttach 1))
    (U : E.side.AttachedCleanTailToLeftBoundaryArc (F.rimAttach 2)) : Prop where
  right_left :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ L.walk.support}
  right_side :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ U.walk.support}
  left_side :
    Disjoint {v : V | v ∈ L.walk.support}
      {v : V | v ∈ U.walk.support}
  right_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ R.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 0
  left_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ L.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 1
  side_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ U.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2

/-- The leg-separation obligations for inserting attached clean tails into the
`K_{3,3}` rim skeleton when the side leg exits to the right boundary arc. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.AttachedCleanTailLegSeparationSideRight
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {E : C.CommonBranchEndpointPathChoices}
    (R : E.right.AttachedCleanTailToRightBoundaryArc (F.rimAttach 0))
    (L : E.left.AttachedCleanTailToLeftBoundaryArc (F.rimAttach 1))
    (U : E.side.AttachedCleanTailToRightBoundaryArc (F.rimAttach 2)) : Prop where
  right_left :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ L.walk.support}
  right_side :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ U.walk.support}
  left_side :
    Disjoint {v : V | v ∈ L.walk.support}
      {v : V | v ∈ U.walk.support}
  right_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ R.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 0
  left_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ L.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 1
  side_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ U.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2

private noncomputable def tripodOfThreeLegs
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (b₀ b₁ b₂ : V)
    (hb₀ : b₀ ∈ S.boundarySet)
    (hb₁ : b₁ ∈ S.boundarySet)
    (hb₂ : b₂ ∈ S.boundarySet)
    (q₀ : S.graph.Walk (F.rimAttach 0) b₀)
    (q₁ : S.graph.Walk (F.rimAttach 1) b₁)
    (q₂ : S.graph.Walk (F.rimAttach 2) b₂)
    (hq₀ : q₀.IsPath) (hq₁ : q₁.IsPath) (hq₂ : q₂.IsPath)
    (hboundary_injective :
      Function.Injective
        (fun i : Fin 3 => if i = 0 then b₀ else if i = 1 then b₁ else b₂))
    (hq₀q₁ : Disjoint {v : V | v ∈ q₀.support} {v : V | v ∈ q₁.support})
    (hq₀q₂ : Disjoint {v : V | v ∈ q₀.support} {v : V | v ∈ q₂.support})
    (hq₁q₂ : Disjoint {v : V | v ∈ q₁.support} {v : V | v ∈ q₂.support})
    (hq₀_rim : forall j : Fin 3, forall v : V,
      v ∈ q₀.support -> v ∈ (F.rim j).support -> v = F.rimAttach 0)
    (hq₁_rim : forall j : Fin 3, forall v : V,
      v ∈ q₁.support -> v ∈ (F.rim j).support -> v = F.rimAttach 1)
    (hq₂_rim : forall j : Fin 3, forall v : V,
      v ∈ q₂.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2) :
    S.Tripod := by
  classical
  let boundary : Fin 3 -> V := fun i =>
    if i = 0 then b₀ else if i = 1 then b₁ else b₂
  let legWithPath : forall i : Fin 3,
      {q : S.graph.Walk (F.rimAttach i) (boundary i) // q.IsPath} := by
    intro i
    by_cases h₀ : i = 0
    · subst i
      exact ⟨q₀, hq₀⟩
    · by_cases h₁ : i = 1
      · subst i
        exact ⟨q₁, hq₁⟩
      · have h₂ : i = 2 := by
          fin_cases i <;> simp at h₀ h₁ ⊢
        subst i
        exact ⟨q₂, hq₂⟩
  let leg : forall i : Fin 3, S.graph.Walk (F.rimAttach i) (boundary i) :=
    fun i => (legWithPath i).1
  refine
    F.toTripodWithLegs boundary ?_
      (by simpa [boundary] using hboundary_injective) leg ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [boundary, hb₀, hb₁, hb₂]
  · intro i
    exact (legWithPath i).2
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · simpa [leg, legWithPath] using hq₀q₁
    · simpa [leg, legWithPath] using hq₀q₂
    · simpa [leg, legWithPath] using hq₀q₁.symm
    · simpa [leg, legWithPath] using hq₁q₂
    · simpa [leg, legWithPath] using hq₀q₂.symm
    · simpa [leg, legWithPath] using hq₁q₂.symm
  · intro i j v hvleg hvrim
    fin_cases i <;> simp [leg, legWithPath] at hvleg ⊢
    · exact hq₀_rim j v hvleg hvrim
    · exact hq₁_rim j v hvleg hvrim
    · exact hq₂_rim j v hvleg hvrim

/-- Insert three attached clean tails into the `K_{3,3}` rim skeleton, in the
case where the side leg exits to the left boundary arc. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.toTripodWithAttachedCleanTailsSideLeft
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {E : C.CommonBranchEndpointPathChoices}
    (R : E.right.AttachedCleanTailToRightBoundaryArc (F.rimAttach 0))
    (L : E.left.AttachedCleanTailToLeftBoundaryArc (F.rimAttach 1))
    (U : E.side.AttachedCleanTailToLeftBoundaryArc (F.rimAttach 2))
    (hboundary_injective :
      Function.Injective
        (fun i : Fin 3 =>
          if i = 0 then R.a else if i = 1 then L.a else U.a))
    (hsep : F.AttachedCleanTailLegSeparationSideLeft R L U) :
    S.Tripod := by
  exact
    tripodOfThreeLegs F R.a L.a U.a
      (P.rightBoundaryArc_subset R.a_mem_rightBoundaryArc)
      (P.leftBoundaryArc_subset L.a_mem_leftBoundaryArc)
      (P.leftBoundaryArc_subset U.a_mem_leftBoundaryArc)
      R.walk L.walk U.walk R.walk_isPath L.walk_isPath U.walk_isPath
      hboundary_injective hsep.right_left hsep.right_side hsep.left_side
      hsep.right_meets_rims_only_at_attach
      hsep.left_meets_rims_only_at_attach
      hsep.side_meets_rims_only_at_attach

/-- Insert three attached clean tails into the `K_{3,3}` rim skeleton, in the
case where the side leg exits to the right boundary arc. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.toTripodWithAttachedCleanTailsSideRight
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {E : C.CommonBranchEndpointPathChoices}
    (R : E.right.AttachedCleanTailToRightBoundaryArc (F.rimAttach 0))
    (L : E.left.AttachedCleanTailToLeftBoundaryArc (F.rimAttach 1))
    (U : E.side.AttachedCleanTailToRightBoundaryArc (F.rimAttach 2))
    (hboundary_injective :
      Function.Injective
        (fun i : Fin 3 =>
          if i = 0 then R.a else if i = 1 then L.a else U.a))
    (hsep : F.AttachedCleanTailLegSeparationSideRight R L U) :
    S.Tripod := by
  exact
    tripodOfThreeLegs F R.a L.a U.a
      (P.rightBoundaryArc_subset R.a_mem_rightBoundaryArc)
      (P.leftBoundaryArc_subset L.a_mem_leftBoundaryArc)
      (P.rightBoundaryArc_subset U.a_mem_rightBoundaryArc)
      R.walk L.walk U.walk R.walk_isPath L.walk_isPath U.walk_isPath
      hboundary_injective hsep.right_left hsep.right_side hsep.left_side
      hsep.right_meets_rims_only_at_attach
      hsep.left_meets_rims_only_at_attach
      hsep.side_meets_rims_only_at_attach

/-- Support-level leg-separation obligations for inserting clean tails into
the `K_{3,3}` rim skeleton when the side leg exits to the left boundary arc.
Unlike `AttachedCleanTailLegSeparationSideLeft`, the attachment segments are
allowed to use the whole strict-subdivision source-edge support. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailLegSeparationSideLeft
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
  right_left :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ L.walk.support}
  right_side :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ U.walk.support}
  left_side :
    Disjoint {v : V | v ∈ L.walk.support}
      {v : V | v ∈ U.walk.support}
  right_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ R.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 0
  left_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ L.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 1
  side_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ U.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2

/-- Support-level leg-separation obligations for inserting clean tails into
the `K_{3,3}` rim skeleton when the side leg exits to the right boundary arc. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.SupportAttachedCleanTailLegSeparationSideRight
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
  right_left :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ L.walk.support}
  right_side :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ U.walk.support}
  left_side :
    Disjoint {v : V | v ∈ L.walk.support}
      {v : V | v ∈ U.walk.support}
  right_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ R.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 0
  left_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ L.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 1
  side_meets_rims_only_at_attach :
    forall j : Fin 3, forall v : V,
      v ∈ U.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2

/-- Rim-contact normalization for a right support-attached leg, reducing the
whole appended walk to the already-normalized support segment and the clean
tail segment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
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
    (htail :
      forall j : Fin 3, forall v : V,
        v ∈ R.tail.support -> v ∈ (F.rim j).support -> v = F.rimAttach 0) :
    forall j : Fin 3, forall v : V,
      v ∈ R.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 0 := by
  intro j v hvWalk hvRim
  rw [GMIX24CutPath.SupportAttachedCleanTailToRightBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvWalk
  rcases hvWalk with hvAttach | hvTail
  · exact F.right_support_meets_rims_only_at_attach j v
      (R.attach_support_subset v hvAttach) hvRim
  · exact htail j v hvTail hvRim

/-- Rim-contact normalization for a left support-attached leg. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (L :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_path.supportSet (F.rimAttach 1))
    (htail :
      forall j : Fin 3, forall v : V,
        v ∈ L.tail.support -> v ∈ (F.rim j).support -> v = F.rimAttach 1) :
    forall j : Fin 3, forall v : V,
      v ∈ L.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 1 := by
  intro j v hvWalk hvRim
  rw [GMIX24CutPath.SupportAttachedCleanTailToLeftBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvWalk
  rcases hvWalk with hvAttach | hvTail
  · exact F.left_support_meets_rims_only_at_attach j v
      (L.attach_support_subset v hvAttach) hvRim
  · exact htail j v hvTail hvRim

/-- Rim-contact normalization for a side support-attached leg exiting to the
left boundary arc. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.sideLeft_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (U :
      P.SupportAttachedCleanTailToLeftBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2))
    (htail :
      forall j : Fin 3, forall v : V,
        v ∈ U.tail.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2) :
    forall j : Fin 3, forall v : V,
      v ∈ U.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2 := by
  intro j v hvWalk hvRim
  rw [GMIX24CutPath.SupportAttachedCleanTailToLeftBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvWalk
  rcases hvWalk with hvAttach | hvTail
  · exact F.side_support_meets_rims_only_at_attach j v
      (U.attach_support_subset v hvAttach) hvRim
  · exact htail j v hvTail hvRim

/-- Rim-contact normalization for a side support-attached leg exiting to the
right boundary arc. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.sideRight_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (U :
      P.SupportAttachedCleanTailToRightBoundaryArc
        D.left_or_right.supportSet (F.rimAttach 2))
    (htail :
      forall j : Fin 3, forall v : V,
        v ∈ U.tail.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2) :
    forall j : Fin 3, forall v : V,
      v ∈ U.walk.support -> v ∈ (F.rim j).support -> v = F.rimAttach 2 := by
  intro j v hvWalk hvRim
  rw [GMIX24CutPath.SupportAttachedCleanTailToRightBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvWalk
  rcases hvWalk with hvAttach | hvTail
  · exact F.side_support_meets_rims_only_at_attach j v
      (U.attach_support_subset v hvAttach) hvRim
  · exact htail j v hvTail hvRim

/-- Assemble the support-attached clean-tail leg-separation package for the
side-left case from componentwise disjointness and tail-rim contact facts. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.supportAttachedCleanTailLegSeparationSideLeft_of_parts
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
        D.left_or_right.supportSet (F.rimAttach 2))
    (hRL_AA :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ L.attach.support})
    (hRL_AT :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ L.tail.support})
    (hRL_TA :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ L.attach.support})
    (hRL_TT :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ L.tail.support})
    (hRU_AA :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ U.attach.support})
    (hRU_AT :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ U.tail.support})
    (hRU_TA :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ U.attach.support})
    (hRU_TT :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ U.tail.support})
    (hLU_AA :
      Disjoint {v : V | v ∈ L.attach.support}
        {v : V | v ∈ U.attach.support})
    (hLU_AT :
      Disjoint {v : V | v ∈ L.attach.support}
        {v : V | v ∈ U.tail.support})
    (hLU_TA :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ U.attach.support})
    (hLU_TT :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ U.tail.support})
    (hR_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ R.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 0)
    (hL_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ L.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 1)
    (hU_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ U.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 2) :
    F.SupportAttachedCleanTailLegSeparationSideLeft R L U where
  right_left :=
    R.walk_disjoint_left_walk_of_parts L
      hRL_AA hRL_AT hRL_TA hRL_TT
  right_side :=
    R.walk_disjoint_left_walk_of_parts U
      hRU_AA hRU_AT hRU_TA hRU_TT
  left_side :=
    L.walk_disjoint_left_walk_of_parts U
      hLU_AA hLU_AT hLU_TA hLU_TT
  right_meets_rims_only_at_attach :=
    F.right_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
      R hR_tail_rim
  left_meets_rims_only_at_attach :=
    F.left_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
      L hL_tail_rim
  side_meets_rims_only_at_attach :=
    F.sideLeft_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
      U hU_tail_rim

/-- Assemble the support-attached clean-tail leg-separation package for the
side-right case from componentwise disjointness and tail-rim contact facts. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.supportAttachedCleanTailLegSeparationSideRight_of_parts
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
        D.left_or_right.supportSet (F.rimAttach 2))
    (hRL_AA :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ L.attach.support})
    (hRL_AT :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ L.tail.support})
    (hRL_TA :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ L.attach.support})
    (hRL_TT :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ L.tail.support})
    (hRU_AA :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ U.attach.support})
    (hRU_AT :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ U.tail.support})
    (hRU_TA :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ U.attach.support})
    (hRU_TT :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ U.tail.support})
    (hLU_AA :
      Disjoint {v : V | v ∈ L.attach.support}
        {v : V | v ∈ U.attach.support})
    (hLU_AT :
      Disjoint {v : V | v ∈ L.attach.support}
        {v : V | v ∈ U.tail.support})
    (hLU_TA :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ U.attach.support})
    (hLU_TT :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ U.tail.support})
    (hR_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ R.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 0)
    (hL_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ L.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 1)
    (hU_tail_rim :
      forall j : Fin 3, forall v : V,
        v ∈ U.tail.support -> v ∈ (F.rim j).support ->
          v = F.rimAttach 2) :
    F.SupportAttachedCleanTailLegSeparationSideRight R L U where
  right_left :=
    R.walk_disjoint_left_walk_of_parts L
      hRL_AA hRL_AT hRL_TA hRL_TT
  right_side :=
    R.walk_disjoint_right_walk_of_parts U
      hRU_AA hRU_AT hRU_TA hRU_TT
  left_side :=
    L.walk_disjoint_right_walk_of_parts U
      hLU_AA hLU_AT hLU_TA hLU_TT
  right_meets_rims_only_at_attach :=
    F.right_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
      R hR_tail_rim
  left_meets_rims_only_at_attach :=
    F.left_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
      L hL_tail_rim
  side_meets_rims_only_at_attach :=
    F.sideRight_supportAttachedCleanTail_meets_rims_only_at_attach_of_tail
      U hU_tail_rim

/-- Insert three support-attached clean tails into the `K_{3,3}` rim skeleton
when the side leg exits to the left boundary arc. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.toTripodWithSupportAttachedCleanTailsSideLeft
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
        D.left_or_right.supportSet (F.rimAttach 2))
    (hboundary_injective :
      Function.Injective
        (fun i : Fin 3 =>
          if i = 0 then R.a else if i = 1 then L.a else U.a))
    (hsep : F.SupportAttachedCleanTailLegSeparationSideLeft R L U) :
    S.Tripod := by
  exact
    tripodOfThreeLegs F R.a L.a U.a
      (P.rightBoundaryArc_subset R.a_mem_rightBoundaryArc)
      (P.leftBoundaryArc_subset L.a_mem_leftBoundaryArc)
      (P.leftBoundaryArc_subset U.a_mem_leftBoundaryArc)
      R.walk L.walk U.walk R.walk_isPath L.walk_isPath U.walk_isPath
      hboundary_injective hsep.right_left hsep.right_side hsep.left_side
      hsep.right_meets_rims_only_at_attach
      hsep.left_meets_rims_only_at_attach
      hsep.side_meets_rims_only_at_attach

/-- Insert three support-attached clean tails into the `K_{3,3}` rim skeleton
when the side leg exits to the right boundary arc. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.toTripodWithSupportAttachedCleanTailsSideRight
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
        D.left_or_right.supportSet (F.rimAttach 2))
    (hboundary_injective :
      Function.Injective
        (fun i : Fin 3 =>
          if i = 0 then R.a else if i = 1 then L.a else U.a))
    (hsep : F.SupportAttachedCleanTailLegSeparationSideRight R L U) :
    S.Tripod := by
  exact
    tripodOfThreeLegs F R.a L.a U.a
      (P.rightBoundaryArc_subset R.a_mem_rightBoundaryArc)
      (P.leftBoundaryArc_subset L.a_mem_leftBoundaryArc)
      (P.rightBoundaryArc_subset U.a_mem_rightBoundaryArc)
      R.walk L.walk U.walk R.walk_isPath L.walk_isPath U.walk_isPath
      hboundary_injective hsep.right_left hsep.right_side hsep.left_side
      hsep.right_meets_rims_only_at_attach
      hsep.left_meets_rims_only_at_attach
      hsep.side_meets_rims_only_at_attach

/-- If the side-left support-attached clean tails have separated legs and the
two left-boundary endpoints are distinct, they give an ambient tripod. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_tripodWithSupportAttachedCleanTailsSideLeft
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
        D.left_or_right.supportSet (F.rimAttach 2))
    (hLU : L.a ≠ U.a)
    (hsep : F.SupportAttachedCleanTailLegSeparationSideLeft R L U) :
    Nonempty S.Tripod :=
  ⟨F.toTripodWithSupportAttachedCleanTailsSideLeft R L U
    (GMIX24CutPath.supportAttachedBoundary_injective_sideLeft
      hno_cross R L U hLU)
    hsep⟩

/-- If the side-right support-attached clean tails have separated legs and the
two right-boundary endpoints are distinct, they give an ambient tripod. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.exists_tripodWithSupportAttachedCleanTailsSideRight
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
        D.left_or_right.supportSet (F.rimAttach 2))
    (hRU : R.a ≠ U.a)
    (hsep : F.SupportAttachedCleanTailLegSeparationSideRight R L U) :
    Nonempty S.Tripod :=
  ⟨F.toTripodWithSupportAttachedCleanTailsSideRight R L U
    (GMIX24CutPath.supportAttachedBoundary_injective_sideRight
      hno_cross R L U hRU)
    hsep⟩

/-- Nontrivial selected endpoints in a common-branch package are pairwise
distinct. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchNontrivialEndpointPathChoices.right_left_target_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchNontrivialEndpointPathChoices) :
    E.choices.right.target ≠ E.choices.left.target := by
  intro hEq
  exact E.right_target_ne_z
    (E.choices.right_left_target_eq_z_of_eq A hEq)

/-- Nontrivial right and side selected endpoints in a common-branch package are
distinct. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchNontrivialEndpointPathChoices.right_side_target_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchNontrivialEndpointPathChoices) :
    E.choices.right.target ≠ E.choices.side.target := by
  intro hEq
  exact E.right_target_ne_z
    (E.choices.right_side_target_eq_z_of_eq A hEq)

/-- Nontrivial left and side selected endpoints in a common-branch package are
distinct. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchNontrivialEndpointPathChoices.left_side_target_ne
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    (E : C.CommonBranchNontrivialEndpointPathChoices) :
    E.choices.left.target ≠ E.choices.side.target := by
  intro hEq
  exact E.left_target_ne_z
    (E.choices.left_side_target_eq_z_of_eq A hEq)

/-- Choose the first concrete endpoint of each tagged host edge and build the
checked three-endpoint path package for a common-branch arm configuration. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.commonBranchEndpointPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    C.CommonBranchEndpointPaths := by
  classical
  exact
    (C.commonBranchEndpointPathChoices A
      C.rightFstEndpointPath C.leftFstEndpointPath C.sideFstEndpointPath).toEndpointPaths

/-- Internal vertices of the right and left common-branch arms are disjoint. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_left_arms_internal_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Disjoint
      (Walk.InternalVertices A.right_arm.path)
      (Walk.InternalVertices A.left_arm.path) := by
  rw [Set.disjoint_left]
  intro w hwRight hwLeft
  have hcommon :
      w = (Classical.choice hK).branchVertex c :=
    A.right_left_arm_inter_eq_common hwRight.1 hwLeft.1
  exact hwRight.2.1 (by simpa [A.z_eq_branchVertex] using hcommon)

/-- Internal vertices of the right and side common-branch arms are disjoint. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_side_arms_internal_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Disjoint
      (Walk.InternalVertices A.right_arm.path)
      (Walk.InternalVertices A.side_arm.path) := by
  rw [Set.disjoint_left]
  intro w hwRight hwSide
  have hcommon :
      w = (Classical.choice hK).branchVertex c :=
    A.right_side_arm_inter_eq_common hwRight.1 hwSide.1
  exact hwRight.2.1 (by simpa [A.z_eq_branchVertex] using hcommon)

/-- Internal vertices of the left and side common-branch arms are disjoint. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_side_arms_internal_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Disjoint
      (Walk.InternalVertices A.left_arm.path)
      (Walk.InternalVertices A.side_arm.path) := by
  rw [Set.disjoint_left]
  intro w hwLeft hwSide
  have hcommon :
      w = (Classical.choice hK).branchVertex c :=
    A.left_side_arm_inter_eq_common hwLeft.1 hwSide.1
  exact hwLeft.2.1 (by simpa [A.z_eq_branchVertex] using hcommon)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
