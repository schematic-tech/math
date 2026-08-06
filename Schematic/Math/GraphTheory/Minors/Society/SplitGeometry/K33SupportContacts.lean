import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.K33Rims

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
private theorem endpoint_eq_of_distinct_endpoint_cover
    {W : Type*} {x y common other w : W}
    (hcommon : common = x ∨ common = y)
    (hother : other = x ∨ other = y)
    (hother_ne_common : other ≠ common)
    (hw : w = x ∨ w = y) :
    w = common ∨ w = other := by
  rcases hcommon with hc | hc <;> rcases hother with ho | ho
  · exact False.elim (hother_ne_common (ho.trans hc.symm))
  · rcases hw with hw | hw
    · exact Or.inl (hw.trans hc.symm)
    · exact Or.inr (hw.trans ho.symm)
  · rcases hw with hw | hw
    · exact Or.inr (hw.trans ho.symm)
    · exact Or.inl (hw.trans hc.symm)
  · exact False.elim (hother_ne_common (ho.trans hc.symm))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_source_endpoint_eq_common_or_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c w : W}
    (A : C.CommonBranchArmPaths c)
    (hw : w = D.right_or_path.x ∨ w = D.right_or_path.y) :
    w = c ∨ w = A.right_arm.other := by
  exact
    endpoint_eq_of_distinct_endpoint_cover A.c_right
      A.right_arm.other_endpoint A.right_arm.other_ne hw

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_source_endpoint_eq_common_or_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c w : W}
    (A : C.CommonBranchArmPaths c)
    (hw : w = D.left_or_path.x ∨ w = D.left_or_path.y) :
    w = c ∨ w = A.left_arm.other := by
  exact
    endpoint_eq_of_distinct_endpoint_cover A.c_left
      A.left_arm.other_endpoint A.left_arm.other_ne hw

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_source_endpoint_eq_common_or_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c w : W}
    (A : C.CommonBranchArmPaths c)
    (hw : w = D.left_or_right.x ∨ w = D.left_or_right.y) :
    w = c ∨ w = A.side_arm.other := by
  exact
    endpoint_eq_of_distinct_endpoint_cover A.c_side
      A.side_arm.other_endpoint A.side_arm.other_ne hw

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_classified_support
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (A : C.CommonBranchArmPaths c) :
    ClassifiedSubdivisionEdgeSupport
      (Classical.choice hK33) c A.right_arm.other where
  source₁ := D.right_or_path.x
  source₂ := D.right_or_path.y
  adj := D.right_or_path.hxy
  endpoints := fun w hw =>
    A.right_source_endpoint_eq_common_or_other (w := w) hw
  support := D.right_or_path.supportSet
  support_subset := by
    intro z hz
    simpa [TaggedSupportWitnessData.supportSet] using hz

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_classified_support
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (A : C.CommonBranchArmPaths c) :
    ClassifiedSubdivisionEdgeSupport
      (Classical.choice hK33) c A.left_arm.other where
  source₁ := D.left_or_path.x
  source₂ := D.left_or_path.y
  adj := D.left_or_path.hxy
  endpoints := fun w hw =>
    A.left_source_endpoint_eq_common_or_other (w := w) hw
  support := D.left_or_path.supportSet
  support_subset := by
    intro z hz
    simpa [TaggedSupportWitnessData.supportSet] using hz

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_classified_support
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    (A : C.CommonBranchArmPaths c) :
    ClassifiedSubdivisionEdgeSupport
      (Classical.choice hK33) c A.side_arm.other where
  source₁ := D.left_or_right.x
  source₂ := D.left_or_right.y
  adj := D.left_or_right.hxy
  endpoints := fun w hw =>
    A.side_source_endpoint_eq_common_or_other (w := w) hw
  support := D.left_or_right.supportSet
  support_subset := by
    intro z hz
    simpa [TaggedSupportWitnessData.supportSet] using hz

/-- The right mixed source-edge support can meet the left half of the right
`K_{3,3}` rim only at the right rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_inter_left_to_right_arm_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.right_or_path.supportSet)
    (hzRim : z ∈ F.left_to_right_arm_path.support) :
    z = F.rimAttach 0 := by
  have h :=
    A.right_classified_support.inter_eq_matching_endpoint
      F.left_adj_right_arm F.left_ne_common
      {z : V | z ∈ F.left_to_right_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_right_arm_support_subset z hz)
      hzSupport hzRim
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_classified_support,
    MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using h

/-- The right mixed source-edge support can meet the right half of the right
`K_{3,3}` rim only at the right rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_inter_right_to_right_arm_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.right_or_path.supportSet)
    (hzRim : z ∈ F.right_to_right_arm_path.support) :
    z = F.rimAttach 0 := by
  have h :=
    A.right_classified_support.inter_eq_matching_endpoint
      F.right_adj_right_arm F.right_ne_common
      {z : V | z ∈ F.right_to_right_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_right_arm_support_subset z hz)
      hzSupport hzRim
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_classified_support,
    MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using h

/-- The right mixed source-edge support meets the right rim only at the right
rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_inter_right_rim_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.right_or_path.supportSet)
    (hzRim : z ∈ (F.rim 0).support) :
    z = F.rimAttach 0 := by
  classical
  have hzCases := F.right_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact F.right_support_inter_left_to_right_arm_eq_attach hzSupport hzLeft
  · exact F.right_support_inter_right_to_right_arm_eq_attach hzSupport hzRight

/-- The right mixed source-edge support is disjoint from the left half of the
left canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_disjoint_left_to_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.right_or_path.supportSet
      {z : V | z ∈ F.left_to_left_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_classified_support] using
    A.right_classified_support.disjoint F.left_adj_left_arm
      F.left_ne_common.symm A.left_arm.other_ne.symm
      F.left_adj_right_arm.ne.symm A.right_left_other_ne
      {z : V | z ∈ F.left_to_left_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_left_arm_support_subset z hz)

/-- The right mixed source-edge support is disjoint from the right half of the
left canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_disjoint_right_to_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.right_or_path.supportSet
      {z : V | z ∈ F.right_to_left_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_classified_support] using
    A.right_classified_support.disjoint F.right_adj_left_arm
      F.right_ne_common.symm A.left_arm.other_ne.symm
      F.right_adj_right_arm.ne.symm A.right_left_other_ne
      {z : V | z ∈ F.right_to_left_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_left_arm_support_subset z hz)

/-- The right mixed source-edge support is disjoint from the left canonical
`K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_disjoint_left_rim
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.right_or_path.supportSet
      {z : V | z ∈ (F.rim 1).support} := by
  classical
  rw [Set.disjoint_left]
  intro z hzSupport hzRim
  have hzCases := F.left_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact Set.disjoint_left.mp F.right_support_disjoint_left_to_left_arm
      hzSupport hzLeft
  · exact Set.disjoint_left.mp F.right_support_disjoint_right_to_left_arm
      hzSupport hzRight

/-- The right mixed source-edge support is disjoint from the left half of the
side canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_disjoint_left_to_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.right_or_path.supportSet
      {z : V | z ∈ F.left_to_side_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_classified_support] using
    A.right_classified_support.disjoint F.left_adj_side_arm
      F.left_ne_common.symm A.side_arm.other_ne.symm
      F.left_adj_right_arm.ne.symm A.right_side_other_ne
      {z : V | z ∈ F.left_to_side_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_side_arm_support_subset z hz)

/-- The right mixed source-edge support is disjoint from the right half of the
side canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_disjoint_right_to_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.right_or_path.supportSet
      {z : V | z ∈ F.right_to_side_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_classified_support] using
    A.right_classified_support.disjoint F.right_adj_side_arm
      F.right_ne_common.symm A.side_arm.other_ne.symm
      F.right_adj_right_arm.ne.symm A.right_side_other_ne
      {z : V | z ∈ F.right_to_side_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_side_arm_support_subset z hz)

/-- The right mixed source-edge support is disjoint from the side canonical
`K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_disjoint_side_rim
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.right_or_path.supportSet
      {z : V | z ∈ (F.rim 2).support} := by
  classical
  rw [Set.disjoint_left]
  intro z hzSupport hzRim
  have hzCases := F.side_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact Set.disjoint_left.mp F.right_support_disjoint_left_to_side_arm
      hzSupport hzLeft
  · exact Set.disjoint_left.mp F.right_support_disjoint_right_to_side_arm
      hzSupport hzRight

/-- The left mixed source-edge support can meet the left half of the left
`K_{3,3}` rim only at the left rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_inter_left_to_left_arm_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.left_or_path.supportSet)
    (hzRim : z ∈ F.left_to_left_arm_path.support) :
    z = F.rimAttach 1 := by
  have h :=
    A.left_classified_support.inter_eq_matching_endpoint
      F.left_adj_left_arm F.left_ne_common
      {z : V | z ∈ F.left_to_left_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_left_arm_support_subset z hz)
      hzSupport hzRim
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_classified_support,
    MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using h

/-- The left mixed source-edge support can meet the right half of the left
`K_{3,3}` rim only at the left rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_inter_right_to_left_arm_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.left_or_path.supportSet)
    (hzRim : z ∈ F.right_to_left_arm_path.support) :
    z = F.rimAttach 1 := by
  have h :=
    A.left_classified_support.inter_eq_matching_endpoint
      F.right_adj_left_arm F.right_ne_common
      {z : V | z ∈ F.right_to_left_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_left_arm_support_subset z hz)
      hzSupport hzRim
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_classified_support,
    MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using h

/-- The left mixed source-edge support meets the left rim only at the left
rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_inter_left_rim_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.left_or_path.supportSet)
    (hzRim : z ∈ (F.rim 1).support) :
    z = F.rimAttach 1 := by
  classical
  have hzCases := F.left_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact F.left_support_inter_left_to_left_arm_eq_attach hzSupport hzLeft
  · exact F.left_support_inter_right_to_left_arm_eq_attach hzSupport hzRight

/-- The left mixed source-edge support is disjoint from the left half of the
right canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_disjoint_left_to_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_path.supportSet
      {z : V | z ∈ F.left_to_right_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_classified_support] using
    A.left_classified_support.disjoint F.left_adj_right_arm
      F.left_ne_common.symm A.right_arm.other_ne.symm
      F.left_adj_left_arm.ne.symm A.right_left_other_ne.symm
      {z : V | z ∈ F.left_to_right_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_right_arm_support_subset z hz)

/-- The left mixed source-edge support is disjoint from the right half of the
right canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_disjoint_right_to_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_path.supportSet
      {z : V | z ∈ F.right_to_right_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_classified_support] using
    A.left_classified_support.disjoint F.right_adj_right_arm
      F.right_ne_common.symm A.right_arm.other_ne.symm
      F.right_adj_left_arm.ne.symm A.right_left_other_ne.symm
      {z : V | z ∈ F.right_to_right_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_right_arm_support_subset z hz)

/-- The left mixed source-edge support is disjoint from the right canonical
`K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_disjoint_right_rim
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_path.supportSet
      {z : V | z ∈ (F.rim 0).support} := by
  classical
  rw [Set.disjoint_left]
  intro z hzSupport hzRim
  have hzCases := F.right_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact Set.disjoint_left.mp F.left_support_disjoint_left_to_right_arm
      hzSupport hzLeft
  · exact Set.disjoint_left.mp F.left_support_disjoint_right_to_right_arm
      hzSupport hzRight

/-- The left mixed source-edge support is disjoint from the left half of the
side canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_disjoint_left_to_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_path.supportSet
      {z : V | z ∈ F.left_to_side_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_classified_support] using
    A.left_classified_support.disjoint F.left_adj_side_arm
      F.left_ne_common.symm A.side_arm.other_ne.symm
      F.left_adj_left_arm.ne.symm A.left_side_other_ne
      {z : V | z ∈ F.left_to_side_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_side_arm_support_subset z hz)

/-- The left mixed source-edge support is disjoint from the right half of the
side canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_disjoint_right_to_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_path.supportSet
      {z : V | z ∈ F.right_to_side_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_classified_support] using
    A.left_classified_support.disjoint F.right_adj_side_arm
      F.right_ne_common.symm A.side_arm.other_ne.symm
      F.right_adj_left_arm.ne.symm A.left_side_other_ne
      {z : V | z ∈ F.right_to_side_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_side_arm_support_subset z hz)

/-- The left mixed source-edge support is disjoint from the side canonical
`K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_disjoint_side_rim
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_path.supportSet
      {z : V | z ∈ (F.rim 2).support} := by
  classical
  rw [Set.disjoint_left]
  intro z hzSupport hzRim
  have hzCases := F.side_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact Set.disjoint_left.mp F.left_support_disjoint_left_to_side_arm
      hzSupport hzLeft
  · exact Set.disjoint_left.mp F.left_support_disjoint_right_to_side_arm
      hzSupport hzRight

/-- The side mixed source-edge support can meet the left half of the side
`K_{3,3}` rim only at the side rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_inter_left_to_side_arm_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.left_or_right.supportSet)
    (hzRim : z ∈ F.left_to_side_arm_path.support) :
    z = F.rimAttach 2 := by
  have h :=
    A.side_classified_support.inter_eq_matching_endpoint
      F.left_adj_side_arm F.left_ne_common
      {z : V | z ∈ F.left_to_side_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_side_arm_support_subset z hz)
      hzSupport hzRim
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_classified_support,
    MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using h

/-- The side mixed source-edge support can meet the right half of the side
`K_{3,3}` rim only at the side rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_inter_right_to_side_arm_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.left_or_right.supportSet)
    (hzRim : z ∈ F.right_to_side_arm_path.support) :
    z = F.rimAttach 2 := by
  have h :=
    A.side_classified_support.inter_eq_matching_endpoint
      F.right_adj_side_arm F.right_ne_common
      {z : V | z ∈ F.right_to_side_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_side_arm_support_subset z hz)
      hzSupport hzRim
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_classified_support,
    MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rimAttach]
    using h

/-- The side mixed source-edge support meets the side rim only at the side
rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_inter_side_rim_eq_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzSupport : z ∈ D.left_or_right.supportSet)
    (hzRim : z ∈ (F.rim 2).support) :
    z = F.rimAttach 2 := by
  classical
  have hzCases := F.side_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact F.side_support_inter_left_to_side_arm_eq_attach hzSupport hzLeft
  · exact F.side_support_inter_right_to_side_arm_eq_attach hzSupport hzRight

/-- The side mixed source-edge support is disjoint from the left half of the
right canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_disjoint_left_to_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_right.supportSet
      {z : V | z ∈ F.left_to_right_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_classified_support] using
    A.side_classified_support.disjoint F.left_adj_right_arm
      F.left_ne_common.symm A.right_arm.other_ne.symm
      F.left_adj_side_arm.ne.symm A.right_side_other_ne.symm
      {z : V | z ∈ F.left_to_right_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_right_arm_support_subset z hz)

/-- The side mixed source-edge support is disjoint from the right half of the
right canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_disjoint_right_to_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_right.supportSet
      {z : V | z ∈ F.right_to_right_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_classified_support] using
    A.side_classified_support.disjoint F.right_adj_right_arm
      F.right_ne_common.symm A.right_arm.other_ne.symm
      F.right_adj_side_arm.ne.symm A.right_side_other_ne.symm
      {z : V | z ∈ F.right_to_right_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_right_arm_support_subset z hz)

/-- The side mixed source-edge support is disjoint from the right canonical
`K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_disjoint_right_rim
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_right.supportSet
      {z : V | z ∈ (F.rim 0).support} := by
  classical
  rw [Set.disjoint_left]
  intro z hzSupport hzRim
  have hzCases := F.right_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact Set.disjoint_left.mp F.side_support_disjoint_left_to_right_arm
      hzSupport hzLeft
  · exact Set.disjoint_left.mp F.side_support_disjoint_right_to_right_arm
      hzSupport hzRight

/-- The side mixed source-edge support is disjoint from the left half of the
left canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_disjoint_left_to_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_right.supportSet
      {z : V | z ∈ F.left_to_left_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_classified_support] using
    A.side_classified_support.disjoint F.left_adj_left_arm
      F.left_ne_common.symm A.left_arm.other_ne.symm
      F.left_adj_side_arm.ne.symm A.left_side_other_ne.symm
      {z : V | z ∈ F.left_to_left_arm_path.support}
      (by
        intro z hz
        simpa using F.left_to_left_arm_support_subset z hz)

/-- The side mixed source-edge support is disjoint from the right half of the
left canonical `K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_disjoint_right_to_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_right.supportSet
      {z : V | z ∈ F.right_to_left_arm_path.support} := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_classified_support] using
    A.side_classified_support.disjoint F.right_adj_left_arm
      F.right_ne_common.symm A.left_arm.other_ne.symm
      F.right_adj_side_arm.ne.symm A.left_side_other_ne.symm
      {z : V | z ∈ F.right_to_left_arm_path.support}
      (by
        intro z hz
        simpa using F.right_to_left_arm_support_subset z hz)

/-- The side mixed source-edge support is disjoint from the left canonical
`K_{3,3}` rim. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_disjoint_left_rim
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint D.left_or_right.supportSet
      {z : V | z ∈ (F.rim 1).support} := by
  classical
  rw [Set.disjoint_left]
  intro z hzSupport hzRim
  have hzCases := F.left_arm_rim_support_cases (by
    simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.rim]
      using hzRim)
  rcases hzCases with hzLeft | hzRight
  · exact Set.disjoint_left.mp F.side_support_disjoint_left_to_left_arm
      hzSupport hzLeft
  · exact Set.disjoint_left.mp F.side_support_disjoint_right_to_left_arm
      hzSupport hzRight

/-- The right mixed source-edge support meets the canonical rim family only at
the right rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_support_meets_rims_only_at_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (j : Fin 3) (v : V)
    (hvSupport : v ∈ D.right_or_path.supportSet)
    (hvRim : v ∈ (F.rim j).support) :
    v = F.rimAttach 0 := by
  classical
  fin_cases j
  · exact F.right_support_inter_right_rim_eq_attach hvSupport hvRim
  · exact False.elim
      (Set.disjoint_left.mp F.right_support_disjoint_left_rim
        hvSupport hvRim)
  · exact False.elim
      (Set.disjoint_left.mp F.right_support_disjoint_side_rim
        hvSupport hvRim)

/-- The left mixed source-edge support meets the canonical rim family only at
the left rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_support_meets_rims_only_at_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (j : Fin 3) (v : V)
    (hvSupport : v ∈ D.left_or_path.supportSet)
    (hvRim : v ∈ (F.rim j).support) :
    v = F.rimAttach 1 := by
  classical
  fin_cases j
  · exact False.elim
      (Set.disjoint_left.mp F.left_support_disjoint_right_rim
        hvSupport hvRim)
  · exact F.left_support_inter_left_rim_eq_attach hvSupport hvRim
  · exact False.elim
      (Set.disjoint_left.mp F.left_support_disjoint_side_rim
        hvSupport hvRim)

/-- The side mixed source-edge support meets the canonical rim family only at
the side rim attachment. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.side_support_meets_rims_only_at_attach
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    (j : Fin 3) (v : V)
    (hvSupport : v ∈ D.left_or_right.supportSet)
    (hvRim : v ∈ (F.rim j).support) :
    v = F.rimAttach 2 := by
  classical
  fin_cases j
  · exact False.elim
      (Set.disjoint_left.mp F.side_support_disjoint_right_rim
        hvSupport hvRim)
  · exact False.elim
      (Set.disjoint_left.mp F.side_support_disjoint_left_rim
        hvSupport hvRim)
  · exact F.side_support_inter_side_rim_eq_attach hvSupport hvRim


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
