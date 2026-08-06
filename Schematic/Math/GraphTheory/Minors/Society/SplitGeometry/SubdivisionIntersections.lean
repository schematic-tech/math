import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.CommonBranchArms

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem subdivisionSubwalks_inter_eq_common_source
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {source target₁ target₂ : W}
    (h₁ : K.Adj source target₁)
    (h₂ : K.Adj source target₂)
    (htarget : target₁ ≠ target₂)
    {a₁ b₁ a₂ b₂ : V}
    (q₁ : G.Walk a₁ b₁) (q₂ : G.Walk a₂ b₂)
    (hq₁ : forall z : V, z ∈ q₁.support -> z ∈ (M.edgePath h₁).support)
    (hq₂ : forall z : V, z ∈ q₂.support -> z ∈ (M.edgePath h₂).support)
    {z : V} (hz₁ : z ∈ q₁.support) (hz₂ : z ∈ q₂.support) :
    z = M.branchVertex source := by
  have hedge_ne :
      Not ((source = source ∧ target₁ = target₂) ∨
        (source = target₂ ∧ target₁ = source)) := by
    rintro (h | h)
    · exact htarget h.2
    · exact h₂.ne h.1
  have hunique :
      forall w : W,
        (w = source ∨ w = target₁) ->
          (w = source ∨ w = target₂) ->
            w = source := by
    intro w hw₁ hw₂
    rcases hw₁ with rfl | rfl
    · rfl
    · rcases hw₂ with h | h
      · exact False.elim (h₁.ne h.symm)
      · exact False.elim (htarget h)
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      h₁ h₂ hedge_ne hunique (hq₁ z hz₁) (hq₂ z hz₂)

theorem subdivisionSubwalks_inter_eq_common_target
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {source₁ source₂ target : W}
    (h₁ : K.Adj source₁ target)
    (h₂ : K.Adj source₂ target)
    (hsource : source₁ ≠ source₂)
    {a₁ b₁ a₂ b₂ : V}
    (q₁ : G.Walk a₁ b₁) (q₂ : G.Walk a₂ b₂)
    (hq₁ : forall z : V, z ∈ q₁.support -> z ∈ (M.edgePath h₁).support)
    (hq₂ : forall z : V, z ∈ q₂.support -> z ∈ (M.edgePath h₂).support)
    {z : V} (hz₁ : z ∈ q₁.support) (hz₂ : z ∈ q₂.support) :
    z = M.branchVertex target := by
  have hedge_ne :
      Not ((source₁ = source₂ ∧ target = target) ∨
        (source₁ = target ∧ target = source₂)) := by
    rintro (h | h)
    · exact hsource h.1
    · exact h₁.ne h.1
  have hunique :
      forall w : W,
        (w = source₁ ∨ w = target) ->
          (w = source₂ ∨ w = target) ->
            w = target := by
    intro w hw₁ hw₂
    rcases hw₁ with rfl | rfl
    · rcases hw₂ with h | h
      · exact False.elim (hsource h)
      · exact h
    · rfl
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      h₁ h₂ hedge_ne hunique (hq₁ z hz₁) (hq₂ z hz₂)

theorem subdivisionSubwalks_inter_eq_classified_source_endpoint
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {common other directOther source₁ source₂ : W}
    (hdirect : K.Adj common directOther)
    (hdirectOther_ne_other : directOther ≠ other)
    (hsource : K.Adj source₁ source₂)
    (hsource_endpoints :
      forall w : W,
        (w = source₁ ∨ w = source₂) -> w = common ∨ w = other)
    {a₁ b₁ a₂ b₂ : V}
    (qdirect : G.Walk a₁ b₁) (qsource : G.Walk a₂ b₂)
    (hqdirect :
      forall z : V, z ∈ qdirect.support ->
        z ∈ (M.edgePath hdirect).support)
    (hqsource :
      forall z : V, z ∈ qsource.support ->
        z ∈ (M.edgePath hsource).support)
    {z : V} (hzdirect : z ∈ qdirect.support)
    (hzsource : z ∈ qsource.support) :
    z = M.branchVertex common := by
  have hdirectOther_not_source :
      directOther ≠ source₁ ∧ directOther ≠ source₂ := by
    constructor <;> intro h
    · rcases hsource_endpoints directOther (Or.inl h) with hc | ho
      · exact hdirect.ne hc.symm
      · exact hdirectOther_ne_other ho
    · rcases hsource_endpoints directOther (Or.inr h) with hc | ho
      · exact hdirect.ne hc.symm
      · exact hdirectOther_ne_other ho
  have hedge_ne :
      Not ((common = source₁ ∧ directOther = source₂) ∨
        (common = source₂ ∧ directOther = source₁)) := by
    rintro (h | h)
    · exact hdirectOther_not_source.2 h.2
    · exact hdirectOther_not_source.1 h.2
  have hunique :
      forall w : W,
        (w = common ∨ w = directOther) ->
          (w = source₁ ∨ w = source₂) ->
            w = common := by
    intro w hwDirect hwSource
    rcases hwDirect with hc | hd
    · exact hc
    · rcases hsource_endpoints w hwSource with hc | ho
      · exact hc
      · exact False.elim (hdirectOther_ne_other (hd.symm.trans ho))
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      hdirect hsource hedge_ne hunique
      (hqdirect z hzdirect) (hqsource z hzsource)

theorem subdivisionSupportSets_disjoint
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {x y x' y' : W}
    (hxy : K.Adj x y) (hx'y' : K.Adj x' y')
    (hxx' : x ≠ x') (hxy' : x ≠ y')
    (hyx' : y ≠ x') (hyy' : y ≠ y')
    (firstSet secondSet : Set V)
    (hfirst_subset :
      firstSet ⊆ {z : V | z ∈ (M.edgePath hxy).support})
    (hsecond_subset :
      secondSet ⊆ {z : V | z ∈ (M.edgePath hx'y').support}) :
    Disjoint firstSet secondSet :=
  (M.edgePath_support_disjoint_of_no_common_endpoint
    hxy hx'y' hxx' hxy' hyx' hyy').mono hfirst_subset hsecond_subset

theorem subdivisionSupportSets_disjoint_of_classified_endpoints
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {common other source₁ source₂ rim₁ rim₂ : W}
    (hsource : K.Adj source₁ source₂)
    (hrim : K.Adj rim₁ rim₂)
    (hsource_endpoints :
      forall w : W,
        (w = source₁ ∨ w = source₂) -> w = common ∨ w = other)
    (hcommon_ne_rim₁ : common ≠ rim₁)
    (hcommon_ne_rim₂ : common ≠ rim₂)
    (hother_ne_rim₁ : other ≠ rim₁)
    (hother_ne_rim₂ : other ≠ rim₂)
    (sourceSet rimSet : Set V)
    (hsource_subset :
      sourceSet ⊆ {z : V | z ∈ (M.edgePath hsource).support})
    (hrim_subset :
      rimSet ⊆ {z : V | z ∈ (M.edgePath hrim).support}) :
    Disjoint sourceSet rimSet := by
  have hendpoint_ne (rim : W) (hcommon : common ≠ rim)
      (hother : other ≠ rim) :
      forall w : W, (w = source₁ ∨ w = source₂) -> w ≠ rim := by
    intro w hw hwrim
    rcases hsource_endpoints w hw with hwcommon | hwother
    · exact hcommon (hwcommon.symm.trans hwrim)
    · exact hother (hwother.symm.trans hwrim)
  exact
    subdivisionSupportSets_disjoint M hsource hrim
      (hendpoint_ne rim₁ hcommon_ne_rim₁ hother_ne_rim₁ source₁ (Or.inl rfl))
      (hendpoint_ne rim₂ hcommon_ne_rim₂ hother_ne_rim₂ source₁ (Or.inl rfl))
      (hendpoint_ne rim₁ hcommon_ne_rim₁ hother_ne_rim₁ source₂ (Or.inr rfl))
      (hendpoint_ne rim₂ hcommon_ne_rim₂ hother_ne_rim₂ source₂ (Or.inr rfl))
      sourceSet rimSet hsource_subset hrim_subset

theorem subdivisionSupportSets_inter_eq_classified_matching_endpoint
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {common other source₁ source₂ rimOther : W}
    (hsource : K.Adj source₁ source₂)
    (hrim : K.Adj rimOther other)
    (hsource_endpoints :
      forall w : W,
        (w = source₁ ∨ w = source₂) -> w = common ∨ w = other)
    (hrimOther_ne_common : rimOther ≠ common)
    (sourceSet rimSet : Set V)
    (hsource_subset :
      sourceSet ⊆ {z : V | z ∈ (M.edgePath hsource).support})
    (hrim_subset :
      rimSet ⊆ {z : V | z ∈ (M.edgePath hrim).support})
    {z : V} (hzsource : z ∈ sourceSet) (hzrim : z ∈ rimSet) :
    z = M.branchVertex other := by
  have hrimOther_not_source :
      rimOther ≠ source₁ ∧ rimOther ≠ source₂ := by
    constructor <;> intro h
    · rcases hsource_endpoints rimOther (Or.inl h) with hc | ho
      · exact hrimOther_ne_common hc
      · exact hrim.ne ho
    · rcases hsource_endpoints rimOther (Or.inr h) with hc | ho
      · exact hrimOther_ne_common hc
      · exact hrim.ne ho
  have hedge_ne :
      Not ((source₁ = rimOther ∧ source₂ = other) ∨
        (source₁ = other ∧ source₂ = rimOther)) := by
    rintro (h | h)
    · exact hrimOther_not_source.1 h.1.symm
    · exact hrimOther_not_source.2 h.2.symm
  have hunique :
      forall w : W,
        (w = source₁ ∨ w = source₂) ->
          (w = rimOther ∨ w = other) -> w = other := by
    intro w hwSource hwRim
    rcases hsource_endpoints w hwSource with hc | ho
    · rcases hwRim with hr | ho
      · exact False.elim (hrimOther_ne_common (hr.symm.trans hc))
      · exact ho
    · exact ho
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      hsource hrim hedge_ne hunique
      (hsource_subset hzsource) (hrim_subset hzrim)

/-- A localized subdivision-edge support whose two source endpoints have been
classified as a distinguished common endpoint and one other endpoint. -/
structure ClassifiedSubdivisionEdgeSupport
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G) (common other : W) where
  source₁ : W
  source₂ : W
  adj : K.Adj source₁ source₂
  endpoints :
    forall w : W,
      (w = source₁ ∨ w = source₂) -> w = common ∨ w = other
  support : Set V
  support_subset :
    support ⊆ {z : V | z ∈ (M.edgePath adj).support}

theorem ClassifiedSubdivisionEdgeSupport.inter_eq_matching_endpoint
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K G} {common other : W}
    (E : ClassifiedSubdivisionEdgeSupport M common other)
    {rimOther : W} (hrim : K.Adj rimOther other)
    (hrimOther_ne_common : rimOther ≠ common)
    (rimSet : Set V)
    (hrim_subset :
      rimSet ⊆ {z : V | z ∈ (M.edgePath hrim).support})
    {z : V} (hzsource : z ∈ E.support) (hzrim : z ∈ rimSet) :
    z = M.branchVertex other := by
  exact
    subdivisionSupportSets_inter_eq_classified_matching_endpoint M
      E.adj hrim E.endpoints hrimOther_ne_common E.support rimSet
      E.support_subset hrim_subset hzsource hzrim

theorem ClassifiedSubdivisionEdgeSupport.disjoint
    {W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K G} {common other : W}
    (E : ClassifiedSubdivisionEdgeSupport M common other)
    {rim₁ rim₂ : W} (hrim : K.Adj rim₁ rim₂)
    (hcommon_ne_rim₁ : common ≠ rim₁)
    (hcommon_ne_rim₂ : common ≠ rim₂)
    (hother_ne_rim₁ : other ≠ rim₁)
    (hother_ne_rim₂ : other ≠ rim₂)
    (rimSet : Set V)
    (hrim_subset :
      rimSet ⊆ {z : V | z ∈ (M.edgePath hrim).support}) :
    Disjoint E.support rimSet := by
  exact
    subdivisionSupportSets_disjoint_of_classified_endpoints M
      E.adj hrim E.endpoints hcommon_ne_rim₁ hcommon_ne_rim₂
      hother_ne_rim₁ hother_ne_rim₂ E.support rimSet
      E.support_subset hrim_subset

theorem walkInternalVertices_disjoint_of_support_inter_eq_endpoint
    {G : SimpleGraph V} {a b c d endpoint : V}
    (first : G.Walk a b) (second : G.Walk c d)
    (hendpoint : endpoint = a ∨ endpoint = b)
    (hinter :
      forall z : V,
        z ∈ first.support -> z ∈ second.support -> z = endpoint) :
    Disjoint (Walk.InternalVertices first) (Walk.InternalVertices second) := by
  rw [Set.disjoint_left]
  intro z hzFirst hzSecond
  have hzEndpoint := hinter z hzFirst.1 hzSecond.1
  rcases hendpoint with rfl | rfl
  · exact hzFirst.2.1 hzEndpoint
  · exact hzFirst.2.2 hzEndpoint

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_right_arm_inter_right_right_arm_eq_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzLeft : z ∈ F.left_to_right_arm_path.support)
    (hzRight : z ∈ F.right_to_right_arm_path.support) :
    z = (Classical.choice hK33).branchVertex A.right_arm.other := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK33)
      F.left_adj_right_arm F.right_adj_right_arm F.left_ne_right
      F.left_to_right_arm_path F.right_to_right_arm_path
      F.left_to_right_arm_support_subset F.right_to_right_arm_support_subset
      hzLeft hzRight

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_left_arm_inter_right_left_arm_eq_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzLeft : z ∈ F.left_to_left_arm_path.support)
    (hzRight : z ∈ F.right_to_left_arm_path.support) :
    z = (Classical.choice hK33).branchVertex A.left_arm.other := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK33)
      F.left_adj_left_arm F.right_adj_left_arm F.left_ne_right
      F.left_to_left_arm_path F.right_to_left_arm_path
      F.left_to_left_arm_support_subset F.right_to_left_arm_support_subset
      hzLeft hzRight

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_side_arm_inter_right_side_arm_eq_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzLeft : z ∈ F.left_to_side_arm_path.support)
    (hzRight : z ∈ F.right_to_side_arm_path.support) :
    z = (Classical.choice hK33).branchVertex A.side_arm.other := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK33)
      F.left_adj_side_arm F.right_adj_side_arm F.left_ne_right
      F.left_to_side_arm_path F.right_to_side_arm_path
      F.left_to_side_arm_support_subset F.right_to_side_arm_support_subset
      hzLeft hzRight

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_right_arm_inter_left_left_arm_eq_leftSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzRightArm : z ∈ F.left_to_right_arm_path.support)
    (hzLeftArm : z ∈ F.left_to_left_arm_path.support) :
    z = (Classical.choice hK33).branchVertex F.leftSource := by
  exact
    subdivisionSubwalks_inter_eq_common_source (Classical.choice hK33)
      F.left_adj_right_arm F.left_adj_left_arm A.right_left_other_ne
      F.left_to_right_arm_path F.left_to_left_arm_path
      F.left_to_right_arm_support_subset F.left_to_left_arm_support_subset
      hzRightArm hzLeftArm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_right_arm_inter_left_side_arm_eq_leftSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzRightArm : z ∈ F.left_to_right_arm_path.support)
    (hzSideArm : z ∈ F.left_to_side_arm_path.support) :
    z = (Classical.choice hK33).branchVertex F.leftSource := by
  exact
    subdivisionSubwalks_inter_eq_common_source (Classical.choice hK33)
      F.left_adj_right_arm F.left_adj_side_arm A.right_side_other_ne
      F.left_to_right_arm_path F.left_to_side_arm_path
      F.left_to_right_arm_support_subset F.left_to_side_arm_support_subset
      hzRightArm hzSideArm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_left_arm_inter_left_side_arm_eq_leftSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzLeftArm : z ∈ F.left_to_left_arm_path.support)
    (hzSideArm : z ∈ F.left_to_side_arm_path.support) :
    z = (Classical.choice hK33).branchVertex F.leftSource := by
  exact
    subdivisionSubwalks_inter_eq_common_source (Classical.choice hK33)
      F.left_adj_left_arm F.left_adj_side_arm A.left_side_other_ne
      F.left_to_left_arm_path F.left_to_side_arm_path
      F.left_to_left_arm_support_subset F.left_to_side_arm_support_subset
      hzLeftArm hzSideArm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_right_arm_inter_right_left_arm_eq_rightSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzRightArm : z ∈ F.right_to_right_arm_path.support)
    (hzLeftArm : z ∈ F.right_to_left_arm_path.support) :
    z = (Classical.choice hK33).branchVertex F.rightSource := by
  exact
    subdivisionSubwalks_inter_eq_common_source (Classical.choice hK33)
      F.right_adj_right_arm F.right_adj_left_arm A.right_left_other_ne
      F.right_to_right_arm_path F.right_to_left_arm_path
      F.right_to_right_arm_support_subset F.right_to_left_arm_support_subset
      hzRightArm hzLeftArm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_right_arm_inter_right_side_arm_eq_rightSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzRightArm : z ∈ F.right_to_right_arm_path.support)
    (hzSideArm : z ∈ F.right_to_side_arm_path.support) :
    z = (Classical.choice hK33).branchVertex F.rightSource := by
  exact
    subdivisionSubwalks_inter_eq_common_source (Classical.choice hK33)
      F.right_adj_right_arm F.right_adj_side_arm A.right_side_other_ne
      F.right_to_right_arm_path F.right_to_side_arm_path
      F.right_to_right_arm_support_subset F.right_to_side_arm_support_subset
      hzRightArm hzSideArm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_left_arm_inter_right_side_arm_eq_rightSource
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths)
    {z : V}
    (hzLeftArm : z ∈ F.right_to_left_arm_path.support)
    (hzSideArm : z ∈ F.right_to_side_arm_path.support) :
    z = (Classical.choice hK33).branchVertex F.rightSource := by
  exact
    subdivisionSubwalks_inter_eq_common_source (Classical.choice hK33)
      F.right_adj_left_arm F.right_adj_side_arm A.left_side_other_ne
      F.right_to_left_arm_path F.right_to_side_arm_path
      F.right_to_left_arm_support_subset F.right_to_side_arm_support_subset
      hzLeftArm hzSideArm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_right_arm_internals_disjoint_right_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_to_right_arm_path)
      (Walk.InternalVertices F.right_to_right_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.left_to_right_arm_path F.right_to_right_arm_path (Or.inr rfl)
      (fun z => F.left_right_arm_inter_right_right_arm_eq_right_arm)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_left_arm_internals_disjoint_right_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_to_left_arm_path)
      (Walk.InternalVertices F.right_to_left_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.left_to_left_arm_path F.right_to_left_arm_path (Or.inr rfl)
      (fun z => F.left_left_arm_inter_right_left_arm_eq_left_arm)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_side_arm_internals_disjoint_right_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_to_side_arm_path)
      (Walk.InternalVertices F.right_to_side_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.left_to_side_arm_path F.right_to_side_arm_path (Or.inr rfl)
      (fun z => F.left_side_arm_inter_right_side_arm_eq_side_arm)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_right_arm_internals_disjoint_left_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_to_right_arm_path)
      (Walk.InternalVertices F.left_to_left_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.left_to_right_arm_path F.left_to_left_arm_path (Or.inl rfl)
      (fun z => F.left_right_arm_inter_left_left_arm_eq_leftSource)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_right_arm_internals_disjoint_left_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_to_right_arm_path)
      (Walk.InternalVertices F.left_to_side_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.left_to_right_arm_path F.left_to_side_arm_path (Or.inl rfl)
      (fun z => F.left_right_arm_inter_left_side_arm_eq_leftSource)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_left_arm_internals_disjoint_left_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_to_left_arm_path)
      (Walk.InternalVertices F.left_to_side_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.left_to_left_arm_path F.left_to_side_arm_path (Or.inl rfl)
      (fun z => F.left_left_arm_inter_left_side_arm_eq_leftSource)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_right_arm_internals_disjoint_right_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.right_to_right_arm_path)
      (Walk.InternalVertices F.right_to_left_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.right_to_right_arm_path F.right_to_left_arm_path (Or.inl rfl)
      (fun z => F.right_right_arm_inter_right_left_arm_eq_rightSource)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_right_arm_internals_disjoint_right_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.right_to_right_arm_path)
      (Walk.InternalVertices F.right_to_side_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.right_to_right_arm_path F.right_to_side_arm_path (Or.inl rfl)
      (fun z => F.right_right_arm_inter_right_side_arm_eq_rightSource)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.right_left_arm_internals_disjoint_right_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.right_to_left_arm_path)
      (Walk.InternalVertices F.right_to_side_arm_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.right_to_left_arm_path F.right_to_side_arm_path (Or.inl rfl)
      (fun z => F.right_left_arm_inter_right_side_arm_eq_rightSource)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_right_arm_support_disjoint_right_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint {z : V | z ∈ F.left_to_right_arm_path.support}
      {z : V | z ∈ F.right_to_left_arm_path.support} := by
  classical
  let M := Classical.choice hK33
  exact
    subdivisionSupportSets_disjoint M
      F.left_adj_right_arm F.right_adj_left_arm
      F.left_ne_right F.left_adj_left_arm.ne
      (fun h => F.right_adj_right_arm.ne h.symm)
      A.right_left_other_ne
      {z : V | z ∈ F.left_to_right_arm_path.support}
      {z : V | z ∈ F.right_to_left_arm_path.support}
      F.left_to_right_arm_support_subset F.right_to_left_arm_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_right_arm_support_disjoint_right_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint {z : V | z ∈ F.left_to_right_arm_path.support}
      {z : V | z ∈ F.right_to_side_arm_path.support} := by
  classical
  let M := Classical.choice hK33
  exact
    subdivisionSupportSets_disjoint M
      F.left_adj_right_arm F.right_adj_side_arm
      F.left_ne_right F.left_adj_side_arm.ne
      (fun h => F.right_adj_right_arm.ne h.symm)
      A.right_side_other_ne
      {z : V | z ∈ F.left_to_right_arm_path.support}
      {z : V | z ∈ F.right_to_side_arm_path.support}
      F.left_to_right_arm_support_subset F.right_to_side_arm_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_left_arm_support_disjoint_right_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint {z : V | z ∈ F.left_to_left_arm_path.support}
      {z : V | z ∈ F.right_to_right_arm_path.support} := by
  classical
  let M := Classical.choice hK33
  exact
    subdivisionSupportSets_disjoint M
      F.left_adj_left_arm F.right_adj_right_arm
      F.left_ne_right F.left_adj_right_arm.ne
      (fun h => F.right_adj_left_arm.ne h.symm)
      (fun h => A.right_left_other_ne h.symm)
      {z : V | z ∈ F.left_to_left_arm_path.support}
      {z : V | z ∈ F.right_to_right_arm_path.support}
      F.left_to_left_arm_support_subset F.right_to_right_arm_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_left_arm_support_disjoint_right_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint {z : V | z ∈ F.left_to_left_arm_path.support}
      {z : V | z ∈ F.right_to_side_arm_path.support} := by
  classical
  let M := Classical.choice hK33
  exact
    subdivisionSupportSets_disjoint M
      F.left_adj_left_arm F.right_adj_side_arm
      F.left_ne_right F.left_adj_side_arm.ne
      (fun h => F.right_adj_left_arm.ne h.symm)
      A.left_side_other_ne
      {z : V | z ∈ F.left_to_left_arm_path.support}
      {z : V | z ∈ F.right_to_side_arm_path.support}
      F.left_to_left_arm_support_subset F.right_to_side_arm_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_side_arm_support_disjoint_right_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint {z : V | z ∈ F.left_to_side_arm_path.support}
      {z : V | z ∈ F.right_to_right_arm_path.support} := by
  classical
  let M := Classical.choice hK33
  exact
    subdivisionSupportSets_disjoint M
      F.left_adj_side_arm F.right_adj_right_arm
      F.left_ne_right F.left_adj_right_arm.ne
      (fun h => F.right_adj_side_arm.ne h.symm)
      (fun h => A.right_side_other_ne h.symm)
      {z : V | z ∈ F.left_to_side_arm_path.support}
      {z : V | z ∈ F.right_to_right_arm_path.support}
      F.left_to_side_arm_support_subset F.right_to_right_arm_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K33RimSourceEdgePaths.left_side_arm_support_disjoint_right_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33}
    {C : D.CommonSupportEndpointPaths} {c : K33Vertex}
    {A : C.CommonBranchArmPaths c}
    (F : A.K33RimSourceEdgePaths) :
    Disjoint {z : V | z ∈ F.left_to_side_arm_path.support}
      {z : V | z ∈ F.right_to_left_arm_path.support} := by
  classical
  let M := Classical.choice hK33
  exact
    subdivisionSupportSets_disjoint M
      F.left_adj_side_arm F.right_adj_left_arm
      F.left_ne_right F.left_adj_left_arm.ne
      (fun h => F.right_adj_side_arm.ne h.symm)
      (fun h => A.left_side_other_ne h.symm)
      {z : V | z ∈ F.left_to_side_arm_path.support}
      {z : V | z ∈ F.right_to_left_arm_path.support}
      F.left_to_side_arm_support_subset F.right_to_left_arm_support_subset


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
