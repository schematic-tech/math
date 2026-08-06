import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.K33SupportContacts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5_exists_fourth_source
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    (A : C.CommonBranchArmPaths c) :
    Exists fun d : Fin 5 =>
      d ≠ c ∧ d ≠ A.right_arm.other ∧
        d ≠ A.left_arm.other ∧ d ≠ A.side_arm.other := by
  exact
    K5Graph.exists_vertex_not_four
      c A.right_arm.other A.left_arm.other A.side_arm.other

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5_fourth_adj_common
    {c d : Fin 5}
    (hdc : d ≠ c) :
    K5Graph.Adj c d :=
  K5Graph.adj_of_ne hdc.symm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5_fourth_adj_right_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c d : Fin 5}
    (A : C.CommonBranchArmPaths c)
    (hdr : d ≠ A.right_arm.other) :
    K5Graph.Adj A.right_arm.other d :=
  K5Graph.adj_of_ne hdr.symm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5_fourth_adj_left_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c d : Fin 5}
    (A : C.CommonBranchArmPaths c)
    (hdl : d ≠ A.left_arm.other) :
    K5Graph.Adj A.left_arm.other d :=
  K5Graph.adj_of_ne hdl.symm

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5_fourth_adj_side_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c d : Fin 5}
    (A : C.CommonBranchArmPaths c)
    (hds : d ≠ A.side_arm.other) :
    K5Graph.Adj A.side_arm.other d :=
  K5Graph.adj_of_ne hds.symm

structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    (A : C.CommonBranchArmPaths c) : Type _ where
  d : Fin 5
  d_ne_common : d ≠ c
  d_ne_right : d ≠ A.right_arm.other
  d_ne_left : d ≠ A.left_arm.other
  d_ne_side : d ≠ A.side_arm.other
  common_path :
    S.graph.Walk
      ((Classical.choice hK5).branchVertex c)
      ((Classical.choice hK5).branchVertex d)
  common_isPath : common_path.IsPath
  common_support_subset :
    forall w : V, w ∈ common_path.support ->
      w ∈ ((Classical.choice hK5).edgePath
        (K5Graph.adj_of_ne d_ne_common.symm)).support
  right_path :
    S.graph.Walk
      ((Classical.choice hK5).branchVertex A.right_arm.other)
      ((Classical.choice hK5).branchVertex d)
  right_isPath : right_path.IsPath
  right_support_subset :
    forall w : V, w ∈ right_path.support ->
      w ∈ ((Classical.choice hK5).edgePath
        (K5Graph.adj_of_ne d_ne_right.symm)).support
  left_path :
    S.graph.Walk
      ((Classical.choice hK5).branchVertex A.left_arm.other)
      ((Classical.choice hK5).branchVertex d)
  left_isPath : left_path.IsPath
  left_support_subset :
    forall w : V, w ∈ left_path.support ->
      w ∈ ((Classical.choice hK5).edgePath
        (K5Graph.adj_of_ne d_ne_left.symm)).support
  side_path :
    S.graph.Walk
      ((Classical.choice hK5).branchVertex A.side_arm.other)
      ((Classical.choice hK5).branchVertex d)
  side_isPath : side_path.IsPath
  side_support_subset :
    forall w : V, w ∈ side_path.support ->
      w ∈ ((Classical.choice hK5).edgePath
        (K5Graph.adj_of_ne d_ne_side.symm)).support

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5_fourthSourceEdgePaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    (A : C.CommonBranchArmPaths c) :
    A.K5FourthSourceEdgePaths := by
  classical
  let d : Fin 5 := Classical.choose A.K5_exists_fourth_source
  have hd := Classical.choose_spec A.K5_exists_fourth_source
  have hdc : d ≠ c := hd.1
  have hdr : d ≠ A.right_arm.other := hd.2.1
  have hdl : d ≠ A.left_arm.other := hd.2.2.1
  have hds : d ≠ A.side_arm.other := hd.2.2.2
  exact {
    d := d
    d_ne_common := hdc
    d_ne_right := hdr
    d_ne_left := hdl
    d_ne_side := hds
    common_path :=
      (Classical.choice hK5).edgePath (K5Graph.adj_of_ne hdc.symm)
    common_isPath :=
      (Classical.choice hK5).edgePath_isPath (K5Graph.adj_of_ne hdc.symm)
    common_support_subset := by
      intro w hw
      simpa using hw
    right_path :=
      (Classical.choice hK5).edgePath (K5Graph.adj_of_ne hdr.symm)
    right_isPath :=
      (Classical.choice hK5).edgePath_isPath (K5Graph.adj_of_ne hdr.symm)
    right_support_subset := by
      intro w hw
      simpa using hw
    left_path :=
      (Classical.choice hK5).edgePath (K5Graph.adj_of_ne hdl.symm)
    left_isPath :=
      (Classical.choice hK5).edgePath_isPath (K5Graph.adj_of_ne hdl.symm)
    left_support_subset := by
      intro w hw
      simpa using hw
    side_path :=
      (Classical.choice hK5).edgePath (K5Graph.adj_of_ne hds.symm)
    side_isPath :=
      (Classical.choice hK5).edgePath_isPath (K5Graph.adj_of_ne hds.symm)
    side_support_subset := by
      intro w hw
      simpa using hw
  }

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.d_branchVertex_ne_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    (Classical.choice hK5).branchVertex F.d ≠
      (Classical.choice hK5).branchVertex c := by
  intro h
  exact F.d_ne_common ((Classical.choice hK5).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.d_branchVertex_ne_right
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    (Classical.choice hK5).branchVertex F.d ≠
      (Classical.choice hK5).branchVertex A.right_arm.other := by
  intro h
  exact F.d_ne_right ((Classical.choice hK5).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.d_branchVertex_ne_left
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    (Classical.choice hK5).branchVertex F.d ≠
      (Classical.choice hK5).branchVertex A.left_arm.other := by
  intro h
  exact F.d_ne_left ((Classical.choice hK5).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.d_branchVertex_ne_side
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    (Classical.choice hK5).branchVertex F.d ≠
      (Classical.choice hK5).branchVertex A.side_arm.other := by
  intro h
  exact F.d_ne_side ((Classical.choice hK5).branchVertex_injective h)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_inter_right_arm_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzF : z ∈ F.common_path.support)
    (hzA : z ∈ A.right_arm.path.support) :
    z = (Classical.choice hK5).branchVertex c := by
  exact
    subdivisionSubwalks_inter_eq_classified_source_endpoint
      (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_common.symm) F.d_ne_right
      D.right_or_path.hxy
      (fun w hw =>
        A.right_source_endpoint_eq_common_or_other (w := w) hw)
      F.common_path A.right_arm.path F.common_support_subset
      (by
        intro w hw
        simpa [GMIX24Split.TaggedSupportWitnessData.supportSet] using
          A.right_arm.support_subset w hw)
      hzF hzA

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_inter_left_arm_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzF : z ∈ F.common_path.support)
    (hzA : z ∈ A.left_arm.path.support) :
    z = (Classical.choice hK5).branchVertex c := by
  exact
    subdivisionSubwalks_inter_eq_classified_source_endpoint
      (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_common.symm) F.d_ne_left
      D.left_or_path.hxy
      (fun w hw =>
        A.left_source_endpoint_eq_common_or_other (w := w) hw)
      F.common_path A.left_arm.path F.common_support_subset
      (by
        intro w hw
        simpa [GMIX24Split.TaggedSupportWitnessData.supportSet] using
          A.left_arm.support_subset w hw)
      hzF hzA

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_inter_side_arm_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzF : z ∈ F.common_path.support)
    (hzA : z ∈ A.side_arm.path.support) :
    z = (Classical.choice hK5).branchVertex c := by
  exact
    subdivisionSubwalks_inter_eq_classified_source_endpoint
      (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_common.symm) F.d_ne_side
      D.left_or_right.hxy
      (fun w hw =>
        A.side_source_endpoint_eq_common_or_other (w := w) hw)
      F.common_path A.side_arm.path F.common_support_subset
      (by
        intro w hw
        simpa [GMIX24Split.TaggedSupportWitnessData.supportSet] using
          A.side_arm.support_subset w hw)
      hzF hzA

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.right_path_inter_right_arm_eq_right_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzF : z ∈ F.right_path.support)
    (hzA : z ∈ A.right_arm.path.support) :
    z = (Classical.choice hK5).branchVertex A.right_arm.other := by
  exact
    subdivisionSubwalks_inter_eq_classified_source_endpoint
      (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_right.symm) F.d_ne_common
      D.right_or_path.hxy
      (fun w hw =>
        (A.right_source_endpoint_eq_common_or_other (w := w) hw).symm)
      F.right_path A.right_arm.path F.right_support_subset
      (by
        intro w hw
        simpa [GMIX24Split.TaggedSupportWitnessData.supportSet] using
          A.right_arm.support_subset w hw)
      hzF hzA

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.left_path_inter_left_arm_eq_left_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzF : z ∈ F.left_path.support)
    (hzA : z ∈ A.left_arm.path.support) :
    z = (Classical.choice hK5).branchVertex A.left_arm.other := by
  exact
    subdivisionSubwalks_inter_eq_classified_source_endpoint
      (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_left.symm) F.d_ne_common
      D.left_or_path.hxy
      (fun w hw =>
        (A.left_source_endpoint_eq_common_or_other (w := w) hw).symm)
      F.left_path A.left_arm.path F.left_support_subset
      (by
        intro w hw
        simpa [GMIX24Split.TaggedSupportWitnessData.supportSet] using
          A.left_arm.support_subset w hw)
      hzF hzA

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.side_path_inter_side_arm_eq_side_other
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzF : z ∈ F.side_path.support)
    (hzA : z ∈ A.side_arm.path.support) :
    z = (Classical.choice hK5).branchVertex A.side_arm.other := by
  exact
    subdivisionSubwalks_inter_eq_classified_source_endpoint
      (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_side.symm) F.d_ne_common
      D.left_or_right.hxy
      (fun w hw =>
        (A.side_source_endpoint_eq_common_or_other (w := w) hw).symm)
      F.side_path A.side_arm.path F.side_support_subset
      (by
        intro w hw
        simpa [GMIX24Split.TaggedSupportWitnessData.supportSet] using
          A.side_arm.support_subset w hw)
      hzF hzA

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_inter_right_path_eq_fourth
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzCommon : z ∈ F.common_path.support)
    (hzRight : z ∈ F.right_path.support) :
    z = (Classical.choice hK5).branchVertex F.d := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_common.symm) (K5Graph.adj_of_ne F.d_ne_right.symm) A.right_arm.other_ne.symm
      F.common_path F.right_path F.common_support_subset F.right_support_subset
      hzCommon hzRight

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_inter_left_path_eq_fourth
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzCommon : z ∈ F.common_path.support)
    (hzLeft : z ∈ F.left_path.support) :
    z = (Classical.choice hK5).branchVertex F.d := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_common.symm) (K5Graph.adj_of_ne F.d_ne_left.symm) A.left_arm.other_ne.symm
      F.common_path F.left_path F.common_support_subset F.left_support_subset
      hzCommon hzLeft

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_inter_side_path_eq_fourth
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzCommon : z ∈ F.common_path.support)
    (hzSide : z ∈ F.side_path.support) :
    z = (Classical.choice hK5).branchVertex F.d := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_common.symm) (K5Graph.adj_of_ne F.d_ne_side.symm) A.side_arm.other_ne.symm
      F.common_path F.side_path F.common_support_subset F.side_support_subset
      hzCommon hzSide

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.right_path_inter_left_path_eq_fourth
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzRight : z ∈ F.right_path.support)
    (hzLeft : z ∈ F.left_path.support) :
    z = (Classical.choice hK5).branchVertex F.d := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_right.symm) (K5Graph.adj_of_ne F.d_ne_left.symm) A.right_left_other_ne
      F.right_path F.left_path F.right_support_subset F.left_support_subset
      hzRight hzLeft

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.right_path_inter_side_path_eq_fourth
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzRight : z ∈ F.right_path.support)
    (hzSide : z ∈ F.side_path.support) :
    z = (Classical.choice hK5).branchVertex F.d := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_right.symm) (K5Graph.adj_of_ne F.d_ne_side.symm) A.right_side_other_ne
      F.right_path F.side_path F.right_support_subset F.side_support_subset
      hzRight hzSide

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.left_path_inter_side_path_eq_fourth
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths)
    {z : V}
    (hzLeft : z ∈ F.left_path.support)
    (hzSide : z ∈ F.side_path.support) :
    z = (Classical.choice hK5).branchVertex F.d := by
  exact
    subdivisionSubwalks_inter_eq_common_target (Classical.choice hK5)
      (K5Graph.adj_of_ne F.d_ne_left.symm) (K5Graph.adj_of_ne F.d_ne_side.symm) A.left_side_other_ne
      F.left_path F.side_path F.left_support_subset F.side_support_subset
      hzLeft hzSide

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_internals_disjoint_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.common_path)
      (Walk.InternalVertices A.right_arm.path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.common_path A.right_arm.path (Or.inl rfl)
      (fun z => F.common_path_inter_right_arm_eq_common)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_internals_disjoint_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.common_path)
      (Walk.InternalVertices A.left_arm.path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.common_path A.left_arm.path (Or.inl rfl)
      (fun z => F.common_path_inter_left_arm_eq_common)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_internals_disjoint_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.common_path)
      (Walk.InternalVertices A.side_arm.path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.common_path A.side_arm.path (Or.inl rfl)
      (fun z => F.common_path_inter_side_arm_eq_common)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.right_path_internals_disjoint_right_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.right_path)
      (Walk.InternalVertices A.right_arm.path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.right_path A.right_arm.path (Or.inl rfl)
      (fun z => F.right_path_inter_right_arm_eq_right_other)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.left_path_internals_disjoint_left_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_path)
      (Walk.InternalVertices A.left_arm.path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.left_path A.left_arm.path (Or.inl rfl)
      (fun z => F.left_path_inter_left_arm_eq_left_other)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.side_path_internals_disjoint_side_arm
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.side_path)
      (Walk.InternalVertices A.side_arm.path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.side_path A.side_arm.path (Or.inl rfl)
      (fun z => F.side_path_inter_side_arm_eq_side_other)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_internals_disjoint_right_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.common_path)
      (Walk.InternalVertices F.right_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.common_path F.right_path (Or.inr rfl)
      (fun z => F.common_path_inter_right_path_eq_fourth)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_internals_disjoint_left_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.common_path)
      (Walk.InternalVertices F.left_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.common_path F.left_path (Or.inr rfl)
      (fun z => F.common_path_inter_left_path_eq_fourth)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.common_path_internals_disjoint_side_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.common_path)
      (Walk.InternalVertices F.side_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.common_path F.side_path (Or.inr rfl)
      (fun z => F.common_path_inter_side_path_eq_fourth)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.right_path_internals_disjoint_left_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.right_path)
      (Walk.InternalVertices F.left_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.right_path F.left_path (Or.inr rfl)
      (fun z => F.right_path_inter_left_path_eq_fourth)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.right_path_internals_disjoint_side_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.right_path)
      (Walk.InternalVertices F.side_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.right_path F.side_path (Or.inr rfl)
      (fun z => F.right_path_inter_side_path_eq_fourth)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.K5FourthSourceEdgePaths.left_path_internals_disjoint_side_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    {C : D.CommonSupportEndpointPaths} {c : Fin 5}
    {A : C.CommonBranchArmPaths c}
    (F : A.K5FourthSourceEdgePaths) :
    Disjoint (Walk.InternalVertices F.left_path)
      (Walk.InternalVertices F.side_path) := by
  exact
    walkInternalVertices_disjoint_of_support_inter_eq_endpoint
      F.left_path F.side_path (Or.inr rfl)
      (fun z => F.left_path_inter_side_path_eq_fourth)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
