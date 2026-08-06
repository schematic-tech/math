import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.TagObstructions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.z_eq_branchVertex_of_right_left_unique
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hne :
      Not ((D.right_or_path.x = D.left_or_path.x ∧
            D.right_or_path.y = D.left_or_path.y) ∨
          (D.right_or_path.x = D.left_or_path.y ∧
            D.right_or_path.y = D.left_or_path.x)))
    (hunique :
      forall w : W,
        (w = D.right_or_path.x ∨ w = D.right_or_path.y) ->
          (w = D.left_or_path.x ∨ w = D.left_or_path.y) ->
            w = c) :
    C.z = (Classical.choice hK).branchVertex c :=
  D.right_or_path.support_inter_eq_common_branchVertex
    D.left_or_path hne hunique C.z_right C.z_left

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.z_eq_branchVertex_of_right_side_unique
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hne :
      Not ((D.right_or_path.x = D.left_or_right.x ∧
            D.right_or_path.y = D.left_or_right.y) ∨
          (D.right_or_path.x = D.left_or_right.y ∧
            D.right_or_path.y = D.left_or_right.x)))
    (hunique :
      forall w : W,
        (w = D.right_or_path.x ∨ w = D.right_or_path.y) ->
          (w = D.left_or_right.x ∨ w = D.left_or_right.y) ->
            w = c) :
    C.z = (Classical.choice hK).branchVertex c :=
  D.right_or_path.support_inter_eq_common_branchVertex
    D.left_or_right hne hunique C.z_right C.z_side

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.z_eq_branchVertex_of_left_side_unique
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hne :
      Not ((D.left_or_path.x = D.left_or_right.x ∧
            D.left_or_path.y = D.left_or_right.y) ∨
          (D.left_or_path.x = D.left_or_right.y ∧
            D.left_or_path.y = D.left_or_right.x)))
    (hunique :
      forall w : W,
        (w = D.left_or_path.x ∨ w = D.left_or_path.y) ->
          (w = D.left_or_right.x ∨ w = D.left_or_right.y) ->
            w = c) :
    C.z = (Classical.choice hK).branchVertex c :=
  D.left_or_path.support_inter_eq_common_branchVertex
    D.left_or_right hne hunique C.z_left C.z_side

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.z_eq_branchVertex_of_right_left_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_right : c = D.right_or_path.x ∨ c = D.right_or_path.y)
    (hc_left : c = D.left_or_path.x ∨ c = D.left_or_path.y)
    (hne :
      Not ((D.right_or_path.x = D.left_or_path.x ∧
            D.right_or_path.y = D.left_or_path.y) ∨
          (D.right_or_path.x = D.left_or_path.y ∧
            D.right_or_path.y = D.left_or_path.x))) :
    C.z = (Classical.choice hK).branchVertex c :=
  C.z_eq_branchVertex_of_right_left_unique hne
    (two_pair_unique_common_endpoint_of_not_same
      D.right_or_path.hxy.ne D.left_or_path.hxy.ne
      hc_right hc_left hne)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.z_eq_branchVertex_of_right_side_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_right : c = D.right_or_path.x ∨ c = D.right_or_path.y)
    (hc_side : c = D.left_or_right.x ∨ c = D.left_or_right.y)
    (hne :
      Not ((D.right_or_path.x = D.left_or_right.x ∧
            D.right_or_path.y = D.left_or_right.y) ∨
          (D.right_or_path.x = D.left_or_right.y ∧
            D.right_or_path.y = D.left_or_right.x))) :
    C.z = (Classical.choice hK).branchVertex c :=
  C.z_eq_branchVertex_of_right_side_unique hne
    (two_pair_unique_common_endpoint_of_not_same
      D.right_or_path.hxy.ne D.left_or_right.hxy.ne
      hc_right hc_side hne)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.z_eq_branchVertex_of_left_side_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_left : c = D.left_or_path.x ∨ c = D.left_or_path.y)
    (hc_side : c = D.left_or_right.x ∨ c = D.left_or_right.y)
    (hne :
      Not ((D.left_or_path.x = D.left_or_right.x ∧
            D.left_or_path.y = D.left_or_right.y) ∨
          (D.left_or_path.x = D.left_or_right.y ∧
            D.left_or_path.y = D.left_or_right.x))) :
    C.z = (Classical.choice hK).branchVertex c :=
  C.z_eq_branchVertex_of_left_side_unique hne
    (two_pair_unique_common_endpoint_of_not_same
      D.left_or_path.hxy.ne D.left_or_right.hxy.ne
      hc_left hc_side hne)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.same_right_left_or_z_eq_branchVertex_of_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_right : c = D.right_or_path.x ∨ c = D.right_or_path.y)
    (hc_left : c = D.left_or_path.x ∨ c = D.left_or_path.y) :
    ((D.right_or_path.x = D.left_or_path.x ∧
        D.right_or_path.y = D.left_or_path.y) ∨
      (D.right_or_path.x = D.left_or_path.y ∧
        D.right_or_path.y = D.left_or_path.x)) ∨
      C.z = (Classical.choice hK).branchVertex c := by
  rcases
      two_pair_same_or_unique_common_endpoint
        D.right_or_path.hxy.ne D.left_or_path.hxy.ne
        hc_right hc_left with hsame | hunique
  · exact Or.inl hsame
  · exact Or.inr
      (C.z_eq_branchVertex_of_right_left_unique hunique.1 hunique.2)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.same_right_side_or_z_eq_branchVertex_of_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_right : c = D.right_or_path.x ∨ c = D.right_or_path.y)
    (hc_side : c = D.left_or_right.x ∨ c = D.left_or_right.y) :
    ((D.right_or_path.x = D.left_or_right.x ∧
        D.right_or_path.y = D.left_or_right.y) ∨
      (D.right_or_path.x = D.left_or_right.y ∧
        D.right_or_path.y = D.left_or_right.x)) ∨
      C.z = (Classical.choice hK).branchVertex c := by
  rcases
      two_pair_same_or_unique_common_endpoint
        D.right_or_path.hxy.ne D.left_or_right.hxy.ne
        hc_right hc_side with hsame | hunique
  · exact Or.inl hsame
  · exact Or.inr
      (C.z_eq_branchVertex_of_right_side_unique hunique.1 hunique.2)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.same_left_side_or_z_eq_branchVertex_of_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    {c : W}
    (hc_left : c = D.left_or_path.x ∨ c = D.left_or_path.y)
    (hc_side : c = D.left_or_right.x ∨ c = D.left_or_right.y) :
    ((D.left_or_path.x = D.left_or_right.x ∧
        D.left_or_path.y = D.left_or_right.y) ∨
      (D.left_or_path.x = D.left_or_right.y ∧
        D.left_or_path.y = D.left_or_right.x)) ∨
      C.z = (Classical.choice hK).branchVertex c := by
  rcases
      two_pair_same_or_unique_common_endpoint
        D.left_or_path.hxy.ne D.left_or_right.hxy.ne
        hc_left hc_side with hsame | hunique
  · exact Or.inl hsame
  · exact Or.inr
      (C.z_eq_branchVertex_of_left_side_unique hunique.1 hunique.2)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.source_common_endpoint_duplicate_or_branchVertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    (hcommon :
      Exists fun c : W =>
        (c = D.right_or_path.x ∨ c = D.right_or_path.y) ∧
          (c = D.left_or_path.x ∨ c = D.left_or_path.y) ∧
            (c = D.left_or_right.x ∨ c = D.left_or_right.y)) :
    Exists fun c : W =>
      (c = D.right_or_path.x ∨ c = D.right_or_path.y) ∧
        (c = D.left_or_path.x ∨ c = D.left_or_path.y) ∧
          (c = D.left_or_right.x ∨ c = D.left_or_right.y) ∧
            ((((D.right_or_path.x = D.left_or_path.x ∧
                  D.right_or_path.y = D.left_or_path.y) ∨
                (D.right_or_path.x = D.left_or_path.y ∧
                  D.right_or_path.y = D.left_or_path.x)) ∨
                C.z = (Classical.choice hK).branchVertex c) ∧
              ((((D.right_or_path.x = D.left_or_right.x ∧
                    D.right_or_path.y = D.left_or_right.y) ∨
                  (D.right_or_path.x = D.left_or_right.y ∧
                    D.right_or_path.y = D.left_or_right.x)) ∨
                  C.z = (Classical.choice hK).branchVertex c) ∧
                (((D.left_or_path.x = D.left_or_right.x ∧
                    D.left_or_path.y = D.left_or_right.y) ∨
                  (D.left_or_path.x = D.left_or_right.y ∧
                    D.left_or_path.y = D.left_or_right.x)) ∨
                  C.z = (Classical.choice hK).branchVertex c))) := by
  rcases hcommon with ⟨c, hcR, hcL, hcS⟩
  exact
    ⟨c, hcR, hcL, hcS,
      C.same_right_left_or_z_eq_branchVertex_of_common_endpoint hcR hcL,
      C.same_right_side_or_z_eq_branchVertex_of_common_endpoint hcR hcS,
      C.same_left_side_or_z_eq_branchVertex_of_common_endpoint hcL hcS⟩

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.z_eq_branchVertex_of_common_source_endpoint_of_right_left_not_same
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths)
    (hcommon :
      Exists fun c : W =>
        (c = D.right_or_path.x ∨ c = D.right_or_path.y) ∧
          (c = D.left_or_path.x ∨ c = D.left_or_path.y) ∧
            (c = D.left_or_right.x ∨ c = D.left_or_right.y))
    (hne :
      Not ((D.right_or_path.x = D.left_or_path.x ∧
            D.right_or_path.y = D.left_or_path.y) ∨
          (D.right_or_path.x = D.left_or_path.y ∧
            D.right_or_path.y = D.left_or_path.x))) :
    Exists fun c : W =>
      (c = D.right_or_path.x ∨ c = D.right_or_path.y) ∧
        (c = D.left_or_path.x ∨ c = D.left_or_path.y) ∧
          (c = D.left_or_right.x ∨ c = D.left_or_right.y) ∧
            C.z = (Classical.choice hK).branchVertex c := by
  rcases hcommon with ⟨c, hcR, hcL, hcS⟩
  exact ⟨c, hcR, hcL, hcS,
    C.z_eq_branchVertex_of_right_left_common_endpoint hcR hcL hne⟩

theorem MixedEdgeTaggedSupportData.commonSupportWithEndpointRegions_of_supports_meet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK)
    (hmeet :
      Exists fun z : V =>
        z ∈ D.right_or_path.supportSet ∧
          z ∈ D.left_or_path.supportSet ∧
            z ∈ D.left_or_right.supportSet) :
    D.CommonSupportWithEndpointRegions := by
  rcases hmeet with ⟨z, hzR, hzL, hzS⟩
  exact ⟨z, hzR, hzL, hzS,
    D.right_or_path_endpoint_regions,
    D.left_or_path_endpoint_regions,
    D.left_or_right_endpoint_regions⟩

theorem MixedEdgeTaggedSupportData.K33_common_source_endpoint_of_pairwise_share
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (h_right_left :
      D.right_or_path.SourceEdgesShareEndpoint D.left_or_path)
    (h_right_side :
      D.right_or_path.SourceEdgesShareEndpoint D.left_or_right)
    (h_left_side :
      D.left_or_path.SourceEdgesShareEndpoint D.left_or_right) :
    D.CommonSourceEndpoint := by
  simpa [MixedEdgeTaggedSupportData.CommonSourceEndpoint,
    GMIX24Split.TaggedSupportWitnessData.SourceEdgesShareEndpoint] using
    K33Graph.common_endpoint_of_pairwise_share
      D.right_or_path.hxy D.left_or_path.hxy D.left_or_right.hxy
      h_right_left h_right_side h_left_side

/-- A common source endpoint gives a common host vertex on the three witness
supports: the corresponding strict-subdivision branch vertex. -/
theorem MixedEdgeTaggedSupportData.common_source_endpoint_supports_meet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK)
    {v : W}
    (h_right : v = D.right_or_path.x ∨ v = D.right_or_path.y)
    (h_left : v = D.left_or_path.x ∨ v = D.left_or_path.y)
    (h_side : v = D.left_or_right.x ∨ v = D.left_or_right.y) :
    Exists fun z : V =>
      z ∈ D.right_or_path.supportSet ∧
        z ∈ D.left_or_path.supportSet ∧
          z ∈ D.left_or_right.supportSet := by
  refine ⟨(Classical.choice hK).branchVertex v, ?_, ?_, ?_⟩
  · exact D.right_or_path.branchVertex_mem_supportSet_of_endpoint h_right
  · exact D.left_or_path.branchVertex_mem_supportSet_of_endpoint h_left
  · exact D.left_or_right.branchVertex_mem_supportSet_of_endpoint h_side

theorem MixedEdgeTaggedSupportData.supports_meet_of_common_source_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK)
    (hcommon : D.CommonSourceEndpoint) :
    Exists fun z : V =>
      z ∈ D.right_or_path.supportSet ∧
        z ∈ D.left_or_path.supportSet ∧
          z ∈ D.left_or_right.supportSet := by
  rcases hcommon with ⟨v, hright, hleft, hside⟩
  exact D.common_source_endpoint_supports_meet hright hleft hside

theorem MixedEdgeTaggedSupportData.commonSupportWithEndpointRegions_of_common_source_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK)
    (hcommon : D.CommonSourceEndpoint) :
    D.CommonSupportWithEndpointRegions :=
  D.commonSupportWithEndpointRegions_of_supports_meet
    (D.supports_meet_of_common_source_endpoint hcommon)

/-- For `K_{3,3}`, the pairwise support alternatives in
`MixedEdgeTaggedSupportData` either already contain a disjoint-support pair,
or the three source edges have a common endpoint.

This is the source-combinatorial core of the `K_{3,3}` mixed rural-gluing
branch.  The remaining geometric argument only needs to rule out the three
disjoint-support alternatives from the side/path tags; the endpoint case is
now named explicitly. -/
theorem MixedEdgeTaggedSupportData.K33_support_disjoint_or_common_source_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33) :
    (Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ∨
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ∨
        Disjoint D.left_or_path.supportSet D.left_or_right.supportSet) ∨
      D.CommonSourceEndpoint := by
  rcases D.right_left_relation with hdisj | hshare
  · exact Or.inl (Or.inl hdisj)
  rcases D.right_side_relation with hdisj | hshare_right
  · exact Or.inl (Or.inr (Or.inl hdisj))
  rcases D.left_side_relation with hdisj | hshare_left
  · exact Or.inl (Or.inr (Or.inr hdisj))
  exact Or.inr
    (D.K33_common_source_endpoint_of_pairwise_share
      hshare hshare_right hshare_left)

/-- Source-level alternative for the `K_5` mixed branch.

If the three named mixed source edges pairwise share source endpoints, then
they either all share one endpoint, or their six endpoints are covered by
three source vertices.  The latter is the formal triangle case of the source
proof. -/
theorem MixedEdgeTaggedSupportData.K5_common_source_endpoint_or_three_cover_of_pairwise_share
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (h_right_left :
      D.right_or_path.SourceEdgesShareEndpoint D.left_or_path)
    (h_right_side :
      D.right_or_path.SourceEdgesShareEndpoint D.left_or_right)
    (h_left_side :
      D.left_or_path.SourceEdgesShareEndpoint D.left_or_right) :
    D.CommonSourceEndpoint ∨
      D.K5ThreeSourceCover := by
  simpa [MixedEdgeTaggedSupportData.CommonSourceEndpoint,
    MixedEdgeTaggedSupportData.K5ThreeSourceCover,
    GMIX24Split.TaggedSupportWitnessData.SourceEdgesShareEndpoint] using
    three_pair_edges_common_endpoint_or_three_cover
      h_right_left h_right_side h_left_side

theorem MixedEdgeTaggedSupportData.K33_common_source_endpoint_of_common_paths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (C : D.CommonSupportEndpointPaths) :
    D.CommonSourceEndpoint := by
  have h_right_left :
      D.right_or_path.SourceEdgesShareEndpoint D.left_or_path := by
    rcases D.right_left_relation with hdisj | hshare
    · exact False.elim (Set.disjoint_left.mp hdisj C.z_right C.z_left)
    · exact hshare
  have h_right_side :
      D.right_or_path.SourceEdgesShareEndpoint D.left_or_right := by
    rcases D.right_side_relation with hdisj | hshare
    · exact False.elim (Set.disjoint_left.mp hdisj C.z_right C.z_side)
    · exact hshare
  have h_left_side :
      D.left_or_path.SourceEdgesShareEndpoint D.left_or_right := by
    rcases D.left_side_relation with hdisj | hshare
    · exact False.elim (Set.disjoint_left.mp hdisj C.z_left C.z_side)
    · exact hshare
  exact
    D.K33_common_source_endpoint_of_pairwise_share
      h_right_left h_right_side h_left_side

theorem MixedEdgeTaggedSupportData.K5_common_source_endpoint_or_three_cover_of_common_paths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (C : D.CommonSupportEndpointPaths) :
    D.CommonSourceEndpoint ∨
      D.K5ThreeSourceCover := by
  have h_right_left :
      D.right_or_path.SourceEdgesShareEndpoint D.left_or_path := by
    rcases D.right_left_relation with hdisj | hshare
    · exact False.elim (Set.disjoint_left.mp hdisj C.z_right C.z_left)
    · exact hshare
  have h_right_side :
      D.right_or_path.SourceEdgesShareEndpoint D.left_or_right := by
    rcases D.right_side_relation with hdisj | hshare
    · exact False.elim (Set.disjoint_left.mp hdisj C.z_right C.z_side)
    · exact hshare
  have h_left_side :
      D.left_or_path.SourceEdgesShareEndpoint D.left_or_right := by
    rcases D.left_side_relation with hdisj | hshare
    · exact False.elim (Set.disjoint_left.mp hdisj C.z_left C.z_side)
    · exact hshare
  exact
    D.K5_common_source_endpoint_or_three_cover_of_pairwise_share
      h_right_left h_right_side h_left_side

theorem MixedEdgeTaggedSupportData.K33_common_paths_duplicate_or_branchVertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (C : D.CommonSupportEndpointPaths) :
    Exists fun c : K33Vertex =>
      (c = D.right_or_path.x ∨ c = D.right_or_path.y) ∧
        (c = D.left_or_path.x ∨ c = D.left_or_path.y) ∧
          (c = D.left_or_right.x ∨ c = D.left_or_right.y) ∧
            ((((D.right_or_path.x = D.left_or_path.x ∧
                  D.right_or_path.y = D.left_or_path.y) ∨
                (D.right_or_path.x = D.left_or_path.y ∧
                  D.right_or_path.y = D.left_or_path.x)) ∨
                C.z = (Classical.choice hK33).branchVertex c) ∧
              ((((D.right_or_path.x = D.left_or_right.x ∧
                    D.right_or_path.y = D.left_or_right.y) ∨
                  (D.right_or_path.x = D.left_or_right.y ∧
                    D.right_or_path.y = D.left_or_right.x)) ∨
                  C.z = (Classical.choice hK33).branchVertex c) ∧
                (((D.left_or_path.x = D.left_or_right.x ∧
                    D.left_or_path.y = D.left_or_right.y) ∨
                  (D.left_or_path.x = D.left_or_right.y ∧
                    D.left_or_path.y = D.left_or_right.x)) ∨
                  C.z = (Classical.choice hK33).branchVertex c))) :=
  C.source_common_endpoint_duplicate_or_branchVertex
    (D.K33_common_source_endpoint_of_common_paths C)

theorem MixedEdgeTaggedSupportData.K5_common_paths_duplicate_or_branchVertex_or_three_cover
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (C : D.CommonSupportEndpointPaths) :
    (Exists fun c : Fin 5 =>
      (c = D.right_or_path.x ∨ c = D.right_or_path.y) ∧
        (c = D.left_or_path.x ∨ c = D.left_or_path.y) ∧
          (c = D.left_or_right.x ∨ c = D.left_or_right.y) ∧
            ((((D.right_or_path.x = D.left_or_path.x ∧
                  D.right_or_path.y = D.left_or_path.y) ∨
                (D.right_or_path.x = D.left_or_path.y ∧
                  D.right_or_path.y = D.left_or_path.x)) ∨
                C.z = (Classical.choice hK5).branchVertex c) ∧
              ((((D.right_or_path.x = D.left_or_right.x ∧
                    D.right_or_path.y = D.left_or_right.y) ∨
                  (D.right_or_path.x = D.left_or_right.y ∧
                    D.right_or_path.y = D.left_or_right.x)) ∨
                  C.z = (Classical.choice hK5).branchVertex c) ∧
                (((D.left_or_path.x = D.left_or_right.x ∧
                    D.left_or_path.y = D.left_or_right.y) ∨
                  (D.left_or_path.x = D.left_or_right.y ∧
                    D.left_or_path.y = D.left_or_right.x)) ∨
                  C.z = (Classical.choice hK5).branchVertex c)))) ∨
      D.K5ThreeSourceCover := by
  rcases D.K5_common_source_endpoint_or_three_cover_of_common_paths C with
    hcommon | hcover
  · exact Or.inl (C.source_common_endpoint_duplicate_or_branchVertex hcommon)
  · exact Or.inr hcover

theorem MixedEdgeTaggedSupportData.K33_common_paths_duplicate_or_commonBranchArmPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK33 : ContainsStrictSubdivision K33Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK33)
    (C : D.CommonSupportEndpointPaths) :
    D.rightLeftSame ∨ D.rightSideSame ∨ D.leftSideSame ∨
      Exists fun c : K33Vertex => Nonempty (C.CommonBranchArmPaths c) := by
  classical
  by_cases hRL : D.rightLeftSame
  · exact Or.inl hRL
  by_cases hRS : D.rightSideSame
  · exact Or.inr (Or.inl hRS)
  by_cases hLS : D.leftSideSame
  · exact Or.inr (Or.inr (Or.inl hLS))
  rcases D.K33_common_source_endpoint_of_common_paths C with
    ⟨c, hcR, hcL, hcS⟩
  exact Or.inr (Or.inr (Or.inr
    ⟨c, ⟨C.commonBranchArmPaths hcR hcL hcS hRL hRS hLS⟩⟩))

theorem MixedEdgeTaggedSupportData.K5_common_paths_duplicate_or_commonBranchArmPaths_or_three_cover
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5)
    (C : D.CommonSupportEndpointPaths) :
    (D.rightLeftSame ∨ D.rightSideSame ∨ D.leftSideSame ∨
      Exists fun c : Fin 5 => Nonempty (C.CommonBranchArmPaths c)) ∨
      D.K5ThreeSourceCover := by
  classical
  rcases D.K5_common_source_endpoint_or_three_cover_of_common_paths C with
    hcommon | hcover
  · left
    by_cases hRL : D.rightLeftSame
    · exact Or.inl hRL
    by_cases hRS : D.rightSideSame
    · exact Or.inr (Or.inl hRS)
    by_cases hLS : D.leftSideSame
    · exact Or.inr (Or.inr (Or.inl hLS))
    rcases hcommon with ⟨c, hcR, hcL, hcS⟩
    exact Or.inr (Or.inr (Or.inr
      ⟨c, ⟨C.commonBranchArmPaths hcR hcL hcS hRL hRS hLS⟩⟩))
  · exact Or.inr hcover

/-- Full source-combinatorial split for `K_5` mixed data.

The three pairwise strict-subdivision alternatives reduce to either a
disjoint-support pair, a common source endpoint, or the `K_5` triangle-source
case.  This is the exact branching needed before constructing the ambient
cross/tripod obstruction. -/
theorem MixedEdgeTaggedSupportData.K5_support_disjoint_or_common_source_endpoint_or_three_cover
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5) :
    (Disjoint D.right_or_path.supportSet D.left_or_path.supportSet ∨
      Disjoint D.right_or_path.supportSet D.left_or_right.supportSet ∨
        Disjoint D.left_or_path.supportSet D.left_or_right.supportSet) ∨
      (D.CommonSourceEndpoint ∨
        D.K5ThreeSourceCover) := by
  rcases D.right_left_relation with hdisj | hshare
  · exact Or.inl (Or.inl hdisj)
  rcases D.right_side_relation with hdisj | hshare_right
  · exact Or.inl (Or.inr (Or.inl hdisj))
  rcases D.left_side_relation with hdisj | hshare_left
  · exact Or.inl (Or.inr (Or.inr hdisj))
  exact Or.inr
    (D.K5_common_source_endpoint_or_three_cover_of_pairwise_share
      hshare hshare_right hshare_left)

/-- Eliminate the source-combinatorial alternatives for one unpacked
`K_{3,3}` mixed witness package.

The caller supplies the geometric obstruction constructor for each of the
three disjoint-support cases and for the common-source-endpoint case.  This
keeps the final rural-gluing proof focused on geometry rather than repeatedly
unpacking the strict-subdivision source alternatives. -/
theorem MixedEdgeTaggedSupportData.K33_obstruction_of_support_disjoint_or_common_source_endpoint
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
    (h_common :
      D.CommonSourceEndpoint ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  rcases D.K33_support_disjoint_or_common_source_endpoint with hdisj | hcommon
  · rcases hdisj with hrl | hrs_or_hls
    · exact h_right_left_disjoint hrl
    rcases hrs_or_hls with hrs | hls
    · exact h_right_side_disjoint hrs
    · exact h_left_side_disjoint hls
  · exact h_common hcommon

/-- Eliminate the source-combinatorial alternatives for one unpacked `K_5`
mixed witness package.

The final `K_5` branch now has four explicit geometric targets: the three
possible disjoint-support pairs, the common-source-endpoint case, and the
triangle-source case. -/
theorem MixedEdgeTaggedSupportData.K5_obstruction_of_support_disjoint_or_common_source_endpoint_or_three_cover
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
    (h_common :
      D.CommonSourceEndpoint ->
        Nonempty S.Cross ∨ Nonempty S.Tripod)
    (h_three_cover :
      D.K5ThreeSourceCover ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  rcases
      D.K5_support_disjoint_or_common_source_endpoint_or_three_cover
    with hdisj | hsource
  · rcases hdisj with hrl | hrs_or_hls
    · exact h_right_left_disjoint hrl
    rcases hrs_or_hls with hrs | hls
    · exact h_right_side_disjoint hrs
    · exact h_left_side_disjoint hls
  · rcases hsource with hcommon | htriangle
    · exact h_common hcommon
    · exact h_three_cover htriangle


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
