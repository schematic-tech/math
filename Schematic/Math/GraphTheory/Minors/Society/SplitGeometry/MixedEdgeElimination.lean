import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.SourceGeometric

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem mixedEdgeTaggedSupportWitnesses_of_mixed_edge_witnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed :
      GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) :
    GMIX24Split.MixedEdgeTaggedSupportWitnesses P hno_cross hK where
  right_or_path :=
    GMIX24Split.modelEdgeInRightOrPath_tagged_support_localization
      P hno_cross hmixed.1
  left_or_path :=
    GMIX24Split.modelEdgeInLeftOrPath_tagged_support_localization
      P hno_cross hmixed.2.1
  left_or_right :=
    GMIX24Split.modelEdgeInLeftOrRight_tagged_support_localization
      P hno_cross hmixed.2.2

theorem mixedEdgeEndpointSupportWitnesses_of_taggedSupportWitnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (H : GMIX24Split.MixedEdgeTaggedSupportWitnesses P hno_cross hK) :
    GMIX24Split.MixedEdgeEndpointSupportWitnesses P hno_cross hK where
  right_or_path := by
    rcases H.right_or_path with
      ⟨x, y, hxy, e, he, hs1, hs2, hloc⟩
    refine ⟨x, y, hxy, e, he, hs1, hs2, ?_⟩
    rcases hloc with hright | hpath
    · exact Or.inl ⟨hright.2.1, hright.2.2⟩
    · exact Or.inr ⟨hpath.2.1, hpath.2.2⟩
  left_or_path := by
    rcases H.left_or_path with
      ⟨x, y, hxy, e, he, hs1, hs2, hloc⟩
    refine ⟨x, y, hxy, e, he, hs1, hs2, ?_⟩
    rcases hloc with hleft | hpath
    · exact Or.inl ⟨hleft.2.1, hleft.2.2⟩
    · exact Or.inr ⟨hpath.2.1, hpath.2.2⟩
  left_or_right := by
    rcases H.left_or_right with
      ⟨x, y, hxy, e, he, hs1, hs2, hloc⟩
    refine ⟨x, y, hxy, e, he, hs1, hs2, ?_⟩
    rcases hloc with hleft | hright
    · exact Or.inl ⟨hleft.2.1, hleft.2.2⟩
    · exact Or.inr ⟨hright.2.1, hright.2.2⟩

theorem mixedEdgeEndpointSupportWitnesses_of_mixed_edge_witnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed :
      GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) :
    GMIX24Split.MixedEdgeEndpointSupportWitnesses P hno_cross hK := by
  classical
  let M := Classical.choice hK
  refine ⟨?_, ?_, ?_⟩
  · rcases
      GMIX24Split.modelEdgeInRightOrPath_endpoint_localization
        P hno_cross hmixed.1 with
      ⟨x, y, hxy, e, he, hloc⟩
    have hsupp := Walk.out_mem_support_of_mem_edges (p := M.edgePath hxy) he
    exact ⟨x, y, hxy, e, he, hsupp.1, hsupp.2, hloc⟩
  · rcases
      GMIX24Split.modelEdgeInLeftOrPath_endpoint_localization
        P hno_cross hmixed.2.1 with
      ⟨x, y, hxy, e, he, hloc⟩
    have hsupp := Walk.out_mem_support_of_mem_edges (p := M.edgePath hxy) he
    exact ⟨x, y, hxy, e, he, hsupp.1, hsupp.2, hloc⟩
  · rcases
      GMIX24Split.modelEdgeInLeftOrRight_endpoint_localization
        P hno_cross hmixed.2.2 with
      ⟨x, y, hxy, e, he, hloc⟩
    have hsupp := Walk.out_mem_support_of_mem_edges (p := M.edgePath hxy) he
    exact ⟨x, y, hxy, e, he, hsupp.1, hsupp.2, hloc⟩

theorem mixedEdgeEndpointWitnesses_of_endpointSupportWitnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (H : GMIX24Split.MixedEdgeEndpointSupportWitnesses P hno_cross hK) :
    GMIX24Split.MixedEdgeEndpointWitnesses P hno_cross hK where
  right_or_path := by
    rcases H.right_or_path with ⟨x, y, hxy, e, he, _hs1, _hs2, hloc⟩
    exact ⟨x, y, hxy, e, he, hloc⟩
  left_or_path := by
    rcases H.left_or_path with ⟨x, y, hxy, e, he, _hs1, _hs2, hloc⟩
    exact ⟨x, y, hxy, e, he, hloc⟩
  left_or_right := by
    rcases H.left_or_right with ⟨x, y, hxy, e, he, _hs1, _hs2, hloc⟩
    exact ⟨x, y, hxy, e, he, hloc⟩

theorem mixed_edge_obstruction_of_endpoint_support_obstruction
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hsupport :
      GMIX24Split.MixedEdgeEndpointSupportWitnesses P hno_cross hK ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
      GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) ->
      Nonempty S.Cross ∨ Nonempty S.Tripod := by
  intro hmixed
  exact hsupport
    (GMIX24Split.mixedEdgeEndpointSupportWitnesses_of_mixed_edge_witnesses
      P hno_cross hmixed)

theorem mixed_edge_obstruction_of_tagged_support_obstruction
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (htagged :
      GMIX24Split.MixedEdgeTaggedSupportWitnesses P hno_cross hK ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
      GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) ->
      Nonempty S.Cross ∨ Nonempty S.Tripod := by
  intro hmixed
  exact htagged
    (GMIX24Split.mixedEdgeTaggedSupportWitnesses_of_mixed_edge_witnesses
      P hno_cross hmixed)

theorem mixed_edge_obstruction_of_endpoint_obstruction
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hendpoint :
      GMIX24Split.MixedEdgeEndpointWitnesses P hno_cross hK ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
      GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) ->
      Nonempty S.Cross ∨ Nonempty S.Tripod := by
  intro hmixed
  exact hendpoint
    (GMIX24Split.mixedEdgeEndpointWitnesses_of_mixed_edge_witnesses
      P hno_cross hmixed)

theorem kuratowskiNoLeakageAlt_or_mixed_edge_witnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) :
    GMIX24Split.KuratowskiNoLeakageAlt P hno_cross hK ∨
      (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) := by
  classical
  by_cases hleft : GMIX24Split.ModelEdgesNoRightNoPath P hno_cross hK
  · exact Or.inl (Or.inl hleft)
  by_cases hright : GMIX24Split.ModelEdgesNoLeftNoPath P hno_cross hK
  · exact Or.inl (Or.inr (Or.inl hright))
  by_cases hpath : GMIX24Split.ModelEdgesNoLeftNoRight P hno_cross hK
  · exact Or.inl (Or.inr (Or.inr (Or.inl hpath)))
  right
  have hright_or_path :
      GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK := by
    by_contra hnone
    exact hleft
      ⟨(by
          intro x y hxy e he heRight
          exact hnone ⟨x, y, hxy, e, he, Or.inl heRight⟩),
        (by
          intro x y hxy e he hePath
          exact hnone ⟨x, y, hxy, e, he, Or.inr hePath⟩)⟩
  have hleft_or_path :
      GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK := by
    by_contra hnone
    exact hright
      ⟨(by
          intro x y hxy e he heLeft
          exact hnone ⟨x, y, hxy, e, he, Or.inl heLeft⟩),
        (by
          intro x y hxy e he hePath
          exact hnone ⟨x, y, hxy, e, he, Or.inr hePath⟩)⟩
  have hleft_or_right :
      GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK := by
    by_contra hnone
    exact hpath
      ⟨(by
          intro x y hxy e he heLeft
          exact hnone ⟨x, y, hxy, e, he, Or.inl heLeft⟩),
        (by
          intro x y hxy e he heRight
          exact hnone ⟨x, y, hxy, e, he, Or.inr heRight⟩)⟩
  exact ⟨hright_or_path, hleft_or_path, hleft_or_right⟩

theorem kuratowskiNoLeakageAlt_of_no_mixed_edge_witnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hno_mixed :
      Not
        (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
          GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
            GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK)) :
    GMIX24Split.KuratowskiNoLeakageAlt P hno_cross hK := by
  rcases
      GMIX24Split.kuratowskiNoLeakageAlt_or_mixed_edge_witnesses
        P hno_cross hK with hleak | hmixed
  · exact hleak
  · exact False.elim (hno_mixed hmixed)

/-- Positive source form of the mixed-edge Kuratowski exclusion.

The paper proves mixed leakage by building a forbidden cross or tripod.  This
lemma converts that constructive statement into the negative `no_mixed`
hypothesis used by the Kuratowski-localization gluing wrapper. -/
theorem no_mixed_edge_witnesses_of_mixed_edge_obstruction
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hmixed_obstruction :
      (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    Not
      (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) := by
  intro hmixed
  rcases hmixed_obstruction hmixed with hcross | htripod
  · exact hno_cross hcross
  · exact hno_tripod htripod

/-- No-leakage from the constructive mixed-edge obstruction form. -/
theorem kuratowskiNoLeakageAlt_of_mixed_edge_obstruction
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hmixed_obstruction :
      (GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    GMIX24Split.KuratowskiNoLeakageAlt P hno_cross hK :=
  GMIX24Split.kuratowskiNoLeakageAlt_of_no_mixed_edge_witnesses
    P hno_cross hK
    (GMIX24Split.no_mixed_edge_witnesses_of_mixed_edge_obstruction
      P hno_cross hno_tripod hK hmixed_obstruction)

theorem canonicalOfNoCross_kuratowski_localization_of_no_leakage_alt
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (halt : GMIX24Split.KuratowskiNoLeakageAlt P hno_cross hK) :
    ContainsStrictSubdivision K
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph ∨
    ContainsStrictSubdivision K
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph ∨
    ContainsStrictSubdivision K P.pathEdgeGraph ∨
      Nonempty S.Cross ∨ Nonempty S.Tripod := by
  rcases halt with hleft | hrest
  · exact Or.inl
      (GMIX24Split.canonicalOfNoCross_containsStrictSubdivision_left_of_no_right_no_path_edges
        P hno_cross hK hleft.1 hleft.2)
  rcases hrest with hright | hrest
  · exact Or.inr (Or.inl
      (GMIX24Split.canonicalOfNoCross_containsStrictSubdivision_right_of_no_left_no_path_edges
        P hno_cross hK hright.1 hright.2))
  rcases hrest with hpath | hrest
  · exact Or.inr (Or.inr (Or.inl
      (GMIX24Split.containsStrictSubdivision_pathEdgeGraph_of_no_left_no_right_edges
        P hno_cross hK hpath.1 hpath.2)))
  · exact Or.inr (Or.inr (Or.inr hrest))

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
