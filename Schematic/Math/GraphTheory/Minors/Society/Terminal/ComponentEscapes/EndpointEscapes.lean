import Schematic.Math.GraphTheory.Minors.Society.Terminal.Symmetry

/-!
Outside escape paths and last-contact tails from common tripod endpoints.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- With hidden cut-path contacts excluded, both common ends of a left-side
tripod lie in the caught left-side region.

This is the component-theoretic input to the final all-collapsed source case.
Each common end belongs to the support of every old rim, hence to the support
of the canonical left graph.  It cannot lie on the induced cut path: such a
contact would be hidden because a tripod boundary foot is never a common rim
end.  The canonical split support decomposition therefore puts it in
`P.leftSide`, where the defining caught-component property supplies a path to
the left boundary arc. -/
theorem left_side_tripod_common_endpoints_mem_leftSide_of_no_hidden_contact
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    T.left ∈ P.leftSide ∧ T.right ∈ P.leftSide := by
  have hleft_support :
      T.left ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.support :=
    T.rim_support_subset_graph_support 0 (T.rim 0).start_mem_support
  have hright_support :
      T.right ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.support :=
    T.rim_support_subset_graph_support 0 (T.rim 0).end_mem_support
  have hleft_side_or_path : T.left ∈ P.leftSide ∪ P.pathSet :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices
      hleft_support
  have hright_side_or_path : T.right ∈ P.leftSide ∪ P.pathSet :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices
      hright_support
  have hleft_not_path : T.left ∉ P.pathSet := by
    intro hleft_path
    exact hno_hidden T.left hleft_path
      ⟨0, (T.rim 0).start_mem_support⟩
      (fun m hm => T.left_ne_boundary m hm)
  have hright_not_path : T.right ∉ P.pathSet := by
    intro hright_path
    exact hno_hidden T.right hright_path
      ⟨0, (T.rim 0).end_mem_support⟩
      (fun m hm => T.right_ne_boundary m hm)
  exact
    ⟨hleft_side_or_path.resolve_right hleft_not_path,
      hright_side_or_path.resolve_right hright_not_path⟩

/-- The two common ends in the normalized all-collapsed case have paths,
entirely inside the caught side and outside the cut path, to the original
left boundary arc. -/
theorem left_side_tripod_common_endpoint_escape_paths_of_no_hidden_contact
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    (Exists fun a : V =>
      Exists fun q : S.graph.Walk T.left a =>
        a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
          (forall z : V, z ∈ q.support -> z ∈ P.leftSide) ∧
            forall z : V, z ∈ q.support -> z ∈ P.outside) ∧
      Exists fun b : V =>
        Exists fun q : S.graph.Walk T.right b =>
          b ∈ P.leftBoundaryArc ∧ q.IsPath ∧
            (forall z : V, z ∈ q.support -> z ∈ P.leftSide) ∧
              forall z : V, z ∈ q.support -> z ∈ P.outside := by
  rcases
      left_side_tripod_common_endpoints_mem_leftSide_of_no_hidden_contact
        (S := S) hno_cross P T hno_hidden with
    ⟨hleft, hright⟩
  exact
    ⟨P.exists_path_from_leftSide_to_leftBoundaryArc_inside hleft,
      P.exists_path_from_leftSide_to_leftBoundaryArc_inside hright⟩

/-- Component-preserving common-end escapes in the all-collapsed branch.

This is the caught-component dichotomy suppressed by the last sentence of the
GM IX `(2.4)` side-tripod paragraph.  The two old common ends either lie in the
same component of `G - V(P)`, or their paths to the left boundary arc are
vertex-disjoint.  The latter alternative is the input for the forbidden-cross
construction; the former is the input for the fourth-rim construction. -/
theorem left_side_tripod_common_endpoint_component_escape_dichotomy_of_no_hidden_contact
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    Exists fun hleftOutside : T.left ∈ P.outside =>
      Exists fun Cleft :
          (S.graph.induce P.outside).ConnectedComponent =>
        (⟨T.left, hleftOutside⟩ : P.outside) ∈ Cleft.supp ∧
          Exists fun a : V =>
            Exists fun qLeft : S.graph.Walk T.left a =>
              a ∈ P.leftBoundaryArc ∧ qLeft.IsPath ∧
                (forall z : V, z ∈ qLeft.support ->
                  z ∈ induceComponentSupport (G := S.graph) Cleft) ∧
                  Exists fun hrightOutside : T.right ∈ P.outside =>
                    Exists fun Cright :
                        (S.graph.induce P.outside).ConnectedComponent =>
                      (⟨T.right, hrightOutside⟩ : P.outside) ∈ Cright.supp ∧
                        Exists fun b : V =>
                          Exists fun qRight : S.graph.Walk T.right b =>
                            b ∈ P.leftBoundaryArc ∧ qRight.IsPath ∧
                              (forall z : V, z ∈ qRight.support ->
                                z ∈ induceComponentSupport
                                  (G := S.graph) Cright) ∧
                              (Cleft = Cright ∨
                                Disjoint
                                  {z : V | z ∈ qLeft.support}
                                  {z : V | z ∈ qRight.support}) := by
  classical
  rcases
      left_side_tripod_common_endpoints_mem_leftSide_of_no_hidden_contact
        (S := S) hno_cross P T hno_hidden with
    ⟨hleftSide, hrightSide⟩
  rcases
      P.exists_path_from_leftSide_to_leftBoundaryArc_in_outsideComponent
        hleftSide with
    ⟨hleftOutside, Cleft, hleftC, a, qLeft, ha, hqLeftPath,
      hqLeftComponent⟩
  rcases
      P.exists_path_from_leftSide_to_leftBoundaryArc_in_outsideComponent
        hrightSide with
    ⟨hrightOutside, Cright, hrightC, b, qRight, hb, hqRightPath,
      hqRightComponent⟩
  refine
    ⟨hleftOutside, Cleft, hleftC, a, qLeft, ha, hqLeftPath,
      hqLeftComponent, hrightOutside, Cright, hrightC, b, qRight, hb,
      hqRightPath, hqRightComponent, ?_⟩
  by_cases hcomponents : Cleft = Cright
  · exact Or.inl hcomponents
  · right
    rw [Set.disjoint_left]
    intro z hzLeft hzRight
    exact Set.disjoint_left.mp
      (induceComponentSupport_disjoint_of_ne
        (G := S.graph) hcomponents)
      (hqLeftComponent z hzLeft) (hqRightComponent z hzRight)

/-- Last-contact normalization of the source path `Q` from a common theta
endpoint to the caught boundary interval.

The supplied endpoint is already in the old tripod carrier and in the caught
left side.  We first choose a boundary-clean path inside that side and then
drop it at its last old-tripod vertex.  The resulting tail has exactly the
`V(P₁ ∪ P₂ ∪ P₃ ∪ Q₁ ∪ Q₂ ∪ Q₃) -> W₁` cleanliness used in the printed
GM IX `(2.4)` proof: its source belongs to the old tripod and no later vertex
does. -/
theorem left_side_tripod_common_endpoint_last_contact_tail
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {v : V}
    (hv_vertex : v ∈ T.vertexSet)
    (hv_side : v ∈ P.leftSide) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          x ∈ T.vertexSet ∧ a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
            (forall z : V, z ∈ q.support -> z ∈ P.leftSide) ∧
              (forall z : V, z ∈ q.support -> z ∈ P.outside) ∧
                Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                  forall z : V,
                    z ∈ q.support -> z ∈ T.vertexSet -> z = x := by
  classical
  obtain ⟨a, q0, ha, hq0_path, hq0_side, hq0_outside,
      hq0_boundary_clean⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside_boundary_clean
      hno_cross hv_side
  let carrier : Set V := T.vertexSet
  have hv_carrier : v ∈ carrier := by
    simpa [carrier] using hv_vertex
  obtain ⟨x, hxq0, hxcarrier, htail_path, htail_clean,
      htail_subset, _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hq0_path carrier
      (by simpa [carrier] using hv_carrier)
  let tail : S.graph.Walk x a := q0.dropUntil x hxq0
  have htail_boundary_clean :
      Walk.InternalVertices tail ∩ S.boundarySet = ∅ := by
    simpa [tail] using
      Walk.IsPath.dropUntil_internalVertices_disjoint_of_internalVertices_disjoint
        hq0_path hxq0 S.boundarySet hq0_boundary_clean
  refine ⟨x, a, tail, ?_, ha, ?_, ?_, ?_, htail_boundary_clean, ?_⟩
  · simpa [carrier] using hxcarrier
  · simpa [tail] using htail_path
  · intro z hz
    exact hq0_side z (htail_subset z (by simpa [tail] using hz))
  · intro z hz
    exact hq0_outside z (htail_subset z (by simpa [tail] using hz))
  · intro z hz hzT
    exact htail_clean z (by simpa [tail] using hz)
      (by simpa [carrier] using hzT)

/-- Simultaneous source-normalized escape tails from the two common ends of
the old theta.  No disjointness between the two tails is asserted here; their
first mutual contact is the next alternative in the source rerouting. -/
theorem left_side_tripod_common_endpoint_last_contact_tails_of_no_hidden_contact
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          x ∈ T.vertexSet ∧ a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
            (forall z : V, z ∈ q.support -> z ∈ P.leftSide) ∧
              (forall z : V, z ∈ q.support -> z ∈ P.outside) ∧
                Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                  forall z : V,
                    z ∈ q.support -> z ∈ T.vertexSet -> z = x) ∧
      (Exists fun y : V =>
        Exists fun b : V =>
          Exists fun q : S.graph.Walk y b =>
            y ∈ T.vertexSet ∧ b ∈ P.leftBoundaryArc ∧ q.IsPath ∧
              (forall z : V, z ∈ q.support -> z ∈ P.leftSide) ∧
                (forall z : V, z ∈ q.support -> z ∈ P.outside) ∧
                  Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                    forall z : V,
                      z ∈ q.support -> z ∈ T.vertexSet -> z = y) := by
  rcases
      left_side_tripod_common_endpoints_mem_leftSide_of_no_hidden_contact
        (S := S) hno_cross P T hno_hidden with
    ⟨hleft_side, hright_side⟩
  exact
    ⟨left_side_tripod_common_endpoint_last_contact_tail
        (S := S) hno_cross P T (T.left_mem_vertexSet) hleft_side,
      left_side_tripod_common_endpoint_last_contact_tail
        (S := S) hno_cross P T (T.right_mem_vertexSet) hright_side⟩

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
