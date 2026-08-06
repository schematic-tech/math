import Schematic.Math.GraphTheory.Minors.Society.Terminal.SourceObligations.OrderedLegs

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Source-clean side-tripod contradiction after the final GM IX `(2.2)`
no-small-separator augmentation has been supplied for the
double-outer-collapsed branch.

This is the same fixed-tripod eliminator as the 3-connected version below, but
with the hypothesis in the literal form used in the printed proof: no deletion
set of size `< 3` separates the three rebuilt attachments from the three
target boundary vertices in the rim-deleted linkage graph.  The formal finite
Menger theorem then produces the three disjoint paths and the checked lift
turns them into the forbidden ambient tripod.
-/
theorem left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_outer_nil_no_separator
    [Fintype V]
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False)
    (hnosep_factory :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
        (hi : T.boundary i ∈ P.pathSet) ->
        (hj : T.boundary j ∈ P.pathSet) ->
        (hk : T.boundary k ∈ P.pathSet) ->
        (hij_order :
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j)) ->
        (hjk_order :
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k)) ->
        forall {x a : V} (q : S.graph.Walk x a),
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
        a ∈ P.leftBoundaryArc ->
        q.IsPath ->
        (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
        (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
        (forall z : V, z ∈ q.support ->
          (Exists fun r : Fin 3 =>
            z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
          z = x) ->
        ((x = T.left ∨ x = T.right) ∨
          Exists fun r : Fin 3 =>
            (r = i ∨ r = k) ∧
              x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) ->
        forall
          (hleg_i_nil : (T.leg i).Nil)
          (hleg_k_nil : (T.leg k).Nil),
          Exists fun hboundary_allowed :
            (forall r s : Fin 3,
              Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
                (T.outerNilCommonLeftEndpointRim P
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
                Exists fun m : Fin 3 =>
                  Tripod.outerNilCommonLeftEndpointBoundary P a r =
                    T.outerNilCommonLeftEndpointAttach j m) =>
            forall Sdel : Set
              (T.outerNilCommonLeftEndpointLinkageSubgraph P
                (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts,
              Sdel.ncard < 3 ->
                Not
                  (SeparatesVertexTriplesByDeletion
                    (T.outerNilCommonLeftEndpointLinkageSubgraph P
                      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe
                    Sdel
                    (fun r : Fin 3 =>
                      (⟨T.outerNilCommonLeftEndpointAttach j r,
                        T.outerNilCommonLeftEndpointAttach_mem_linkageSubgraph P
                          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r⟩ :
                        (T.outerNilCommonLeftEndpointLinkageSubgraph P
                          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts))
                    (fun r : Fin 3 =>
                      (⟨Tripod.outerNilCommonLeftEndpointBoundary P a r,
                        T.outerNilCommonLeftEndpointBoundary_mem_linkageSubgraph P
                          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
                          hboundary_allowed r⟩ :
                        (T.outerNilCommonLeftEndpointLinkageSubgraph P
                          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)))) :
    False := by
  classical
  let hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hsource_clean hno_hidden
  have hall :
      forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  obtain ⟨_z0, x, a, q, _hz0T, _hz0Left, hxT, ha, hq_path,
      hq_side, hq_outside, hq_clean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at
      P hno_cross T j (hall j)
  have hmedian :
      x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
    refine
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_outer_nil_linkage
        P hno_cross hno_tripod T hij hik hjk q hxT ha
        (hall i) (hall j) (hall k) hq_path hij_order hjk_order
        hq_outside hpath_contacts hq_clean ?_
    intro hresidual hleg_i_nil hleg_k_nil
    rcases
        hnosep_factory hij hik hjk (hall i) (hall j) (hall k)
          hij_order hjk_order q hxT ha hq_path hq_side hq_outside
          hq_clean hresidual hleg_i_nil hleg_k_nil with
      ⟨hboundary_allowed, hnosep⟩
    refine ⟨hboundary_allowed, ?_⟩
    exact
      T.outerNilCommonLeftEndpointLinkageSubgraph_hasThreeVertexLinkage_of_not_separates
        P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
        hleg_i_nil hleg_k_nil (hall i) (hall k) hij_order hjk_order ha
        hboundary_allowed hnosep
  have hq_clean_vertex :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x := by
    intro z hz hzT
    exact hq_clean z hz (by
      rcases hzT with hzRim | hzLeg
      · rcases hzRim with ⟨r, hr⟩
        exact ⟨r, Or.inl hr⟩
      · rcases hzLeg with ⟨r, hr⟩
        exact ⟨r, Or.inr hr⟩)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk q hmedian ha
      (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside hpath_contacts hq_clean_vertex)

/-- Source-clean side-tripod contradiction with the double-collapsed branch
given in the source-correct obstruction form.

This is the same assembly as the linkage version below, but the residual
factory is allowed to return the forbidden ambient tripod directly.  This is
the form needed for the endpoint and collapsed-arm residuals: those branches
are not fixed `(a,s,t)` linkage statements, but they do produce the ambient
tripod required to contradict `hno_tripod`. -/
theorem left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_outer_nil_obstruction
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False)
    (hobstruction_factory :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
        (hi : T.boundary i ∈ P.pathSet) ->
        (hj : T.boundary j ∈ P.pathSet) ->
        (hk : T.boundary k ∈ P.pathSet) ->
        (hij_order :
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j)) ->
        (hjk_order :
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k)) ->
        forall {x a : V} (q : S.graph.Walk x a),
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
        a ∈ P.leftBoundaryArc ->
        q.IsPath ->
        (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
        (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
        (forall z : V, z ∈ q.support ->
          (Exists fun r : Fin 3 =>
            z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
          z = x) ->
        ((x = T.left ∨ x = T.right) ∨
          Exists fun r : Fin 3 =>
            (r = i ∨ r = k) ∧
              x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) ->
        forall
          (_hleg_i_nil : (T.leg i).Nil)
          (_hleg_k_nil : (T.leg k).Nil),
          Nonempty S.Tripod) :
    False := by
  classical
  let hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hsource_clean hno_hidden
  have hall :
      forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  obtain ⟨_z0, x, a, q, _hz0T, _hz0Left, hxT, ha, hq_path,
      hq_side, hq_outside, hq_clean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at
      P hno_cross T j (hall j)
  have hmedian :
      x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
    refine
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_outer_nil_obstruction
        P hno_cross hno_tripod T hij hik hjk q hxT ha
        (hall i) (hall j) (hall k) hq_path hij_order hjk_order
        hq_outside hpath_contacts hq_clean ?_
    intro hresidual hleg_i_nil hleg_k_nil
    exact
      hobstruction_factory hij hik hjk (hall i) (hall j) (hall k)
        hij_order hjk_order q hxT ha hq_path hq_side hq_outside
        hq_clean hresidual hleg_i_nil hleg_k_nil
  have hq_clean_vertex :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x := by
    intro z hz hzT
    exact hq_clean z hz (by
      rcases hzT with hzRim | hzLeg
      · rcases hzRim with ⟨r, hr⟩
        exact ⟨r, Or.inl hr⟩
      · rcases hzLeg with ⟨r, hr⟩
        exact ⟨r, Or.inr hr⟩)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk q hmedian ha
      (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside hpath_contacts hq_clean_vertex)

/-- Source-clean side-tripod contradiction after the final GM IX `(2.2)`
augmentation has been supplied for the double-outer-collapsed branch.

This is the one-tripod version of the checked residual/linkage constructor:
hidden rim contacts have already been excluded, so all cut-path contacts are
the three feet.  The clean opposite-side tail is then classified exactly as in
the source proof.  Every branch except the double-collapsed outer-leg case is
closed by the existing ambient-tripod constructors; in that last case the
provided GM IX `(2.2)` augmentation gives the three disjoint paths in the
rim-deleted linkage graph, and the checked lift again yields the forbidden
ambient tripod. -/
theorem left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_outer_nil_linkage
    [Fintype V] [Fintype (Sym2 V)]
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False)
    (hlinkage_factory :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
        (hi : T.boundary i ∈ P.pathSet) ->
        (hj : T.boundary j ∈ P.pathSet) ->
        (hk : T.boundary k ∈ P.pathSet) ->
        (hij_order :
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j)) ->
        (hjk_order :
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k)) ->
        forall {x a : V} (q : S.graph.Walk x a),
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
        a ∈ P.leftBoundaryArc ->
        q.IsPath ->
        (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
        (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
        (forall z : V, z ∈ q.support ->
          (Exists fun r : Fin 3 =>
            z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
          z = x) ->
        ((x = T.left ∨ x = T.right) ∨
          Exists fun r : Fin 3 =>
            (r = i ∨ r = k) ∧
              x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) ->
        forall
          (hleg_i_nil : (T.leg i).Nil)
          (hleg_k_nil : (T.leg k).Nil),
          Exists fun hboundary_allowed :
            (forall r s : Fin 3,
              Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
                (T.outerNilCommonLeftEndpointRim P
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
                Exists fun m : Fin 3 =>
                  Tripod.outerNilCommonLeftEndpointBoundary P a r =
                    T.outerNilCommonLeftEndpointAttach j m) =>
            HasThreeVertexLinkage
              (T.outerNilCommonLeftEndpointLinkageSubgraph P
                (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe
              (fun r : Fin 3 =>
                (⟨T.outerNilCommonLeftEndpointAttach j r,
                  T.outerNilCommonLeftEndpointAttach_mem_linkageSubgraph P
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                    hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r⟩ :
                  (T.outerNilCommonLeftEndpointLinkageSubgraph P
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                    hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts))
              (fun r : Fin 3 =>
                (⟨Tripod.outerNilCommonLeftEndpointBoundary P a r,
                  T.outerNilCommonLeftEndpointBoundary_mem_linkageSubgraph P
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                    hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
                    hboundary_allowed r⟩ :
                  (T.outerNilCommonLeftEndpointLinkageSubgraph P
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                    hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts))) :
    False := by
  classical
  let hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hsource_clean hno_hidden
  apply
    left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_outer_nil_obstruction
      S hno_cross hno_tripod P T hsource_clean hno_hidden
  intro i j k hij hik hjk hi hj hk hij_order hjk_order x a q hxT ha
    hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil hleg_k_nil
  rcases
      hlinkage_factory hij hik hjk hi hj hk hij_order hjk_order q hxT ha
        hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil hleg_k_nil with
    ⟨hboundary_allowed, ⟨L⟩⟩
  exact
    T.liftOuterNilCommonLeftEndpointOfAllowedSubgraphLinkage
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hi hj hk hleg_i_nil hleg_k_nil hij_order hjk_order
      hpath_contacts ha hboundary_allowed L

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
