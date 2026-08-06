import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.OrderedFreeness

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Reverse-left form of
`canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_no_separator_no_endpoint`.

The right side of a canonical GM IX `(2.4)` split is represented throughout the
source route as the left side of `P.reverse`.  This theorem makes the final
double-outer-collapsed side-tripod eliminator available in that form without
returning to the older nontrivial-leg interface. -/
theorem canonicalOfNoCross_reverse_left_tripod_free_of_arc_path_contacts_outer_nil_no_separator_no_endpoint
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (harc_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.reverse.leftBoundaryArc -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.reverse.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hendpoints :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
          (hi : T.boundary i ∈ P.reverse.pathSet) ->
          (hj : T.boundary j ∈ P.reverse.pathSet) ->
          (hk : T.boundary k ∈ P.reverse.pathSet) ->
          (hij_order :
            Walk.supportIndex P.reverse.path (T.boundary i) <
              Walk.supportIndex P.reverse.path (T.boundary j)) ->
          (hjk_order :
            Walk.supportIndex P.reverse.path (T.boundary j) <
              Walk.supportIndex P.reverse.path (T.boundary k)) ->
          forall {x a : V} (q : S.graph.Walk x a),
          (Exists fun r : Fin 3 =>
            x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
          a ∈ P.reverse.leftBoundaryArc ->
          q.IsPath ->
          (forall w : V, w ∈ q.support -> w ∈ P.reverse.leftSide) ->
          (forall w : V, w ∈ q.support -> w ∈ P.reverse.outside) ->
          (forall z : V, z ∈ q.support ->
            (Exists fun r : Fin 3 =>
              z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
            z = x) ->
          ((x = T.left ∨ x = T.right) ∨
            Exists fun r : Fin 3 =>
              (r = i ∨ r = k) ∧
                x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) ->
          (T.leg i).Nil -> (T.leg k).Nil ->
            P.reverse.s ≠ T.boundary i ∧ P.reverse.s ≠ T.boundary k ∧
              P.reverse.t ≠ T.boundary i ∧ P.reverse.t ≠ T.boundary k)
    (hnosep_factory :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
          (hi : T.boundary i ∈ P.reverse.pathSet) ->
          (hj : T.boundary j ∈ P.reverse.pathSet) ->
          (hk : T.boundary k ∈ P.reverse.pathSet) ->
          (hij_order :
            Walk.supportIndex P.reverse.path (T.boundary i) <
              Walk.supportIndex P.reverse.path (T.boundary j)) ->
          (hjk_order :
            Walk.supportIndex P.reverse.path (T.boundary j) <
              Walk.supportIndex P.reverse.path (T.boundary k)) ->
          forall {x a : V} (q : S.graph.Walk x a),
          (Exists fun r : Fin 3 =>
            x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
          a ∈ P.reverse.leftBoundaryArc ->
          q.IsPath ->
          (forall w : V, w ∈ q.support -> w ∈ P.reverse.leftSide) ->
          (forall w : V, w ∈ q.support -> w ∈ P.reverse.outside) ->
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
          forall hboundary_allowed :
            (forall r s : Fin 3,
              Tripod.outerNilCommonLeftEndpointBoundary P.reverse a r ∈
                (T.outerNilCommonLeftEndpointRim P.reverse
                  (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
                Exists fun m : Fin 3 =>
                  Tripod.outerNilCommonLeftEndpointBoundary P.reverse a r =
                    T.outerNilCommonLeftEndpointAttach j m),
          forall Sdel : Set
            (T.outerNilCommonLeftEndpointLinkageSubgraph P.reverse
              (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
              hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts,
          Sdel.ncard < 3 ->
            Not
              (SeparatesVertexTriplesByDeletion
                (T.outerNilCommonLeftEndpointLinkageSubgraph P.reverse
                  (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe
                Sdel
                (fun r : Fin 3 =>
                  (⟨T.outerNilCommonLeftEndpointAttach j r,
                    T.outerNilCommonLeftEndpointAttach_mem_linkageSubgraph P.reverse
                      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
                      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r⟩ :
                    (T.outerNilCommonLeftEndpointLinkageSubgraph P.reverse
                      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
                      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts))
                (fun r : Fin 3 =>
                  (⟨Tripod.outerNilCommonLeftEndpointBoundary P.reverse a r,
                    T.outerNilCommonLeftEndpointBoundary_mem_linkageSubgraph P.reverse
                      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
                      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
                      hboundary_allowed r⟩ :
                    (T.outerNilCommonLeftEndpointLinkageSubgraph P.reverse
                      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
                      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)))) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod) :=
  GMIX24Split.canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_no_separator_no_endpoint
    P.reverse hno_cross hno_tripod harc_contacts hpath_contacts hendpoints
    hnosep_factory

/-- Reverse-left form of
`canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_threeConnected_extreme_endpoints`.

This is the right side of the original canonical split, expressed as the left
side of `P.reverse`, with the source GM IX `(2.2)` augmentation supplied in
3-connected form. -/
theorem canonicalOfNoCross_reverse_left_tripod_free_of_arc_path_contacts_outer_nil_threeConnected_extreme_endpoints
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (harc_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.reverse.leftBoundaryArc -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.reverse.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hendpoints :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
          (hi : T.boundary i ∈ P.reverse.pathSet) ->
          (hj : T.boundary j ∈ P.reverse.pathSet) ->
          (hk : T.boundary k ∈ P.reverse.pathSet) ->
          (hij_order :
            Walk.supportIndex P.reverse.path (T.boundary i) <
              Walk.supportIndex P.reverse.path (T.boundary j)) ->
          (hjk_order :
            Walk.supportIndex P.reverse.path (T.boundary j) <
              Walk.supportIndex P.reverse.path (T.boundary k)) ->
          forall {x a : V} (q : S.graph.Walk x a),
          (Exists fun r : Fin 3 =>
            x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
          a ∈ P.reverse.leftBoundaryArc ->
          q.IsPath ->
          (forall w : V, w ∈ q.support -> w ∈ P.reverse.leftSide) ->
          (forall w : V, w ∈ q.support -> w ∈ P.reverse.outside) ->
          (forall z : V, z ∈ q.support ->
            (Exists fun r : Fin 3 =>
              z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
            z = x) ->
          ((x = T.left ∨ x = T.right) ∨
            Exists fun r : Fin 3 =>
              (r = i ∨ r = k) ∧
                x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) ->
          (T.leg i).Nil -> (T.leg k).Nil ->
            P.reverse.s ≠ T.boundary i ∧
              P.reverse.t ≠ T.boundary k)
    (hthree_factory :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
          (hi : T.boundary i ∈ P.reverse.pathSet) ->
          (hj : T.boundary j ∈ P.reverse.pathSet) ->
          (hk : T.boundary k ∈ P.reverse.pathSet) ->
          (hij_order :
            Walk.supportIndex P.reverse.path (T.boundary i) <
              Walk.supportIndex P.reverse.path (T.boundary j)) ->
          (hjk_order :
            Walk.supportIndex P.reverse.path (T.boundary j) <
              Walk.supportIndex P.reverse.path (T.boundary k)) ->
          forall {x a : V} (q : S.graph.Walk x a),
          (Exists fun r : Fin 3 =>
            x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
          a ∈ P.reverse.leftBoundaryArc ->
          q.IsPath ->
          (forall w : V, w ∈ q.support -> w ∈ P.reverse.leftSide) ->
          (forall w : V, w ∈ q.support -> w ∈ P.reverse.outside) ->
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
          forall _hboundary_allowed :
            (forall r s : Fin 3,
              Tripod.outerNilCommonLeftEndpointBoundary P.reverse a r ∈
                (T.outerNilCommonLeftEndpointRim P.reverse
                  (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
                Exists fun m : Fin 3 =>
                  Tripod.outerNilCommonLeftEndpointBoundary P.reverse a r =
                    T.outerNilCommonLeftEndpointAttach j m),
            IsThreeConnected
              (T.outerNilCommonLeftEndpointLinkageSubgraph P.reverse
                (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety_graph_le
                hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod) :=
  GMIX24Split.canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_threeConnected_extreme_endpoints
    P.reverse hno_cross hno_tripod harc_contacts hpath_contacts hendpoints
    hthree_factory


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
