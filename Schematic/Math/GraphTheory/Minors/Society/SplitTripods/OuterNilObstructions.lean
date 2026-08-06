import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.LastResidualLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- The final double-collapsed residual is closed as soon as the source
GM IX `(2.2)` linkage has been constructed.

This is the direct continuation of
`canonicalOfNoCross_left_tripod_ordered_residual_outer_legs_nil_of_residual`:
all other residual branches have already produced an ambient tripod or a
nontrivial-leg contradiction.  If both outer ordered legs are nil, the rebuilt
three rims are fixed, and a vertex-disjoint linkage from their attachments to
`(a,s,t)` is enough to instantiate the ambient `Tripod`. -/
theorem canonicalOfNoCross_left_tripod_outer_nil_linkage_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (L :
      ThreeVertexLinkage S.graph
        (T.outerNilCommonLeftEndpointAttach j)
        (Tripod.outerNilCommonLeftEndpointBoundary P a))
    (hlink_meet_rims :
      forall r s : Fin 3, forall z : V,
        z ∈ (L.path r).support ->
          z ∈
            (T.outerNilCommonLeftEndpointRim P
              (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
              hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
            z = T.outerNilCommonLeftEndpointAttach j r) :
    False := by
  exact hno_tripod
    (Tripod.liftOuterNilCommonLeftEndpointOfLinkage
      P T
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hi hj hk hleg_i_nil hleg_k_nil hij_order hjk_order
      hpath_contacts ha L hlink_meet_rims)

/-- The final double-collapsed residual is closed by a linkage in the exact
rim-deleted graph used by the source GM IX `(2.2)` argument.

This is the head-on target for the remaining augmenting-path proof.  The
subgraph deletes every rebuilt-rim vertex except the three new attachments;
therefore a three-linkage in this subgraph automatically has the
`X -> Y` property needed to instantiate the ambient forbidden tripod. -/
theorem canonicalOfNoCross_left_tripod_outer_nil_allowed_subgraph_linkage_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hboundary_allowed :
      forall r s : Fin 3,
        Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            Tripod.outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (L :
      ThreeVertexLinkage
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
  exact hno_tripod
    (T.liftOuterNilCommonLeftEndpointOfAllowedSubgraphLinkage
      P
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hi hj hk hleg_i_nil hleg_k_nil hij_order hjk_order
      hpath_contacts ha hboundary_allowed L)

/-- The double-collapsed side-tripod residual is impossible from the exact
GM IX `(2.2)` no-small-separator condition.

This is the local source step immediately before the augmenting-path theorem:
instead of asking for the three disjoint paths outright, it asks for the
`< 3`-separator negation in the rim-deleted graph and invokes the finite
three-terminal Menger theorem already formalized in `Rerouting`. -/
theorem canonicalOfNoCross_left_tripod_outer_nil_no_separator_impossible
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hboundary_allowed :
      forall r s : Fin 3,
        Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            Tripod.outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (hnosep :
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
  obtain ⟨L⟩ :=
    T.outerNilCommonLeftEndpointLinkageSubgraph_hasThreeVertexLinkage_of_not_separates
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order ha
      hboundary_allowed hnosep
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_outer_nil_allowed_subgraph_linkage_impossible
      P hno_cross hno_tripod T hij hik hjk hi hj hk hleg_i_nil hleg_k_nil
      hij_order hjk_order hpath_contacts ha hboundary_allowed L

/-- The double-collapsed side-tripod residual is impossible from the
3-connected form of the GM IX `(2.2)` augmentation.

This is the same hard branch as
`canonicalOfNoCross_left_tripod_outer_nil_no_separator_impossible`, but it
accepts the source no-separation fact in the compact `IsThreeConnected` form
for the rim-deleted linkage graph.  The finite three-terminal Menger theorem
then supplies the required linkage, and the checked linkage lift gives the
forbidden ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_outer_nil_threeConnected_impossible
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hboundary_allowed :
      forall r s : Fin 3,
        Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            Tripod.outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (hthree :
      IsThreeConnected
        (T.outerNilCommonLeftEndpointLinkageSubgraph P
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe) :
    False := by
  classical
  obtain ⟨L⟩ :=
    T.outerNilCommonLeftEndpointLinkageSubgraph_hasThreeVertexLinkage_of_threeConnected
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order ha
      hboundary_allowed hthree
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_outer_nil_allowed_subgraph_linkage_impossible
      P hno_cross hno_tripod T hij hik hjk hi hj hk hleg_i_nil hleg_k_nil
      hij_order hjk_order hpath_contacts ha hboundary_allowed L

/-- The double-collapsed side-tripod residual is impossible in the
no-endpoint subcase from the exact GM IX `(2.2)` no-separator condition.

The previous local boundary lemma constructs the rim-deleted linkage graph's
target membership from the source contact normalization, provided neither end
of the cut path is one of the two collapsed outer feet.  This theorem is the
direct source handoff for that branch: after those four endpoint exclusions,
Menger gives the three disjoint paths and the checked linkage lift produces
the forbidden ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_outer_nil_no_separator_impossible_of_no_endpoint_outer_boundary
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (harc_contacts :
      forall z : V, z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hs_ne_i : P.s ≠ T.boundary i)
    (hs_ne_k : P.s ≠ T.boundary k)
    (ht_ne_i : P.t ≠ T.boundary i)
    (ht_ne_k : P.t ≠ T.boundary k)
    (hnosep :
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
                    (T.outerNilCommonLeftEndpointBoundary_allowed_of_no_endpoint_outer_boundary
                      P
                      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                      hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
                      hjk_order
                      (by
                        intro m
                        rcases fin3_eq_of_pairwise hij hik hjk (m := m) with
                          hmi | hmjk
                        · simpa [hmi] using hi
                        · rcases hmjk with hmj | hmk
                          · simpa [hmj] using hj
                          · simpa [hmk] using hk)
                      harc_contacts hpath_contacts ha
                      hs_ne_i hs_ne_k ht_ne_i ht_ne_k) r⟩ :
                  (T.outerNilCommonLeftEndpointLinkageSubgraph P
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                    hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)))) :
    False := by
  classical
  have hall : forall m : Fin 3, T.boundary m ∈ P.pathSet := by
    intro m
    rcases fin3_eq_of_pairwise hij hik hjk (m := m) with hmi | hmjk
    · simpa [hmi] using hi
    · rcases hmjk with hmj | hmk
      · simpa [hmj] using hj
      · simpa [hmk] using hk
  let hboundary_allowed :
      forall r s : Fin 3,
        Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            Tripod.outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m :=
    T.outerNilCommonLeftEndpointBoundary_allowed_of_no_endpoint_outer_boundary
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hall
      harc_contacts hpath_contacts ha hs_ne_i hs_ne_k ht_ne_i ht_ne_k
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_outer_nil_no_separator_impossible
      P hno_cross hno_tripod T hij hik hjk hi hj hk hleg_i_nil hleg_k_nil
      hij_order hjk_order hpath_contacts ha hboundary_allowed
      (by
        simpa [hboundary_allowed] using hnosep)

/-- Ordered source classifier with the double-collapsed branch stated in its
actual source form.

The printed proof of GM IX `(2.4)` does not need the residual branch to
produce a fixed `(a,s,t)` linkage in every endpoint configuration.  It only
needs that the residual creates the forbidden ambient tripod.  This is the
correct top-level classifier for that use: after the ordered clean-tail
analysis, either the tail starts on the median branch, or the residual
obstruction supplied by the caller contradicts the no-tripod hypothesis. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_outer_nil_obstruction
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hobstruction :
      forall
        (_hresidual :
          (x = T.left ∨ x = T.right) ∨
            Exists fun r : Fin 3 =>
              (r = i ∨ r = k) ∧
                x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil)
        (_hleg_i_nil : (T.leg i).Nil)
        (_hleg_k_nil : (T.leg k).Nil),
        Nonempty S.Tripod) :
    x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
  classical
  have hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet := by
    intro r
    fin_cases r <;> simp [fin3Order, hi, hj, hk]
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
        P hno_cross hno_tripod T hij hik hjk q hxT ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean with
    hmedian | hresidual
  · exact hmedian
  · have houter_nil :
        (T.leg i).Nil ∧ (T.leg k).Nil :=
      GMIX24Split.canonicalOfNoCross_left_tripod_ordered_residual_outer_legs_nil_of_residual
        P hno_cross hno_tripod T hij hik hjk q ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean hresidual
    exact False.elim (hno_tripod (hobstruction hresidual houter_nil.1 houter_nil.2))

/-- Ordered source classifier with the double-collapsed case delegated to the
actual GM IX `(2.2)` linkage construction.

The preceding residual analysis reduces every non-median clean-tail start to
the case where both outer ordered legs have collapsed.  This theorem records
the precise remaining task: build the linkage on the rebuilt three-rim system.
Once that linkage is available in the rim-deleted induced graph,
`canonicalOfNoCross_left_tripod_outer_nil_allowed_subgraph_linkage_impossible`
turns it into the forbidden ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_outer_nil_linkage
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hlink_factory :
      forall
        (_hresidual :
          (x = T.left ∨ x = T.right) ∨
            Exists fun r : Fin 3 =>
              (r = i ∨ r = k) ∧
                x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil)
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
        Nonempty
          (ThreeVertexLinkage
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
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)))) :
    x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_outer_nil_obstruction
      P hno_cross hno_tripod T hij hik hjk q hxT ha hi hj hk hq_path
      hij_order hjk_order hq_outside hpath_contacts hq_clean ?_
  intro hresidual hleg_i_nil hleg_k_nil
  rcases hlink_factory hresidual hleg_i_nil hleg_k_nil with
    ⟨hboundary_allowed, ⟨L⟩⟩
  exact
    T.liftOuterNilCommonLeftEndpointOfAllowedSubgraphLinkage
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hi hj hk hleg_i_nil hleg_k_nil hij_order hjk_order
      hpath_contacts ha hboundary_allowed L

/-- Ordered classifier with the residual localized to collapsed outer legs.

This is the sharpened form of the side-tripod source paragraph before the final
middle-only construction is applied: after ordering the three feet on the cut
path, the clean tail either starts on the median branch or both outer ordered
legs are nil. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_outer_legs_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    (x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) ∨
      ((T.leg i).Nil ∧ (T.leg k).Nil) := by
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
        P hno_cross hno_tripod T hij hik hjk q hxT ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean with
    hmedian | hresidual
  · exact Or.inl hmedian
  · exact Or.inr
      (GMIX24Split.canonicalOfNoCross_left_tripod_ordered_residual_outer_legs_nil_of_residual
        P hno_cross hno_tripod T hij hik hjk q ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean hresidual)

/-- Ordered source side-tripod median branch after the common-end case is also
closed internally.

This is the formal source sentence for the ordered case, requiring only the
first ordered leg to be nontrivial.  The endpoint branch is
closed by the checked common-end constructor; the last nil branch is closed by
the direct arm constructor from the preceding lemma. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_first_non_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
        P hno_cross hno_tripod T hij hik hjk q hxT ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean with
    hmedian | hresidual
  · exact hmedian
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_tripod_ordered_residual_impossible_of_first_non_nil
        P hno_cross hno_tripod T hij hik hjk hleg_i_not_nil
        q ha hold hq_path hij_order hjk_order
        hq_outside hpath_contacts hq_clean hresidual)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
