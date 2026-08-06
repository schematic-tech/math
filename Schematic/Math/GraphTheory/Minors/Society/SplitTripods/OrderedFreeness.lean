import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.OuterNilObstructions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
private theorem clean_tail_median_branch_of_outer_choice
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (houter : Not (T.leg i).Nil ∨ Not (T.leg k).Nil)
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
      (GMIX24Split.canonicalOfNoCross_left_tripod_ordered_residual_impossible_of_first_or_last_non_nil
        P hno_cross hno_tripod T hij hik hjk houter q ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean hresidual)

/-- Direct ordered source side-tripod median branch when only the last ordered
leg is known to be nontrivial.

This is the current sharp form of the GM IX `(2.4)` side-tripod paragraph in
the local development.  The residual classifier leaves either the median
branch, a common old endpoint, or a collapsed outer branch.  The checked
`...residual_impossible_of_last_non_nil` theorem closes the latter two cases by
constructing the forbidden ambient tripod, using only the last ordered side
path as genuinely nontrivial. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_last_non_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_k_not_nil : Not (T.leg k).Nil)
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
    x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) :=
  clean_tail_median_branch_of_outer_choice
    P hno_cross hno_tripod T hij hik hjk (Or.inr hleg_k_not_nil) q hxT ha hold hq_path
    hij_order hjk_order hq_outside hpath_contacts hq_clean

/-- Direct ordered source side-tripod median branch under the exact first/last
outer-leg dichotomy.

This is the normalized local target for the side-tripod paragraph: the clean
outside tail classifier leaves the median branch or a residual, and the
consolidated residual eliminator closes that residual from either nontrivial
outer ordered leg. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_first_or_last_non_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_or_k_not_nil : Not (T.leg i).Nil ∨ Not (T.leg k).Nil)
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
    x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) :=
  clean_tail_median_branch_of_outer_choice
    P hno_cross hno_tripod T hij hik hjk hleg_i_or_k_not_nil q hxT ha hold hq_path
    hij_order hjk_order hq_outside hpath_contacts hq_clean

/-- Left side-tripods are impossible from the exact outer-leg disjunction now
needed by the direct source residual proof.

After ordering the three side feet on the cut path, it is enough that either
outer ordered leg is nontrivial.  The two direct residual eliminators close the
corresponding endpoint and collapsed-side cases, leaving the source median
branch and hence the ambient tripod contradiction. -/
theorem canonicalOfNoCross_left_tripod_free_of_path_contacts_ordered_first_or_last_non_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hordered_first_or_last_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not (T.leg i).Nil ∨ Not (T.leg k).Nil) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  classical
  intro hT
  rcases hT with ⟨T⟩
  have hall :
      forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T (hpath_contacts T)
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  obtain ⟨_z0, x, a, q, _hz0T, _hz0Left, hxT, ha, hq_path,
      _hq_side, hq_outside, hq_clean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at
      P hno_cross T j (hall j)
  have hmedian :
      x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_first_or_last_non_nil
        P hno_cross hno_tripod T hij hik hjk
        (hordered_first_or_last_not_nil T hij hik hjk hij_order hjk_order)
        q hxT ha (fun r : Fin 3 => hall (fin3Order i j k r))
        hq_path hij_order hjk_order hq_outside (hpath_contacts T) hq_clean
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk q hmedian ha
      (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside (hpath_contacts T)
      hq_clean_vertex)

/-- Left side-tripods are impossible once the source GM IX `(2.2)` linkage is
available in the final double-outer-collapsed branch.

This is the source side-tripod paragraph without the older nontrivial-leg
escape hatch.  The proof orders the three side feet on the induced cut path,
chooses the clean tail to the opposite boundary arc, runs the checked residual
analysis, and delegates only the literal paper step "`Q,P_1,P_2,P_3` give the
three disjoint paths" to `hlink_factory`.  That linkage is required in the
rim-deleted induced graph used by
`outerNilCommonLeftEndpointLinkageSubgraph`, so the final lift is an actual
ambient forbidden tripod rather than a legacy endpoint handoff. -/
theorem canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_linkage
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hlink_factory :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
            Exists fun _hboundary_allowed :
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
                      _hboundary_allowed r⟩ :
                    (T.outerNilCommonLeftEndpointLinkageSubgraph P
                      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)))) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  classical
  intro hT
  rcases hT with ⟨T⟩
  have hall :
      forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T (hpath_contacts T)
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
        hq_outside (hpath_contacts T) hq_clean ?_
    intro hresidual hleg_i_nil hleg_k_nil
    exact
      hlink_factory T hij hik hjk (hall i) (hall j) (hall k)
        hij_order hjk_order q hxT ha hq_path hq_side hq_outside hq_clean
        hresidual hleg_i_nil hleg_k_nil
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk q hmedian ha
      (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside (hpath_contacts T)
      hq_clean_vertex)

/-- Left side-tripods are impossible from the source GM IX `(2.2)` separator
condition in the final double-outer-collapsed branch.

This is the same side-tripod paragraph as
`canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_linkage`, but
the residual hypothesis is the paper's no-small-separator premise rather than
an already-built linkage.  The proof applies the finite three-terminal Menger
theorem to the rim-deleted linkage graph and then reuses the checked ambient
tripod constructor. -/
theorem canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_no_separator
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hnosep_factory :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
            Exists fun _hboundary_allowed :
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
                      _hboundary_allowed r⟩ :
                        (T.outerNilCommonLeftEndpointLinkageSubgraph P
                          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)))) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  classical
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_linkage
      P hno_cross hno_tripod hpath_contacts ?_
  intro T i j k hij hik hjk hi hj hk hij_order hjk_order x a q hxT ha
    hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil hleg_k_nil
  rcases
      hnosep_factory T hij hik hjk hi hj hk hij_order hjk_order q hxT ha
        hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil
        hleg_k_nil with
    ⟨hboundary_allowed, hnosep⟩
  refine ⟨hboundary_allowed, ?_⟩
  exact
    T.outerNilCommonLeftEndpointLinkageSubgraph_hasThreeVertexLinkage_of_not_separates
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order ha
      hboundary_allowed hnosep

/-- Left side-tripods are impossible from the 3-connected form of the source
GM IX `(2.2)` augmentation in the final double-outer-collapsed branch.

This is the same residual side-tripod eliminator as
`canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_no_separator`,
but its last hypothesis is the compact graph-theoretic condition that the
rim-deleted linkage graph is 3-connected.  The theorem then applies the
finite three-terminal Menger theorem to obtain the linkage used by the
ambient tripod lift. -/
theorem canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_threeConnected
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hthree_factory :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
            Exists fun _hboundary_allowed :
              (forall r s : Fin 3,
                Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
                  (T.outerNilCommonLeftEndpointRim P
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                    hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
                  Exists fun m : Fin 3 =>
                    Tripod.outerNilCommonLeftEndpointBoundary P a r =
                      T.outerNilCommonLeftEndpointAttach j m) =>
              IsThreeConnected
                (T.outerNilCommonLeftEndpointLinkageSubgraph P
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  classical
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_linkage
      P hno_cross hno_tripod hpath_contacts ?_
  intro T i j k hij hik hjk hi hj hk hij_order hjk_order x a q hxT ha
    hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil hleg_k_nil
  rcases
      hthree_factory T hij hik hjk hi hj hk hij_order hjk_order q hxT ha
        hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil
        hleg_k_nil with
    ⟨hboundary_allowed, hthree⟩
  refine ⟨hboundary_allowed, ?_⟩
  exact
    T.outerNilCommonLeftEndpointLinkageSubgraph_hasThreeVertexLinkage_of_threeConnected
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order ha
      hboundary_allowed hthree

/-- Left side-tripods are impossible from arc/path contact normalization,
endpoint exclusions, and the literal GM IX `(2.2)` no-small-separator
condition in the final double-outer-collapsed branch.

This is the first integrated source-route version of the hard side-tripod
paragraph after the residual analysis.  It no longer asks callers to supply a
three-linkage or even boundary-allowed target data.  The target data is built
from the arc/path contact facts once the four collapsed-end coincidences are
excluded; the supplied no-separator condition is then fed to the finite
three-terminal Menger theorem. -/
theorem canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_no_separator_no_endpoint
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (harc_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hendpoints :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
          (T.leg i).Nil -> (T.leg k).Nil ->
            P.s ≠ T.boundary i ∧ P.s ≠ T.boundary k ∧
              P.t ≠ T.boundary i ∧ P.t ≠ T.boundary k)
    (hnosep_factory :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
          forall _hboundary_allowed :
            (forall r s : Fin 3,
              Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
                (T.outerNilCommonLeftEndpointRim P
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
                Exists fun m : Fin 3 =>
                  Tripod.outerNilCommonLeftEndpointBoundary P a r =
                    T.outerNilCommonLeftEndpointAttach j m),
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
                      _hboundary_allowed r⟩ :
                    (T.outerNilCommonLeftEndpointLinkageSubgraph P
                      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)))) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  classical
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_no_separator
      P hno_cross hno_tripod hpath_contacts ?_
  intro T i j k hij hik hjk hi hj hk hij_order hjk_order x a q hxT ha
    hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil hleg_k_nil
  have hall : forall m : Fin 3, T.boundary m ∈ P.pathSet := by
    intro m
    rcases fin3_eq_of_pairwise hij hik hjk (m := m) with hmi | hmjk
    · simpa [hmi] using hi
    · rcases hmjk with hmj | hmk
      · simpa [hmj] using hj
      · simpa [hmk] using hk
  rcases
      hendpoints T hij hik hjk hi hj hk hij_order hjk_order q hxT ha
        hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil
        hleg_k_nil with
    ⟨hs_ne_i, hs_ne_k, ht_ne_i, ht_ne_k⟩
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
      (harc_contacts T) (hpath_contacts T) ha
      hs_ne_i hs_ne_k ht_ne_i ht_ne_k
  refine ⟨hboundary_allowed, ?_⟩
  intro Sdel hSdel
  exact
    hnosep_factory T hij hik hjk hi hj hk hij_order hjk_order q hxT ha
      hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil
      hleg_k_nil hboundary_allowed Sdel hSdel

/-- Left side-tripods are impossible from arc/path contact normalization, the
two genuine endpoint exclusions, and the literal GM IX `(2.2)` no-small-
separator condition in the final double-outer-collapsed branch.

This removes two artificial endpoint assumptions from
`canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_no_separator_no_endpoint`:
once the three side-tripod feet are ordered on the induced cut path, the start
of the cut path cannot be the last ordered foot and the end cannot be the first
ordered foot. -/
theorem canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_no_separator_extreme_endpoints
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (harc_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hendpoints :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
          (T.leg i).Nil -> (T.leg k).Nil ->
            P.s ≠ T.boundary i ∧ P.t ≠ T.boundary k)
    (hnosep_factory :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
          forall _hboundary_allowed :
            (forall r s : Fin 3,
              Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
                (T.outerNilCommonLeftEndpointRim P
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
                Exists fun m : Fin 3 =>
                  Tripod.outerNilCommonLeftEndpointBoundary P a r =
                    T.outerNilCommonLeftEndpointAttach j m),
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
                      _hboundary_allowed r⟩ :
                    (T.outerNilCommonLeftEndpointLinkageSubgraph P
                      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)))) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  classical
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_no_separator
      P hno_cross hno_tripod hpath_contacts ?_
  intro T i j k hij hik hjk hi hj hk hij_order hjk_order x a q hxT ha
    hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil hleg_k_nil
  have hall : forall m : Fin 3, T.boundary m ∈ P.pathSet := by
    intro m
    rcases fin3_eq_of_pairwise hij hik hjk (m := m) with hmi | hmjk
    · simpa [hmi] using hi
    · rcases hmjk with hmj | hmk
      · simpa [hmj] using hj
      · simpa [hmk] using hk
  rcases
      hendpoints T hij hik hjk hi hj hk hij_order hjk_order q hxT ha
        hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil
        hleg_k_nil with
    ⟨hs_ne_i, ht_ne_k⟩
  let hboundary_allowed :
      forall r s : Fin 3,
        Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            Tripod.outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m :=
    T.outerNilCommonLeftEndpointBoundary_allowed_of_extreme_endpoint_exclusions
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hall
      (harc_contacts T) (hpath_contacts T) ha hs_ne_i ht_ne_k
  refine ⟨hboundary_allowed, ?_⟩
  intro Sdel hSdel
  exact
    hnosep_factory T hij hik hjk hi hj hk hij_order hjk_order q hxT ha
      hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil
      hleg_k_nil hboundary_allowed Sdel hSdel

/-- Left side-tripods are impossible from arc/path contact normalization, the
two genuine endpoint exclusions, and the compact 3-connected form of the
source GM IX `(2.2)` augmentation in the double-outer-collapsed branch.

This is the source-aligned version of
`canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_no_separator_extreme_endpoints`
after replacing the explicit no-small-separator premise by the checked
three-terminal Menger bridge for the rim-deleted linkage graph. -/
theorem canonicalOfNoCross_left_tripod_free_of_arc_path_contacts_outer_nil_threeConnected_extreme_endpoints
    [Fintype V] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (harc_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hendpoints :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
          (T.leg i).Nil -> (T.leg k).Nil ->
            P.s ≠ T.boundary i ∧ P.t ≠ T.boundary k)
    (hthree_factory :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
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
          forall _hboundary_allowed :
            (forall r s : Fin 3,
              Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
                (T.outerNilCommonLeftEndpointRim P
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
                Exists fun m : Fin 3 =>
                  Tripod.outerNilCommonLeftEndpointBoundary P a r =
                    T.outerNilCommonLeftEndpointAttach j m),
            IsThreeConnected
              (T.outerNilCommonLeftEndpointLinkageSubgraph P
                (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
                hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  classical
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_free_of_path_contacts_outer_nil_threeConnected
      P hno_cross hno_tripod hpath_contacts ?_
  intro T i j k hij hik hjk hi hj hk hij_order hjk_order x a q hxT ha
    hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil hleg_k_nil
  have hall : forall m : Fin 3, T.boundary m ∈ P.pathSet := by
    intro m
    rcases fin3_eq_of_pairwise hij hik hjk (m := m) with hmi | hmjk
    · simpa [hmi] using hi
    · rcases hmjk with hmj | hmk
      · simpa [hmj] using hj
      · simpa [hmk] using hk
  rcases
      hendpoints T hij hik hjk hi hj hk hij_order hjk_order q hxT ha
        hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil
        hleg_k_nil with
    ⟨hs_ne_i, ht_ne_k⟩
  let hboundary_allowed :
      forall r s : Fin 3,
        Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            Tripod.outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m :=
    T.outerNilCommonLeftEndpointBoundary_allowed_of_extreme_endpoint_exclusions
      P (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hall
      (harc_contacts T) (hpath_contacts T) ha hs_ne_i ht_ne_k
  refine ⟨hboundary_allowed, ?_⟩
  exact
    hthree_factory T hij hik hjk hi hj hk hij_order hjk_order q hxT ha
      hq_path hq_side hq_outside hq_clean hresidual hleg_i_nil
      hleg_k_nil hboundary_allowed


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
