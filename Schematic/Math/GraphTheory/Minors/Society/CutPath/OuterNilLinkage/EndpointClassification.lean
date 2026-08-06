import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilLinkage.AllowedSubgraph
namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

private theorem outerNilCommonLeftEndpoint_boundary_target_forbidden
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k c q : Fin 3}
    (hcj : c ≠ j)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (boundary : Fin 3 -> V)
    (hboundary_allowed :
      forall r s : Fin 3,
        boundary r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            boundary r = T.outerNilCommonLeftEndpointAttach j m)
    (hboundary_eq : boundary q = T.boundary c)
    (hboundary_mem :
      boundary q ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 0).support) :
    False := by
  classical
  rcases hboundary_allowed q 0 hboundary_mem with ⟨m, hm⟩
  fin_cases m
  · have hcj_eq : c = j :=
      T.boundary_injective (by
        simpa [Tripod.outerNilCommonLeftEndpointAttach] using
          hboundary_eq.symm.trans hm)
    exact hcj hcj_eq
  · exact T.left_ne_boundary c (by
      simpa [Tripod.outerNilCommonLeftEndpointAttach] using
        (hboundary_eq.symm.trans hm).symm)
  · exact T.right_ne_boundary c (by
      simpa [Tripod.outerNilCommonLeftEndpointAttach] using
        (hboundary_eq.symm.trans hm).symm)

/-- The rebuilt double-outer-collapsed linkage graph cannot use the cut-path
end `t` as the third target when `t` is the last collapsed foot.

This is the concrete statement behind the endpoint branch in the source
residual proof.  The cut-path rim of the rebuilt tripod has endpoint
`T.attach k`; if the `k`-leg has collapsed and `P.t = T.boundary k`, then this
target is a deleted rim endpoint, not one of the three allowed rebuilt
attachments `(T.boundary j, T.left, T.right)`. -/
theorem outerNilCommonLeftEndpoint_last_endpoint_forbidden_of_boundary_allowed
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (hboundary_allowed :
      forall r s : Fin 3,
        outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (ht_eq_k : P.t = T.boundary k) :
    False := by
  classical
  have ht_eq_attach_k : P.t = T.attach k := by
    exact ht_eq_k.trans ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
  have ht_mem_rim :
      outerNilCommonLeftEndpointBoundary P a 2 ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 0).support := by
    simpa [Tripod.outerNilCommonLeftEndpointBoundary,
      Tripod.outerNilCommonLeftEndpointRim, ht_eq_attach_k] using
      (T.outerNilCommonLeftEndpointRim P hgraph hleg_i_nil hleg_k_nil
        hi hk hij_order hjk_order 0).end_mem_support
  exact
    T.outerNilCommonLeftEndpoint_boundary_target_forbidden
      P hgraph (i := i) (j := j) (k := k) (c := k) (q := 2)
      (Ne.symm hjk) hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed
      (by simpa [Tripod.outerNilCommonLeftEndpointBoundary] using ht_eq_k)
      ht_mem_rim

/-- The rebuilt double-outer-collapsed linkage graph cannot use the cut-path
start `s` as the second target when `s` is the first collapsed foot.

This is the start-end analogue of
`outerNilCommonLeftEndpoint_last_endpoint_forbidden_of_boundary_allowed`. -/
theorem outerNilCommonLeftEndpoint_first_endpoint_forbidden_of_boundary_allowed
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (hboundary_allowed :
      forall r s : Fin 3,
        outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (hs_eq_i : P.s = T.boundary i) :
    False := by
  classical
  have hs_eq_attach_i : P.s = T.attach i := by
    exact hs_eq_i.trans ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
  have hs_mem_rim :
      outerNilCommonLeftEndpointBoundary P a 1 ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 0).support := by
    simpa [Tripod.outerNilCommonLeftEndpointBoundary,
      Tripod.outerNilCommonLeftEndpointRim, hs_eq_attach_i] using
      (T.outerNilCommonLeftEndpointRim P hgraph hleg_i_nil hleg_k_nil
        hi hk hij_order hjk_order 0).start_mem_support
  exact
    T.outerNilCommonLeftEndpoint_boundary_target_forbidden
      P hgraph (i := i) (j := j) (k := k) (c := i) (q := 1)
      hij hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed
      (by simpa [Tripod.outerNilCommonLeftEndpointBoundary] using hs_eq_i)
      hs_mem_rim

/-- Boundary-admissibility for the rebuilt double-outer-collapsed linkage graph
forces the two genuine endpoint exclusions used in the GM IX `(2.2)` handoff.

The rebuilt graph keeps only the three new attachments on the rebuilt rims.  If
the first/last cut-path endpoint were also the corresponding collapsed outer
foot, that endpoint would be a deleted old attachment and hence could not be one
of the three admissible target vertices. -/
theorem outerNilCommonLeftEndpoint_extreme_endpoint_exclusions_of_boundary_allowed
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (hboundary_allowed :
      forall r s : Fin 3,
        outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m) :
    P.s ≠ T.boundary i ∧ P.t ≠ T.boundary k := by
  constructor
  · intro hs_eq_i
    exact
      T.outerNilCommonLeftEndpoint_first_endpoint_forbidden_of_boundary_allowed
        P hgraph hij hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
        hboundary_allowed hs_eq_i
  · intro ht_eq_k
    exact
      T.outerNilCommonLeftEndpoint_last_endpoint_forbidden_of_boundary_allowed
        P hgraph hjk hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
        hboundary_allowed ht_eq_k

/-- Endpoint exclusion forced by the full rim-deleted linkage target.

This is a checked guardrail for the GM IX `(2.2)` handoff.  A linkage in
`outerNilCommonLeftEndpointLinkageSubgraph` already contains the
`hboundary_allowed` target-membership proof, so it is only a valid target in
the source no-endpoint branch.  The collapsed endpoint cases must be handled
by their own ambient-tripod constructors; they cannot be discharged by asking
for this linkage. -/
theorem outerNilCommonLeftEndpoint_extreme_endpoint_exclusions_of_linkage
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (hlink :
      Exists fun hboundary_allowed :
        (forall r s : Fin 3,
          outerNilCommonLeftEndpointBoundary P a r ∈
            (T.outerNilCommonLeftEndpointRim P hgraph hleg_i_nil hleg_k_nil
              hi hk hij_order hjk_order s).support ->
            Exists fun m : Fin 3 =>
              outerNilCommonLeftEndpointBoundary P a r =
                T.outerNilCommonLeftEndpointAttach j m) =>
        HasThreeVertexLinkage
          (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
            hleg_k_nil hi hk hij_order hjk_order).coe
          (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
            hleg_k_nil hi hk hij_order hjk_order)
          (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
            hleg_k_nil hi hk hij_order hjk_order
            (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed)) :
    P.s ≠ T.boundary i ∧ P.t ≠ T.boundary k := by
  rcases hlink with ⟨hboundary_allowed, _hlinkage⟩
  exact
    T.outerNilCommonLeftEndpoint_extreme_endpoint_exclusions_of_boundary_allowed
      P hgraph hij hjk hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      hboundary_allowed

/-- If the start of the GM IX cut path lies on the rebuilt cut-path rim in the
double-outer-collapsed construction, then the first collapsed side-tripod foot
is exactly that start vertex. -/
theorem outerNilCommonLeftEndpoint_start_mem_cut_rim_eq_first_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hs :
      P.s ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 0).support) :
    T.boundary i = P.s := by
  exact
    P.pathSegmentBetween_start_mem_eq_left hi hk
      (Nat.le_of_lt (lt_trans hij_order hjk_order))
      (by
        simpa [Tripod.outerNilCommonLeftEndpointRim] using hs)

/-- If the end of the GM IX cut path lies on the rebuilt cut-path rim in the
double-outer-collapsed construction, then the last collapsed side-tripod foot
is exactly that end vertex. -/
theorem outerNilCommonLeftEndpoint_end_mem_cut_rim_eq_last_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (ht :
      P.t ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 0).support) :
    T.boundary k = P.t := by
  exact
    P.pathSegmentBetween_end_mem_eq_right hi hk
      (Nat.le_of_lt (lt_trans hij_order hjk_order))
      (by
        simpa [Tripod.outerNilCommonLeftEndpointRim] using ht)

private theorem outerNilCommonLeftEndpoint_path_vertex_allowed_or_outer_boundary
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {b : V}
    (hb_path : b ∈ P.pathSet)
    (hbT : b ∈ T.vertexSet) :
    (Exists fun m : Fin 3 =>
      b = T.outerNilCommonLeftEndpointAttach j m) ∨
      b = T.boundary i ∨ b = T.boundary k := by
  classical
  rcases hpath_contacts b hb_path hbT with ⟨m, hm⟩
  rcases fin3_eq_of_pairwise hij hik hjk (m := m) with hmi | hmj | hmk
  · exact Or.inr (Or.inl (by simpa [hmi] using hm))
  · exact Or.inl ⟨0, by
      simpa [Tripod.outerNilCommonLeftEndpointAttach, hmj] using hm⟩
  · exact Or.inr (Or.inr (by simpa [hmk] using hm))

/-- If a cut-path vertex lies on the old left side-rim route in the
double-outer-collapsed common-left construction, path-contact normalization
says it is one of the three side-tripod feet.  The middle foot is an allowed
new attachment; the two outer feet are the genuine collapsed-end residuals. -/
theorem outerNilCommonLeftEndpoint_path_vertex_mem_left_old_rim_allowed_or_outer_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {b : V}
    (hb_path : b ∈ P.pathSet)
    (hb :
      b ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 1).support) :
    (Exists fun m : Fin 3 =>
      b = T.outerNilCommonLeftEndpointAttach j m) ∨
      b = T.boundary i ∨ b = T.boundary k := by
  classical
  have hbOld :
      b ∈ (T.attachToAttachViaLeft i k).support := by
    simpa [Tripod.outerNilCommonLeftEndpointRim,
      SimpleGraph.Walk.support_mapLe_eq_support] using hb
  have hbT : b ∈ T.vertexSet := by
    rcases T.attachToAttachViaLeft_support_cases hbOld with hbi | hbk
    · exact T.rim_mem_vertexSet (i := i) hbi
    · exact T.rim_mem_vertexSet (i := k) hbk
  exact
    T.outerNilCommonLeftEndpoint_path_vertex_allowed_or_outer_boundary
      P hij hik hjk hpath_contacts hb_path hbT

/-- Right-side analogue of
`outerNilCommonLeftEndpoint_path_vertex_mem_left_old_rim_allowed_or_outer_boundary`. -/
theorem outerNilCommonLeftEndpoint_path_vertex_mem_right_old_rim_allowed_or_outer_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {b : V}
    (hb_path : b ∈ P.pathSet)
    (hb :
      b ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 2).support) :
    (Exists fun m : Fin 3 =>
      b = T.outerNilCommonLeftEndpointAttach j m) ∨
      b = T.boundary i ∨ b = T.boundary k := by
  classical
  have hbOld :
      b ∈ (T.attachToAttachViaRight i k).support := by
    simpa [Tripod.outerNilCommonLeftEndpointRim,
      SimpleGraph.Walk.support_mapLe_eq_support] using hb
  have hbT : b ∈ T.vertexSet := by
    rcases T.attachToAttachViaRight_support_cases hbOld with hbi | hbk
    · exact T.rim_mem_vertexSet (i := i) hbi
    · exact T.rim_mem_vertexSet (i := k) hbk
  exact
    T.outerNilCommonLeftEndpoint_path_vertex_allowed_or_outer_boundary
      P hij hik hjk hpath_contacts hb_path hbT

/-- Endpoint classification for `P.s` in the double-outer-collapsed linkage
graph.  Being on any rebuilt rim is either boundary-allowed for the GM IX
`(2.2)` linkage graph, or forces `P.s` to be one of the two collapsed outer
feet. -/
theorem outerNilCommonLeftEndpoint_start_mem_rim_allowed_or_outer_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (s : Fin 3)
    (hs :
      P.s ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support) :
    (Exists fun m : Fin 3 =>
      P.s = T.outerNilCommonLeftEndpointAttach j m) ∨
      P.s = T.boundary i ∨ P.s = T.boundary k := by
  classical
  fin_cases s
  · exact Or.inr (Or.inl
      (T.outerNilCommonLeftEndpoint_start_mem_cut_rim_eq_first_boundary
        P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hs).symm)
  · exact
      T.outerNilCommonLeftEndpoint_path_vertex_mem_left_old_rim_allowed_or_outer_boundary
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
        hjk_order hpath_contacts P.s_mem_pathSet hs
  · exact
      T.outerNilCommonLeftEndpoint_path_vertex_mem_right_old_rim_allowed_or_outer_boundary
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
        hjk_order hpath_contacts P.s_mem_pathSet hs

/-- Endpoint classification for `P.t` in the double-outer-collapsed linkage
graph. -/
theorem outerNilCommonLeftEndpoint_end_mem_rim_allowed_or_outer_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (s : Fin 3)
    (ht :
      P.t ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support) :
    (Exists fun m : Fin 3 =>
      P.t = T.outerNilCommonLeftEndpointAttach j m) ∨
      P.t = T.boundary i ∨ P.t = T.boundary k := by
  classical
  fin_cases s
  · exact Or.inr (Or.inr
      (T.outerNilCommonLeftEndpoint_end_mem_cut_rim_eq_last_boundary
        P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order ht).symm)
  · exact
      T.outerNilCommonLeftEndpoint_path_vertex_mem_left_old_rim_allowed_or_outer_boundary
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
        hjk_order hpath_contacts P.t_mem_pathSet ht
  · exact
      T.outerNilCommonLeftEndpoint_path_vertex_mem_right_old_rim_allowed_or_outer_boundary
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
        hjk_order hpath_contacts P.t_mem_pathSet ht


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
