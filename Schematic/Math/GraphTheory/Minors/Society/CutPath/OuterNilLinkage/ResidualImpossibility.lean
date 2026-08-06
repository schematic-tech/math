import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilLinkage.AllowedSubgraph
namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- In the double-outer-collapsed residual, the side-boundary target cannot
be a nil residual point once the clean tail starts at an old common endpoint.

This is one of the source subcases inside the GM IX `(2.4)` sentence
"then `Q,P_1,P_2,P_3` have a common end": if the clean tail starts at the old
left or old right endpoint, cleanliness forces its boundary end `a` to be that
same endpoint whenever `a` lies on an old rim.  But an internal rim vertex is
neither old common endpoint. -/
theorem outerNilCommonLeftEndpointBoundary_zero_internal_impossible_of_common_endpoint
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hend : x = T.left ∨ x = T.right) :
    forall r : Fin 3,
      Tripod.outerNilCommonLeftEndpointBoundary P a 0 ∈
        Walk.InternalVertices (T.rim r) -> False := by
  intro r hzInternal
  have haInternal : a ∈ Walk.InternalVertices (T.rim r) := by
    simpa [Tripod.outerNilCommonLeftEndpointBoundary] using hzInternal
  have ha_x : a = x :=
    hq_clean a q.end_mem_support
      ⟨r, Or.inl (Walk.internalVertices_subset_support (T.rim r) haInternal)⟩
  rcases hend with hx_left | hx_right
  · exact haInternal.2.1 (by simp [ha_x, hx_left])
  · exact haInternal.2.2 (by simp [ha_x, hx_right])

/-- Source residual split for the side-boundary target in the
double-outer-collapsed branch.

After the clean-tail classifier has reduced the tail start to either an old
common endpoint or a nil non-median rim hit, the target `a` has no remaining
zero-boundary residual in the common-end case.  Thus the only unclosed
zero-boundary branch is the genuine nil-rim residual. -/
theorem outerNilCommonLeftEndpointBoundary_zero_residual_impossible_or_nil_branch
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i k : Fin 3}
    {x a : V} (q : S.graph.Walk x a)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    (forall r : Fin 3,
      (r = i ∨ r = k) ->
        Tripod.outerNilCommonLeftEndpointBoundary P a 0 ∈
          Walk.InternalVertices (T.rim r) ->
        (T.leg r).Nil -> False) ∨
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil := by
  rcases hresidual with hend | hnil
  · refine Or.inl ?_
    intro r _hr hzInternal _hleg_nil
    exact
      T.outerNilCommonLeftEndpointBoundary_zero_internal_impossible_of_common_endpoint
        P q hq_clean hend r hzInternal
  · exact Or.inr hnil

theorem outerNilCommonLeftEndpointLinkageSubgraph_meets_rims_only_at_attach
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
        Walk.supportIndex P.path (T.boundary k)) :
    forall
      (v :
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts)
      (s : Fin 3),
        (v : V) ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun r : Fin 3 =>
            (v : V) = T.outerNilCommonLeftEndpointAttach j r := by
  intro v s hs
  exact v.2 s hs


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
