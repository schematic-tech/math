import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilLinkage.ConnectivityBridges
namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- The double-collapsed constructor specialized to the canonical induced
subgraph that deletes all non-attachment rim vertices.

After this point, the only remaining source work in the hard side-tripod
branch is to prove, by the GM IX `(2.2)` augmenting-path argument, that the
displayed induced subgraph contains the required three-vertex linkage. -/
theorem liftOuterNilCommonLeftEndpointOfAllowedSubgraphLinkage
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
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
        outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (L :
      ThreeVertexLinkage
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).coe
        (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order)
        (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order
          (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed)) :
    Nonempty S.Tripod :=
  T.liftOuterNilCommonLeftEndpointOfSubgraphLinkage
    P hgraph hij hik hjk hi hj hk hleg_i_nil hleg_k_nil hij_order
    hjk_order hpath_contacts ha
    (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
      hleg_k_nil hi hk hij_order hjk_order)
    (T.outerNilCommonLeftEndpointAttach_mem_linkageSubgraph P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order)
    (T.outerNilCommonLeftEndpointBoundary_mem_linkageSubgraph P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hboundary_allowed)
    L
    (T.outerNilCommonLeftEndpointLinkageSubgraph_meets_rims_only_at_attach
      P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order)

/-- Arbitrary-boundary specialization of
`liftOuterNilCommonLeftEndpointOfAllowedSubgraphLinkage`.

The endpoint normalization in GM IX `(2.2)` may produce a boundary triple other
than `(a,s,t)`.  This theorem is the checked handoff from such a linkage in the
standard rim-deleted graph to the forbidden ambient tripod. -/
theorem liftOuterNilCommonLeftEndpointOfAllowedBoundarySubgraphLinkage
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
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
    (boundary : Fin 3 -> V)
    (hboundary_mem : forall r : Fin 3, boundary r ∈ S.boundarySet)
    (hboundary_injective : Function.Injective boundary)
    (hboundary_allowed :
      forall r s : Fin 3,
        boundary r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            boundary r = T.outerNilCommonLeftEndpointAttach j m)
    (L :
      ThreeVertexLinkage
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).coe
        (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order)
        (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order boundary hboundary_allowed)) :
    Nonempty S.Tripod :=
  T.liftOuterNilCommonLeftEndpointOfBoundarySubgraphLinkage
    P hgraph hij hik hjk hi hj hk hleg_i_nil hleg_k_nil hij_order
    hjk_order hpath_contacts boundary hboundary_mem hboundary_injective
    (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
      hleg_k_nil hi hk hij_order hjk_order)
    (T.outerNilCommonLeftEndpointAttach_mem_linkageSubgraph P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order)
    (T.outerNilCommonLeftEndpointBoundaryTriple_mem_linkageSubgraph
      P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      boundary hboundary_allowed)
    L
    (T.outerNilCommonLeftEndpointLinkageSubgraph_meets_rims_only_at_attach
      P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order)


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory

