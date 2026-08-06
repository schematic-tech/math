import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilConstruction
namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Vertices allowed in the GM IX `(2.2)` linkage graph for the
double-outer-collapsed common-left construction.

All vertices lying on one of the rebuilt rims are deleted except for the three
new attachments.  This is exactly the source requirement that the
`X -> Y` paths have their initial vertex, and no other vertex, in
`X = V(P_1 ∪ P_2 ∪ P_3)`. -/
def outerNilCommonLeftEndpointLinkageAllowed
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
    Set V :=
  {z : V |
    forall s : Fin 3,
      z ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
        Exists fun r : Fin 3 => z = T.outerNilCommonLeftEndpointAttach j r}

/-- The actual induced subgraph in which the source GM IX `(2.2)` linkage is
to be constructed in the double-outer-collapsed case. -/
def outerNilCommonLeftEndpointLinkageSubgraph
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
    S.graph.Subgraph :=
  (⊤ : S.graph.Subgraph).induce
    (T.outerNilCommonLeftEndpointLinkageAllowed P hgraph hleg_i_nil
      hleg_k_nil hi hk hij_order hjk_order)

theorem outerNilCommonLeftEndpointAttach_mem_linkageAllowed
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
    (r : Fin 3) :
    T.outerNilCommonLeftEndpointAttach j r ∈
      T.outerNilCommonLeftEndpointLinkageAllowed P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order := by
  intro s _hs
  exact ⟨r, rfl⟩

theorem outerNilCommonLeftEndpointAttach_mem_linkageSubgraph
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
    (r : Fin 3) :
    T.outerNilCommonLeftEndpointAttach j r ∈
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).verts := by
  simpa [Tripod.outerNilCommonLeftEndpointLinkageSubgraph] using
    T.outerNilCommonLeftEndpointAttach_mem_linkageAllowed P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r

theorem outerNilCommonLeftEndpointBoundary_mem_linkageSubgraph
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
    {a : V}
    (hboundary_allowed :
      forall r s : Fin 3,
        outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (r : Fin 3) :
    outerNilCommonLeftEndpointBoundary P a r ∈
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).verts := by
  intro s hs
  exact hboundary_allowed r s hs

/-- Arbitrary-boundary target membership in the rim-deleted
double-outer-collapsed linkage graph. -/
theorem outerNilCommonLeftEndpointBoundaryTriple_mem_linkageSubgraph
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
    (boundary : Fin 3 -> V)
    (hboundary_allowed :
      forall r s : Fin 3,
        boundary r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            boundary r = T.outerNilCommonLeftEndpointAttach j m)
    (r : Fin 3) :
    boundary r ∈
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).verts := by
  intro s hs
  exact hboundary_allowed r s hs

/-- The three rebuilt attachments as vertices of the rim-deleted linkage
subgraph. -/
def outerNilCommonLeftEndpointLinkageSources
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
    Fin 3 ->
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).verts :=
  fun r =>
    ⟨T.outerNilCommonLeftEndpointAttach j r,
      T.outerNilCommonLeftEndpointAttach_mem_linkageSubgraph P hgraph
        hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r⟩

/-- An admissible boundary triple as vertices of the rim-deleted linkage
subgraph. -/
def outerNilCommonLeftEndpointLinkageTargets
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
    (boundary : Fin 3 -> V)
    (hboundary_allowed :
      forall r s : Fin 3,
        boundary r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            boundary r = T.outerNilCommonLeftEndpointAttach j m) :
    Fin 3 ->
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).verts :=
  fun r =>
    ⟨boundary r,
      T.outerNilCommonLeftEndpointBoundaryTriple_mem_linkageSubgraph
        P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
        boundary hboundary_allowed r⟩

end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
