import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilLinkage.ResidualImpossibility
namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Finite-Menger bridge for the exact GM IX `(2.2)` double-collapsed
linkage graph.

The remaining source work is now isolated in `hnosep`: no deletion set of
size `< 3` separates the three rebuilt attachments from the three target
boundary vertices inside the rim-deleted graph.  This theorem applies the
proved finite three-terminal Menger theorem to turn that source
no-separator/augmentation condition into the required linkage. -/
theorem outerNilCommonLeftEndpointLinkageSubgraph_hasThreeVertexLinkage_of_not_separates
    {S H : GeneralSociety V}
    [Fintype V] [DecidableEq V]
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
    (ha : a ∈ P.leftBoundaryArc)
    (hboundary_allowed :
      forall r s : Fin 3,
        outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (hnosep :
      forall Sdel : Set
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).verts,
        Sdel.ncard < 3 ->
          Not
            (SeparatesVertexTriplesByDeletion
              (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph
                hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe
              Sdel
              (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
                hleg_k_nil hi hk hij_order hjk_order)
              (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
                hleg_k_nil hi hk hij_order hjk_order
                (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed))) :
    HasThreeVertexLinkage
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).coe
      (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order)
      (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order
        (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed) := by
  classical
  refine finite_menger_three_vertex_linkage_of_not_separates ?_ ?_ hnosep
  · intro r s hrs
    exact T.outerNilCommonLeftEndpointAttach_injective j
      (congrArg Subtype.val hrs)
  · intro r s hrs
    exact outerNilCommonLeftEndpointBoundary_injective_of_leftArc P ha
      (congrArg Subtype.val hrs)

/-- Arbitrary-boundary finite-Menger bridge for the rim-deleted
double-outer-collapsed linkage graph.

This is the source-correct GM IX `(2.2)` endpoint for the component argument:
once the proof has identified three distinct society-boundary vertices that
survive the rebuilt-rim deletion, it only has to prove the corresponding
`< 3` no-separator condition in this induced graph. -/
theorem outerNilCommonLeftEndpointLinkageSubgraph_hasBoundaryLinkage_of_not_separates
    {S H : GeneralSociety V}
    [Fintype V] [DecidableEq V]
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
    (hboundary_injective : Function.Injective boundary)
    (hboundary_allowed :
      forall r s : Fin 3,
        boundary r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            boundary r = T.outerNilCommonLeftEndpointAttach j m)
    (hnosep :
      forall Sdel : Set
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).verts,
        Sdel.ncard < 3 ->
          Not
            (SeparatesVertexTriplesByDeletion
              (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph
                hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe
              Sdel
              (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
                hleg_k_nil hi hk hij_order hjk_order)
              (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
                hleg_k_nil hi hk hij_order hjk_order boundary hboundary_allowed))) :
    HasThreeVertexLinkage
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).coe
      (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order)
      (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order boundary hboundary_allowed) := by
  classical
  refine finite_menger_three_vertex_linkage_of_not_separates ?_ ?_ hnosep
  · intro r s hrs
    exact T.outerNilCommonLeftEndpointAttach_injective j
      (congrArg Subtype.val hrs)
  · intro r s hrs
    exact hboundary_injective (congrArg Subtype.val hrs)

/-- Arbitrary-boundary three-connected bridge for the rim-deleted
double-outer-collapsed linkage graph.

This is the three-connected companion to
`outerNilCommonLeftEndpointLinkageSubgraph_hasBoundaryLinkage_of_not_separates`.
It is the form needed by the source GM IX `(2.2)` argument once the target
side has been normalized to three surviving society-boundary vertices rather
than the special triple `(a,s,t)`. -/
theorem outerNilCommonLeftEndpointLinkageSubgraph_hasBoundaryLinkage_of_threeConnected
    {S H : GeneralSociety V}
    [Fintype V] [DecidableEq V]
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
    (hboundary_injective : Function.Injective boundary)
    (hboundary_allowed :
      forall r s : Fin 3,
        boundary r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            boundary r = T.outerNilCommonLeftEndpointAttach j m)
    (hthree :
      IsThreeConnected
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).coe) :
    HasThreeVertexLinkage
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).coe
      (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order)
      (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order boundary hboundary_allowed) := by
  classical
  refine hthree.hasThreeVertexLinkage_fin3_triples ?_ ?_
  · intro r s hrs
    exact T.outerNilCommonLeftEndpointAttach_injective j
      (congrArg Subtype.val hrs)
  · intro r s hrs
    exact hboundary_injective (congrArg Subtype.val hrs)

/-- Converse no-small-separator certificate from an already-built GM IX
`(2.2)` linkage in the rim-deleted graph.

This is the easy direction of the finite-Menger handoff specialized to the
double-outer-collapsed source graph: three vertex-disjoint paths cannot all be
blocked by deleting fewer than three vertices.  The hard source work remains
the other direction used in
`outerNilCommonLeftEndpointLinkageSubgraph_hasThreeVertexLinkage_of_not_separates`,
namely proving this no-separator hypothesis from the ambient society. -/
theorem outerNilCommonLeftEndpointLinkageSubgraph_not_separates_of_linkage
    {S H : GeneralSociety V}
    [Fintype V] [DecidableEq V]
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
    (hlink :
      HasThreeVertexLinkage
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).coe
        (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order)
        (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order
          (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed)) :
    forall Sdel : Set
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).verts,
      Sdel.ncard < 3 ->
        Not
          (SeparatesVertexTriplesByDeletion
            (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
              hleg_k_nil hi hk hij_order hjk_order).coe
            Sdel
            (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
              hleg_k_nil hi hk hij_order hjk_order)
            (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
              hleg_k_nil hi hk hij_order hjk_order
              (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed)) := by
  classical
  intro Sdel hSdel
  exact HasThreeVertexLinkage.not_separates_by_small_deletion hlink hSdel

/-- The source GM IX `(2.2)` augmentation in the usual 3-connected form.

After the double-outer-collapsed rims have been deleted except for their three
attachments, a 3-connectedness proof for that induced subgraph gives the
three disjoint paths from the rebuilt attachments to `(a,s,t)` by the finite
three-terminal Menger theorem.  The remaining source work in the hard
side-tripod branch is therefore to prove this exact 3-connectedness/no-small
separator condition from the ambient side-society hypotheses. -/
theorem outerNilCommonLeftEndpointLinkageSubgraph_hasThreeVertexLinkage_of_threeConnected
    {S H : GeneralSociety V}
    [Fintype V] [DecidableEq V]
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
    (ha : a ∈ P.leftBoundaryArc)
    (hboundary_allowed :
      forall r s : Fin 3,
        outerNilCommonLeftEndpointBoundary P a r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            outerNilCommonLeftEndpointBoundary P a r =
              T.outerNilCommonLeftEndpointAttach j m)
    (hthree :
      IsThreeConnected
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).coe) :
    HasThreeVertexLinkage
      (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order).coe
      (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order)
      (T.outerNilCommonLeftEndpointLinkageTargets P hgraph hleg_i_nil
        hleg_k_nil hi hk hij_order hjk_order
        (outerNilCommonLeftEndpointBoundary P a) hboundary_allowed) := by
  exact
    T.outerNilCommonLeftEndpointLinkageSubgraph_hasBoundaryLinkage_of_threeConnected
      P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      (outerNilCommonLeftEndpointBoundary P a)
      (outerNilCommonLeftEndpointBoundary_injective_of_leftArc P ha)
      hboundary_allowed hthree


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
