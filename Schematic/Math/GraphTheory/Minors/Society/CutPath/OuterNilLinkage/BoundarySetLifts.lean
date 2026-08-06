import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilLinkage.ConcreteLifts
namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- The rebuilt linkage graph has at least three surviving society-boundary
vertices whenever the concrete target triple `(a,s,t)` is admissible.

This is the cardinality half of the source GM IX `(2.2)` set-target handoff:
the later augmenting-path argument may choose arbitrary surviving boundary
targets, but in the no-endpoint subcase the old triple already proves that the
target set has size at least three. -/
theorem outerNilCommonLeftEndpointLinkageSubgraph_boundarySet_ncard_ge_three_of_boundary_allowed
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
              T.outerNilCommonLeftEndpointAttach j m) :
    3 <=
      ({v :
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).verts |
        (v : V) ∈ S.boundarySet} : Set
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).verts).ncard := by
  classical
  let K :=
    T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
      hleg_k_nil hi hk hij_order hjk_order
  let boundaryK : Fin 3 -> K.verts := fun r : Fin 3 =>
    (⟨outerNilCommonLeftEndpointBoundary P a r,
      T.outerNilCommonLeftEndpointBoundary_mem_linkageSubgraph P hgraph
        hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hboundary_allowed r⟩ :
      K.verts)
  let Y : Set K.verts := {v : K.verts | (v : V) ∈ S.boundarySet}
  have hboundaryK_inj : Function.Injective boundaryK := by
    intro r s hrs
    exact
      outerNilCommonLeftEndpointBoundary_injective_of_leftArc P ha
        (congrArg Subtype.val hrs)
  have hrange_subset : Set.range boundaryK ⊆ Y := by
    rintro v ⟨r, rfl⟩
    exact outerNilCommonLeftEndpointBoundary_mem_of_leftArc P ha r
  have hrange_card : (Set.range boundaryK).ncard = 3 := by
    rw [Set.ncard_range_of_injective hboundaryK_inj]
    simp
  have hle : (Set.range boundaryK).ncard <= Y.ncard :=
    Set.ncard_le_ncard hrange_subset
  have hY : 3 <= Y.ncard := by omega
  simpa [K, Y] using hY

/-- Set-target version of the double-outer-collapsed GM IX `(2.2)` lift.

The source proof does not need the three paths in the rim-deleted graph to end
at a preassigned ordered boundary triple.  It needs three disjoint paths from
the rebuilt attachments to three surviving society-boundary vertices.  This
lemma packages exactly that use of the finite three-terminal Menger theorem and
then feeds the chosen boundary triple to the checked tripod constructor above.
-/
theorem liftOuterNilCommonLeftEndpointOfAllowedBoundarySetSubgraphLinkage_of_threeConnected
    {S H : GeneralSociety V}
    [Fintype V] [DecidableEq V]
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
    (hthree :
      IsThreeConnected
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).coe)
    (hboundary_large :
      3 <=
        ({v :
          (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
            hleg_k_nil hi hk hij_order hjk_order).verts |
          (v : V) ∈ S.boundarySet} : Set
          (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
            hleg_k_nil hi hk hij_order hjk_order).verts).ncard) :
    Nonempty S.Tripod := by
  classical
  let K :=
    T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
      hleg_k_nil hi hk hij_order hjk_order
  let leftK : Fin 3 -> K.verts := fun r : Fin 3 =>
    (⟨T.outerNilCommonLeftEndpointAttach j r,
      T.outerNilCommonLeftEndpointAttach_mem_linkageSubgraph P hgraph
        hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r⟩ : K.verts)
  have hleftK_inj : Function.Injective leftK := by
    intro r s hrs
    exact
      T.outerNilCommonLeftEndpointAttach_injective j
        (congrArg Subtype.val hrs)
  let Y : Set K.verts := {v : K.verts | (v : V) ∈ S.boundarySet}
  have hY : 3 <= Y.ncard := by
    simpa [K, Y] using hboundary_large
  rcases IsThreeConnected.exists_hasThreeVertexLinkage_to_set
      (G := K.coe) hthree hleftK_inj (Y := Y) hY with
    ⟨rightK, hrightK_inj, hrightK_mem, hlink⟩
  let boundary : Fin 3 -> V := fun r : Fin 3 => (rightK r : V)
  have hboundary_mem : forall r : Fin 3, boundary r ∈ S.boundarySet := by
    intro r
    exact hrightK_mem r
  have hboundary_injective : Function.Injective boundary := by
    intro r s hrs
    exact hrightK_inj (Subtype.ext hrs)
  have hboundary_allowed :
      forall r s : Fin 3,
        boundary r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            boundary r = T.outerNilCommonLeftEndpointAttach j m := by
    intro r s hrs
    exact (rightK r).2 s (by simpa [boundary] using hrs)
  rcases hlink with ⟨L⟩
  have L' :
      ThreeVertexLinkage K.coe leftK
        (fun r : Fin 3 =>
          (⟨boundary r,
            T.outerNilCommonLeftEndpointBoundaryTriple_mem_linkageSubgraph
              P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
              boundary hboundary_allowed r⟩ : K.verts)) := by
    simpa [boundary, K, leftK] using L
  exact
    T.liftOuterNilCommonLeftEndpointOfAllowedBoundarySubgraphLinkage
      P hgraph hij hik hjk hi hj hk hleg_i_nil hleg_k_nil hij_order
      hjk_order hpath_contacts boundary hboundary_mem hboundary_injective
      hboundary_allowed L'

/-- Set-target version of the double-outer-collapsed lift from the actual
GM IX `(2.2)` no-separator hypothesis.

Unlike the older fixed-target local lemma, this theorem lets the augmenting
path argument choose whichever three surviving society-boundary vertices it
finds in the rim-deleted linkage graph.  This matches the source proof: the
targets are a boundary set, not the preselected triple `(a,s,t)`. -/
theorem liftOuterNilCommonLeftEndpointOfAllowedBoundarySetSubgraphLinkage_of_not_separates_from_set
    {S H : GeneralSociety V}
    [Fintype V] [DecidableEq V]
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
    (hnosep :
      forall Sdel : Set
        (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
          hleg_k_nil hi hk hij_order hjk_order).verts,
        Sdel.ncard < 3 ->
          Not
            (SeparatesVertexTripleFromSetByDeletion
              (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph
                hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).coe
              Sdel
              (T.outerNilCommonLeftEndpointLinkageSources P hgraph hleg_i_nil
                hleg_k_nil hi hk hij_order hjk_order)
              ({v :
                (T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order).verts |
                (v : V) ∈ S.boundarySet}))) :
    Nonempty S.Tripod := by
  classical
  let K :=
    T.outerNilCommonLeftEndpointLinkageSubgraph P hgraph hleg_i_nil
      hleg_k_nil hi hk hij_order hjk_order
  let leftK : Fin 3 -> K.verts := fun r : Fin 3 =>
    (⟨T.outerNilCommonLeftEndpointAttach j r,
      T.outerNilCommonLeftEndpointAttach_mem_linkageSubgraph P hgraph
        hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r⟩ : K.verts)
  have hleftK_inj : Function.Injective leftK := by
    intro r s hrs
    exact
      T.outerNilCommonLeftEndpointAttach_injective j
        (congrArg Subtype.val hrs)
  let Y : Set K.verts := {v : K.verts | (v : V) ∈ S.boundarySet}
  have hnosepK :
      forall Sdel : Set K.verts, Sdel.ncard < 3 ->
        Not (SeparatesVertexTripleFromSetByDeletion K.coe Sdel leftK Y) := by
    intro Sdel hSdel
    simpa [K, leftK, Y] using hnosep Sdel hSdel
  rcases finite_menger_three_vertex_linkage_to_set_of_not_separates_from_set
      (G := K.coe) (left := leftK) (Y := Y) hleftK_inj hnosepK with
    ⟨rightK, hrightK_mem, hlink⟩
  rcases hlink with ⟨L⟩
  let boundary : Fin 3 -> V := fun r : Fin 3 => (rightK r : V)
  have hboundary_mem : forall r : Fin 3, boundary r ∈ S.boundarySet := by
    intro r
    exact hrightK_mem r
  have hrightK_inj : Function.Injective rightK :=
    L.right_injective
  have hboundary_injective : Function.Injective boundary := by
    intro r s hrs
    exact hrightK_inj (Subtype.ext hrs)
  have hboundary_allowed :
      forall r s : Fin 3,
        boundary r ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            boundary r = T.outerNilCommonLeftEndpointAttach j m := by
    intro r s hrs
    exact (rightK r).2 s (by simpa [boundary] using hrs)
  have L' :
      ThreeVertexLinkage K.coe leftK
        (fun r : Fin 3 =>
          (⟨boundary r,
            T.outerNilCommonLeftEndpointBoundaryTriple_mem_linkageSubgraph
              P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
              boundary hboundary_allowed r⟩ : K.verts)) := by
    simpa [boundary, K, leftK] using L
  exact
    T.liftOuterNilCommonLeftEndpointOfAllowedBoundarySubgraphLinkage
      P hgraph hij hik hjk hi hj hk hleg_i_nil hleg_k_nil hij_order
      hjk_order hpath_contacts boundary hboundary_mem hboundary_injective
      hboundary_allowed L'


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory

