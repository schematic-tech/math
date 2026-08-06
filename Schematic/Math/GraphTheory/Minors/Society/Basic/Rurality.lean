import Schematic.Math.GraphTheory.Minors.Society.Basic.OuterTailLifts
import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Rotation.CycleFaces
import Schematic.Math.GraphTheory.Planarity.Basic

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety


def Tripod.lift_of_le
    {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (hboundary_mem :
      forall i : Fin 3, T.boundary i ∈ S.boundarySet) :
    S.Tripod where
  left := T.left
  right := T.right
  left_ne_right := T.left_ne_right
  rim := fun i => (T.rim i).mapLe hgraph
  rim_isPath := by
    intro i
    exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.rim_isPath i)
  attach := T.attach
  attach_mem_rim := by
    intro i
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.attach_mem_rim i
  boundary := T.boundary
  boundary_mem := hboundary_mem
  boundary_injective := T.boundary_injective
  leg := fun i => (T.leg i).mapLe hgraph
  leg_isPath := by
    intro i
    exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath i)
  rim_internals_disjoint := by
    intro i j hij
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.rim_internals_disjoint i j hij
  legs_pairwise_disjoint := by
    intro i j hij
    simpa [SimpleGraph.Walk.support_mapLe_eq_support]
      using T.legs_pairwise_disjoint i j hij
  legs_meet_rims_only_at_attach := by
    intro i j v hvLeg hvRim
    exact T.legs_meet_rims_only_at_attach i j v
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hvLeg)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hvRim)

/-- The repository-level rurality interface for a general society.

For a boundary of length at least three, `disk` is the literal finite
rotation-system certificate for the GM IX drawing in a closed disk.  The
redundant `planar` field is retained because the downstream three-boundary RST
adapter consumes the repository's strict-Kuratowski `IsPlanar` predicate.
For boundaries of length at most two the source theorem calls rurality
trivial; in that case the disk-certificate field is vacuous. -/
structure Rural (S : GeneralSociety V) : Prop where
  planar : IsPlanar S.graph
  disk :
    forall [Fintype V] [DecidableEq V],
      3 <= S.boundarySet.ncard -> Nonempty (DiskRuralCertificate S)

theorem Rural.of_isPlanar_of_boundarySet_ncard_le_two
    {S : GeneralSociety V}
    (hplanar : IsPlanar S.graph)
    (hcard : S.boundarySet.ncard <= 2) :
    Nonempty S.Rural :=
  ⟨{
    planar := hplanar
    disk := fun hlarge => False.elim (by omega)
  }⟩

/-- An edgeless society is rural: its boundary augmentation is exactly the
canonical boundary cycle, equipped with the canonical degree-two planar
rotation.  This is the source-correct base used before selecting the GM IX
`(2.1)` cut path. -/
theorem Rural.of_graph_eq_bot
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (hgraph : S.graph = ⊥) :
    Nonempty S.Rural := by
  classical
  let T : GeneralSociety V := {
    graph := ⊥
    boundary := S.boundary
  }
  have hST : S = T := by
    apply GeneralSociety.ext
    · simpa [T] using hgraph
    · simp [T]
  rw [hST]
  have hplanar : IsPlanar T.graph := by
    letI : DecidableRel T.graph.Adj := Classical.decRel _
    apply IsPlanar.of_max_degree_le_two
    intro v
    simp [T, SimpleGraph.degree, SimpleGraph.neighborFinset]
  refine ⟨{
    planar := hplanar
    disk := ?_
  }⟩
  intro _ _ hlarge
  have hlength_large : 3 <= T.boundary.length := by
    rw [← T.boundarySet_ncard]
    exact hlarge
  let n : Nat := T.boundary.length - 3
  have hlength : T.boundary.length = n + 3 := by
    dsimp [n]
    omega
  letI : DecidableRel
      (T.boundaryAugmentedGraphOfLength (n + 3) hlength).Adj :=
    Classical.decRel _
  letI : DecidableRel
      (T.boundary.cycleGraphOfLength (n + 3) hlength).Adj :=
    Classical.decRel _
  have haugmented :
      T.boundaryAugmentedGraphOfLength (n + 3) hlength =
        T.boundary.cycleGraphOfLength (n + 3) hlength := by
    change (⊥ : SimpleGraph V) ⊔
      T.boundary.cycleGraphOfLength (n + 3) hlength = _
    exact bot_sup_eq _
  have hcycle_degree : forall v : V,
      (T.boundary.cycleGraphOfLength (n + 3) hlength).degree v <= 2 :=
    T.boundary.cycleGraphOfLength_degree_le_two n hlength
  have hdegree : forall v : V,
      (T.boundaryAugmentedGraphOfLength (n + 3) hlength).degree v <= 2 := by
    exact CyclicBoundary.degree_le_two_of_graph_eq haugmented hcycle_degree
  let R : FourColor.RotationSystem
      (T.boundaryAugmentedGraphOfLength (n + 3) hlength) :=
    FourColor.degreeLeTwoRotationSystem hdegree
  let c := T.boundaryCycleWalkOfLength n hlength
  let hc : c.IsCycle := T.boundaryCycleWalkOfLength_isCycle n hlength
  have hsupport :
      ((T.boundaryAugmentedGraphOfLength (n + 3) hlength).induce
        (T.boundaryAugmentedGraphOfLength (n + 3) hlength).support).Preconnected := by
    rw [haugmented]
    exact T.boundary.cycleGraphOfLength_support_preconnected n hlength
  refine ⟨{
    n := n
    boundary_length := hlength
    rotation := R
    dual_eulerPlanar := ?_
    boundary_facial := ?_
  }⟩
  · simpa [R] using
      FourColor.degreeLeTwoRotationSystem_dual_eulerPlanar_of_support_preconnected_cycle
        hdegree hsupport c hc
  · simpa [R, c, hc] using
      FourColor.degreeLeTwoRotationSystem_isFacialCycle hdegree c hc

/-- The `|Ω| <= 2` initial case in the GM IX `(2.4)` induction.

For the general society 3-connectedness predicate, if the boundary has at
most two vertices then no active vertex can lie outside the boundary: the
separation with left side `Ω` and right side all vertices would have order at
most two.  Hence the graph support has at most two vertices and is planar in
the repository's Kuratowski-style interface. -/
theorem rural_of_boundarySet_ncard_le_two
    [Fintype V]
    (S : GeneralSociety V)
    (hthree : S.ThreeConnected)
    (hcard : S.boundarySet.ncard <= 2) :
    Nonempty S.Rural := by
  classical
  have hactive_subset_boundary : S.activeSet ⊆ S.boundarySet := by
    intro v hvActive
    by_contra hvBoundary
    let T : Separation S.graph := {
      left := S.boundarySet
      right := Set.univ
      covers := by
        ext x
        simp
      no_cross := by
        intro a _b _ha haNotRight _hb _hbNotLeft _hab
        exact False.elim (haNotRight (Set.mem_univ a))
    }
    have hboundary_left : S.boundarySet ⊆ T.left := by
      intro x hx
      exact hx
    have hright : ((T.right \ T.left) ∩ S.activeSet).Nonempty := by
      refine ⟨v, ?_⟩
      exact ⟨⟨Set.mem_univ v, hvBoundary⟩, hvActive⟩
    have horder : T.OrderAtMost 2 := by
      refine ⟨S.boundarySet_finite.toFinset, ?_, ?_⟩
      · ext x
        simp [T, Separation.separator]
      · rw [← Set.ncard_eq_toFinset_card
            S.boundarySet S.boundarySet_finite]
        exact hcard
    exact hthree T hboundary_left hright horder
  have hsupport_subset_boundary : S.graph.support ⊆ S.boundarySet := by
    intro v hv
    exact hactive_subset_boundary (Or.inl hv)
  have hsupport_card : S.graph.support.ncard <= 4 := by
    have hle : S.graph.support.ncard <= S.boundarySet.ncard :=
      Set.ncard_le_ncard hsupport_subset_boundary
    omega
  have hplanar_support : IsPlanar (S.graph.induce S.graph.support) := by
    refine isPlanar_of_card_le_four _ ?_
    rw [Set.fintypeCard_eq_ncard]
    exact hsupport_card
  exact Rural.of_isPlanar_of_boundarySet_ncard_le_two
    (IsPlanar.of_induce_support hplanar_support) hcard



end GeneralSociety

end Schematic.Math.GraphTheory
