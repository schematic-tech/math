import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Reattach a degree-one leaf to an Euler-planar rotation system on the
deleted-leaf graph.  This is the forward lift needed after the contraction
induction identifies `G/vw` with `G - v`. -/
theorem HasEulerRotationSystem.of_deleted_leaf_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (hdel : HasEulerRotationSystem (G.induce {z : V | z ≠ v})) :
    HasEulerRotationSystem G := by
  rcases hdel with ⟨R, hR⟩
  exact
    ⟨LeafExtension.leafReattachRotationSystem
      (G := G) (v := v) (w := w) hvw hdegree R,
      LeafExtension.leafReattachRotationSystem_dual_eulerPlanar
        (G := G) (v := v) (w := w) hvw hdegree R hR⟩

/-- Degree-one contraction induction gives the deleted-leaf graph an
Euler-planar rotation system, via the checked quotient isomorphism
`G/vw ≃ G - v`. -/
theorem HasEulerRotationSystem.induce_compl_singleton_of_collapseEdge_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hdegree : G.degree v <= 1)
    (hcollapse :
      HasEulerRotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    HasEulerRotationSystem (G.induce {z : V | z ≠ v}) :=
  HasEulerRotationSystem.of_iso
    (GraphContraction.collapseEdgeDeleteLeftIso_of_degree_le_one
      (G := G) hvw hdegree)
    hcollapse

/-- Degree-one contraction branch for the non-circular embedding target.  If
contracting a leaf edge has an Euler-planar rotation system, then the original
graph has one. -/
theorem HasEulerRotationSystem.of_collapseEdge_of_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hdegree : G.degree v <= 1)
    (hcollapse :
      HasEulerRotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    HasEulerRotationSystem G := by
  have hdel :
      HasEulerRotationSystem (G.induce {z : V | z ≠ v}) :=
    HasEulerRotationSystem.induce_compl_singleton_of_collapseEdge_degree_le_one
      (G := G) (v := v) (w := w) hvw hdegree hcollapse
  exact
    HasEulerRotationSystem.of_deleted_leaf_degree_le_one
      (G := G) (v := v) (w := w) hvw hdegree hdel

/-- Incident-edge form of the degree-one contraction branch. -/
theorem HasEulerRotationSystem.of_incident_collapseEdge_of_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V}
    (hdegree : G.degree v <= 1)
    (hincident : Exists fun w : V => G.Adj v w)
    (hcontract :
      forall {w : V} (hvw : G.Adj v w),
        letI : DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj :=
          Classical.decRel _
        HasEulerRotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    HasEulerRotationSystem G := by
  classical
  rcases hincident with ⟨w, hvw⟩
  letI : DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj :=
    Classical.decRel _
  exact
    HasEulerRotationSystem.of_collapseEdge_of_degree_le_one
      (G := G) (v := v) (w := w) hvw hdegree (hcontract hvw)

/-- Disconnected branch of the non-circular embedding target: if every graph
connected component has an Euler-planar rotation system, then the original
graph has one by gluing the component systems. -/
theorem HasEulerRotationSystem.of_connectedComponents
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcomp :
      forall C : G.ConnectedComponent,
        letI : Fintype C := C.supp.toFinite.fintype
        letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
        HasEulerRotationSystem C.toSimpleGraph) :
    HasEulerRotationSystem G := by
  classical
  let Rcomp : forall C : G.ConnectedComponent,
      RotationSystem C.toSimpleGraph :=
    fun C =>
      letI : Fintype C := C.supp.toFinite.fintype
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      Classical.choose (hcomp C)
  have hRcomp :
      forall C : G.ConnectedComponent,
        letI : Fintype C := C.supp.toFinite.fintype
        letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
        ((Rcomp C).toHypermap).dual.EulerPlanar := by
    intro C
    dsimp [Rcomp]
    exact Classical.choose_spec (hcomp C)
  exact
    ⟨componentRotationSystem (G := G) Rcomp,
      componentRotationSystem_dual_eulerPlanar (G := G) Rcomp hRcomp⟩

/-- Induction-ready disconnected branch: if every connected component that is
planar in the strict-Kuratowski sense has an Euler-planar rotation system, then
the original planar graph has one. -/
theorem HasEulerRotationSystem.of_isPlanar_connectedComponents
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    (hcomp :
      forall C : G.ConnectedComponent,
        letI : Fintype C := C.supp.toFinite.fintype
        letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
        IsPlanar C.toSimpleGraph → HasEulerRotationSystem C.toSimpleGraph) :
    HasEulerRotationSystem G :=
  HasEulerRotationSystem.of_connectedComponents (G := G) (by
    intro C
    exact hcomp C (h_planar.connectedComponent_toSimpleGraph C))

/-- Singleton/smaller base branch of the non-circular embedding target. -/
theorem HasEulerRotationSystem.of_card_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 1) :
    HasEulerRotationSystem G :=
  exists_eulerRotationSystem_of_card_le_one (G := G) hcard

/-- Three-vertex branch of the non-circular embedding target. -/
theorem HasEulerRotationSystem.of_card_le_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 3) :
    HasEulerRotationSystem G :=
  exists_eulerRotationSystem_of_card_le_three (G := G) hcard

/-- A complete four-vertex finite graph is isomorphic to the universe-lifted
`K4` endpoint. -/
noncomputable def completeCardFourIsoK4Lift
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (hcomplete : ∀ x y : V, x ≠ y → G.Adj x y)
    (hcard : Fintype.card V = 4) :
    G ≃g CompleteFourEndpoint.K4LiftGraph.{u} := by
  classical
  let eFin : V ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let e : V ≃ ULift.{u, 0} (Fin 4) := eFin.trans Equiv.ulift.symm
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro a b
  constructor
  · intro hk
    have hne_img : e a ≠ e b := by
      simpa [CompleteFourEndpoint.K4LiftGraph] using hk
    exact hcomplete a b (by
      intro hab
      exact hne_img (by simp [e, hab]))
  · intro hab
    have hne : a ≠ b := by
      intro h
      subst b
      exact G.loopless.irrefl a hab
    have hne_img : e a ≠ e b := by
      intro h
      exact hne (e.injective h)
    simpa [CompleteFourEndpoint.K4LiftGraph] using hne_img

/-- Complete four-vertex branch of the non-circular embedding target. -/
theorem HasEulerRotationSystem.of_complete_card_eq_four
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcomplete : ∀ x y : V, x ≠ y → G.Adj x y)
    (hcard : Fintype.card V = 4) :
    HasEulerRotationSystem G := by
  classical
  letI : DecidableRel (CompleteFourEndpoint.K4LiftGraph.{u}).Adj :=
    CompleteFourEndpoint.k4LiftGraphDecidableRel
  exact
    HasEulerRotationSystem.of_iso
      (completeCardFourIsoK4Lift (G := G) hcomplete hcard)
      CompleteFourEndpoint.exists_eulerRotationSystem.{u}

/-- Connected induction branch for a degree-at-most-one vertex.  If the
low-degree vertex is isolated, connectedness makes the graph a singleton; if
it is incident to an edge, the checked degree-one contraction lift applies. -/
theorem HasEulerRotationSystem.of_preconnected_forall_collapseEdge_of_exists_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected)
    (hdegree : Exists fun v : V => G.degree v <= 1)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        HasEulerRotationSystem (GraphContraction.collapseEdge G hab).graph) :
    HasEulerRotationSystem G := by
  classical
  rcases hdegree with ⟨v, hvdeg⟩
  by_cases hincident : Exists fun w : V => G.Adj v w
  · exact
      HasEulerRotationSystem.of_incident_collapseEdge_of_degree_le_one
        (G := G) (v := v) hvdeg hincident (by
          intro w hvw
          exact hcontract hvw)
  · have hvzero : G.degree v = 0 := by
      exact Nat.eq_zero_of_not_pos (by
        intro hpos
        exact hincident ((G.degree_pos_iff_exists_adj v).mp hpos))
    haveI : Subsingleton V := ⟨by
      intro x y
      have hxv : x = v := by
        by_contra hxv
        exact
          (SimpleGraph.not_reachable_of_right_degree_zero
            (G := G) hxv hvzero) (hG x v)
      have hyv : y = v := by
        by_contra hyv
        exact
          (SimpleGraph.not_reachable_of_right_degree_zero
            (G := G) hyv hvzero) (hG y v)
      exact hxv.trans hyv.symm⟩
    exact HasEulerRotationSystem.of_card_le_one (G := G)
      (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)

/-- Connected induction branch for a degree-at-most-two vertex.  Vertices of
degree at most one are handled by the leaf/singleton branch; otherwise the
vertex has exact degree two and the checked subdivision/triangle contraction
lift applies to any incident edge. -/
theorem HasEulerRotationSystem.of_preconnected_forall_collapseEdge_of_exists_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected)
    (hdegree : Exists fun v : V => G.degree v <= 2)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        HasEulerRotationSystem (GraphContraction.collapseEdge G hab).graph) :
    HasEulerRotationSystem G := by
  classical
  rcases hdegree with ⟨v, hvdeg⟩
  by_cases hleaf : G.degree v <= 1
  · exact
      HasEulerRotationSystem.of_preconnected_forall_collapseEdge_of_exists_degree_le_one
        (G := G) hG ⟨v, hleaf⟩ (by
          intro a b hab
          exact hcontract hab)
  · have hincident : Exists fun w : V => G.Adj v w := by
      have hpos : 0 < G.degree v := by omega
      exact (G.degree_pos_iff_exists_adj v).mp hpos
    exact
      HasEulerRotationSystem.of_incident_collapseEdge_of_degree_two
        (G := G) (v := v) hvdeg hleaf hincident (by
          intro w hvw
          exact hcontract hvw)

/-- Induction-ready low-degree branch for the non-circular embedding target.
If `G` is planar in the strict-Kuratowski sense, has a vertex of degree at
most two, and the recursive theorem is already available for every planar edge
contraction, then `G` has an Euler-planar rotation system. -/
theorem HasEulerRotationSystem.of_isPlanar_preconnected_forall_collapseEdge_of_exists_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    (hG : G.Preconnected)
    (hdegree : Exists fun v : V => G.degree v <= 2)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : Fintype (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetFintype G hab
        letI : DecidableEq (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetDecidableEq G hab
        letI : DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        IsPlanar (GraphContraction.collapseEdge G hab).graph →
          HasEulerRotationSystem (GraphContraction.collapseEdge G hab).graph) :
    HasEulerRotationSystem G := by
  classical
  exact
    HasEulerRotationSystem.of_preconnected_forall_collapseEdge_of_exists_degree_le_two
      (G := G) hG hdegree (by
        intro a b hab
        letI : Fintype (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetFintype G hab
        letI : DecidableEq (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetDecidableEq G hab
        letI : DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        exact hcontract hab (IsPlanar.collapseEdge h_planar hab))

/-- Connected induction step for the non-circular embedding target.  Low-degree
vertices are handled by the checked contraction lift; once all vertices have
degree at least three, the source theorem chooses one
deleted edge whose recursive embedding has cofacial endpoint pivots. -/
theorem HasEulerRotationSystem.of_isPlanar_preconnected_forall_collapseEdge_of_deleteEdge_cofacial
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    (hG : G.Preconnected)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : Fintype (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetFintype G hab
        letI : DecidableEq (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetDecidableEq G hab
        letI : DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        IsPlanar (GraphContraction.collapseEdge G hab).graph →
          HasEulerRotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hdelete :
      (forall v : V, 3 <= G.degree v) →
        Exists fun a : V =>
          Exists fun b : V =>
            Exists fun _hab : G.Adj a b =>
              IsPlanar (EdgeDeletion.deletedGraph G a b) →
                Exists fun R : RotationSystem (EdgeDeletion.deletedGraph G a b) =>
                  (R.toHypermap).dual.EulerPlanar ∧
                    Exists fun p : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                      Exists fun q : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                        p.tail = a ∧ q.tail = b ∧
                            EdgeDeletion.addEdgeCofacial R.toHypermap (some p) (some q)) :
    HasEulerRotationSystem G := by
  classical
  by_cases hlow : Exists fun v : V => G.degree v <= 2
  · exact
      HasEulerRotationSystem.of_isPlanar_preconnected_forall_collapseEdge_of_exists_degree_le_two
        (G := G) h_planar hG hlow hcontract
  · have hmin : forall v : V, 3 <= G.degree v := by
      intro v
      by_contra hlt
      exact hlow ⟨v, by omega⟩
    rcases hdelete hmin with ⟨a, b, hab, hdel⟩
    exact
      HasEulerRotationSystem.of_isPlanar_deleteEdge_of_exists_cofacial_pivots
        (G := G) h_planar hab hdel

/-- Connected non-complete four-vertex-or-smaller branch.  The graph has a
degree-at-most-two vertex; every incident contraction has at most three
vertices, so the completed degree-two contraction lift closes the case. -/
theorem HasEulerRotationSystem.of_preconnected_card_le_four_of_not_complete
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected)
    (hcard : Fintype.card V <= 4)
    (hnot_complete : Not (forall u v : V, u ≠ v -> G.Adj u v)) :
    HasEulerRotationSystem G := by
  classical
  exact
    HasEulerRotationSystem.of_preconnected_forall_collapseEdge_of_exists_degree_le_two
      (G := G) hG
      (exists_degree_le_two_of_card_le_four_of_not_complete
        (G := G) hcard hnot_complete)
      (by
        intro a b hab
        letI : Fintype (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetFintype G hab
        letI : DecidableEq (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetDecidableEq G hab
        letI : DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        have htarget :
            Fintype.card (GraphContraction.collapseEdge G hab).Target <= 3 := by
          have hlt :
              Fintype.card (GraphContraction.collapseEdge G hab).Target <
                Fintype.card V :=
            GraphContraction.collapseEdge_target_card_lt G hab
          omega
        exact
          HasEulerRotationSystem.of_card_le_three
            (G := (GraphContraction.collapseEdge G hab).graph) htarget)

/-- Every connected component of a finite disconnected graph has strictly
fewer vertices than the whole graph.  This is the disconnected case needed by
the final deletion-contraction induction measure. -/
theorem connectedComponent_card_lt_of_not_preconnected
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (hnot_preconnected : ¬ G.Preconnected)
    (C : G.ConnectedComponent) :
    letI : Fintype C := C.supp.toFinite.fintype
    Fintype.card C < Fintype.card V := by
  classical
  letI : Fintype C := C.supp.toFinite.fintype
  have hCcard : Fintype.card C = C.supp.ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq C.supp
  by_contra hnot_lt
  have huniv_le : (Set.univ : Set V).ncard <= C.supp.ncard := by
    have hcard_le : Fintype.card V <= C.supp.ncard := by omega
    simpa [Set.ncard_univ] using hcard_le
  have hC_univ : C.supp = Set.univ := by
    exact Set.eq_of_subset_of_ncard_le (Set.subset_univ C.supp) huniv_le
  have hpre : G.Preconnected := by
    intro x y
    have hx : x ∈ C.supp := by
      rw [hC_univ]
      exact Set.mem_univ x
    have hy : y ∈ C.supp := by
      rw [hC_univ]
      exact Set.mem_univ y
    exact C.reachable_of_mem_supp hx hy
  exact hnot_preconnected hpre

/-- In a non-preconnected graph on at most four vertices, every connected
component has at most three vertices. -/
theorem connectedComponent_card_le_three_of_card_le_four_of_not_preconnected
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (hcard : Fintype.card V <= 4)
    (hnot_preconnected : ¬ G.Preconnected)
    (C : G.ConnectedComponent) :
    letI : Fintype C := C.supp.toFinite.fintype
    Fintype.card C <= 3 := by
  classical
  letI : Fintype C := C.supp.toFinite.fintype
  have hCcard : Fintype.card C = C.supp.ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq C.supp
  by_contra hnot
  have hlarge : 4 <= C.supp.ncard := by
    have hcardC_gt : 3 < Fintype.card C := by omega
    omega
  have hC_univ : C.supp = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ C.supp)
    have huniv_le : (Set.univ : Set V).ncard <= C.supp.ncard := by
      have hcard_le : Fintype.card V <= C.supp.ncard := by omega
      simpa [Set.ncard_univ] using hcard_le
    exact huniv_le
  have hpre : G.Preconnected := by
    intro x y
    have hx : x ∈ C.supp := by
      rw [hC_univ]
      exact Set.mem_univ x
    have hy : y ∈ C.supp := by
      rw [hC_univ]
      exact Set.mem_univ y
    exact C.reachable_of_mem_supp hx hy
  exact hnot_preconnected hpre

/-- Non-complete four-vertex-or-smaller branch, with disconnected graphs
handled by component gluing and connected graphs by the degree-two contraction
lift. -/
theorem HasEulerRotationSystem.of_card_le_four_of_not_complete
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 4)
    (hnot_complete : Not (forall u v : V, u ≠ v -> G.Adj u v)) :
    HasEulerRotationSystem G := by
  classical
  by_cases hG : G.Preconnected
  · exact
      HasEulerRotationSystem.of_preconnected_card_le_four_of_not_complete
        (G := G) hG hcard hnot_complete
  · exact
      HasEulerRotationSystem.of_connectedComponents (G := G) (by
        intro C
        letI : Fintype C := C.supp.toFinite.fintype
        letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
        have hCcard : Fintype.card C <= 3 :=
          connectedComponent_card_le_three_of_card_le_four_of_not_preconnected
            (G := G) hcard hG C
        exact HasEulerRotationSystem.of_card_le_three
          (G := C.toSimpleGraph) hCcard)

/-- Four-vertex-or-smaller base branch.  The non-complete case is reduced by
degree-two contraction; the sole remaining complete endpoint is the explicit
tetrahedral rotation system above. -/
theorem HasEulerRotationSystem.of_card_le_four
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 4) :
    HasEulerRotationSystem G := by
  classical
  by_cases hcomplete : ∀ x y : V, x ≠ y → G.Adj x y
  · by_cases hsmall : Fintype.card V <= 3
    · exact HasEulerRotationSystem.of_card_le_three (G := G) hsmall
    · have hcard_eq : Fintype.card V = 4 := by omega
      exact
        HasEulerRotationSystem.of_complete_card_eq_four
          (G := G) hcomplete hcard_eq
  · exact
      HasEulerRotationSystem.of_card_le_four_of_not_complete
        (G := G) hcard hcomplete

/-- Connected induction step with the small-cardinality endpoint discharged
before the source deleted-edge theorem is requested.  This is the intended
cardinal-induction interface: after the explicit four-vertex base and the
low-degree contraction branch, only the minimum-degree-three, larger-than-four
source proposition remains. -/
theorem HasEulerRotationSystem.of_isPlanar_preconnected_forall_collapseEdge_of_deleteEdge_cofacial_large
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    (hG : G.Preconnected)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : Fintype (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetFintype G hab
        letI : DecidableEq (GraphContraction.collapseEdge G hab).Target :=
          GraphContraction.collapseEdgeTargetDecidableEq G hab
        letI : DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        IsPlanar (GraphContraction.collapseEdge G hab).graph →
          HasEulerRotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hdelete :
      4 < Fintype.card V →
        (forall v : V, 3 <= G.degree v) →
          Exists fun a : V =>
            Exists fun b : V =>
              Exists fun _hab : G.Adj a b =>
                IsPlanar (EdgeDeletion.deletedGraph G a b) →
                  Exists fun R : RotationSystem (EdgeDeletion.deletedGraph G a b) =>
                    (R.toHypermap).dual.EulerPlanar ∧
                      Exists fun p : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                        Exists fun q : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                          p.tail = a ∧ q.tail = b ∧
                              EdgeDeletion.addEdgeCofacial R.toHypermap
                                (some p) (some q)) :
    HasEulerRotationSystem G := by
  classical
  by_cases hsmall : Fintype.card V <= 4
  · exact HasEulerRotationSystem.of_card_le_four (G := G) hsmall
  · exact
      HasEulerRotationSystem.of_isPlanar_preconnected_forall_collapseEdge_of_deleteEdge_cofacial
        (G := G) h_planar hG hcontract
        (fun hmin => hdelete (by omega) hmin)

end FourColor

end Schematic.Math.GraphTheory
