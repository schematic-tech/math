import Schematic.Math.GraphTheory.Embedding.Kuratowski.MinimumDegree
import Schematic.Math.GraphTheory.Embedding.Kuratowski.TheoremInterfaces

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem CofacialDeletionSourceTheorem.of_extension
    (hext : CofacialDeletionExtensionTheorem.{u}) :
    CofacialDeletionSourceTheorem.{u} := by
  intro V _ _ G _ hG h_planar hlarge hmin
  classical
  rcases exists_adj_of_card_pos_min_degree_three
      (G := G) (by omega : 0 < Fintype.card V) hmin with
    ⟨a, b, hab⟩
  exact ⟨a, b, hab, hext hG h_planar hlarge hmin hab⟩

private theorem all_deleted_and_not_cofacial_of_not_good_edge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnone : ¬ Exists fun a : V =>
      Exists fun b : V =>
        Exists fun _hab : G.Adj a b =>
          HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b) →
            EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b) :
    (∀ {a b : V} (_hab : G.Adj a b),
      HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b)) ∧
      (∀ {a b : V} (_hab : G.Adj a b),
        ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b) := by
  constructor
  · intro a b hab
    by_contra hnot_deleted
    exact hnone ⟨a, b, hab, fun hdeleted => False.elim (hnot_deleted hdeleted)⟩
  · intro a b hab hcofacial
    exact hnone ⟨a, b, hab, fun _hdeleted => hcofacial⟩

/-- The obstruction form implies the source theorem.  If no edge gives the
required cofacial deleted embedding, then each edge deletion is recursively
embedded and each such embedding fails cofacial extension; the obstruction
theorem produces a strict `K5`/`K3,3`, contradicting `IsPlanar`. -/
theorem CofacialDeletionSourceTheorem.of_obstruction
    (hobstruction : CofacialDeletionObstructionTheorem.{u}) :
    CofacialDeletionSourceTheorem.{u} := by
  intro V _ _ G _ hG h_planar hlarge hmin
  classical
  by_contra hnone
  rcases all_deleted_and_not_cofacial_of_not_good_edge hnone with
    ⟨hdeleted, hnoco⟩
  rcases hobstruction hG hlarge hmin hdeleted hnoco with hK5 | hK33
  · exact h_planar.no_K5_subdivision hK5
  · exact h_planar.no_K33_subdivision hK33

/-- Contraction-aware obstruction form implies the contraction-aware source
theorem.  The proof is the same minimal-counterexample contradiction as the
plain route, but it passes the recursive contraction embeddings to the
obstruction theorem. -/
theorem CofacialDeletionSourceWithContractionTheorem.of_obstructionWithContraction
    (hobstruction : CofacialDeletionObstructionWithContractionTheorem.{u}) :
    CofacialDeletionSourceWithContractionTheorem.{u} := by
  intro V _ _ G _ hG h_planar hlarge hmin hcontract
  classical
  by_contra hnone
  rcases all_deleted_and_not_cofacial_of_not_good_edge hnone with
    ⟨hdeleted, hnoco⟩
  rcases hobstruction hG hlarge hmin hcontract hdeleted hnoco with hK5 | hK33
  · exact h_planar.no_K5_subdivision hK5
  · exact h_planar.no_K33_subdivision hK33

/-- Exact degree-two deleted-end data implies the block-production target.
The hanging-cycle branch is unnecessary in this sharper route: once every
two-end deletion is exactly two-regular, the checked connectedness lemma gives
the connected branch for any source edge. -/
theorem DeleteEdgeEndsBlockProductionTheorem.of_degreeTwo
    (hdegree : DeleteEdgeEndsDegreeTwoTheorem.{u}) :
    DeleteEdgeEndsBlockProductionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hno
  classical
  rcases exists_adj_of_card_pos_min_degree_three
      (G := G) (by omega : 0 < Fintype.card V) hmin with
    ⟨x, y, hxy⟩
  have hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2 := by
    intro p q hpq
    exact hdegree hG hlarge hmin hno hpq
  have hconn : (deleteEdgeEndsGraph G x y).Preconnected :=
    deleteEdgeEndsGraph_preconnected_of_degree_eq_two
      (G := G) hno hmin hxy (hdegree_delete hxy)
  exact ⟨x, y, hxy, hdegree_delete, Or.inl hconn⟩

/-- Exact degree-two deleted-end data implies the reference-faithful
Makarychev/Skopenkov condition `(1) -> (2)` spanning-cycle formulation. -/
theorem DeleteEdgeEndsSpanningCyclesObstructionTheorem.of_degreeTwo
    (hdegree : DeleteEdgeEndsDegreeTwoTheorem.{u}) :
    DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hno _hdegree_ge p q hpq
  classical
  have hdegree_pq :
      forall z : {w : V | w ∉ ({p, q} : Set V)},
        (deleteEdgeEndsGraph G p q).degree z = 2 :=
    hdegree hG hlarge hmin hno hpq
  have hconn : (deleteEdgeEndsGraph G p q).Preconnected :=
    deleteEdgeEndsGraph_preconnected_of_degree_eq_two
      (G := G) hno hmin hpq hdegree_pq
  letI : Nonempty {w : V | w ∉ ({p, q} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin p q
  exact
    exists_cycle_toSubgraph_verts_eq_univ_of_preconnected_degree_eq_two
      (G := deleteEdgeEndsGraph G p q) hconn hdegree_pq

/-- Exact degree-two deleted-end data also supplies the non-cut-attachment
cycle target.  The spanning cycle comes from the two-regular connectedness
lemma; then every cycle vertex other than the distinguished basepoint has
deleted degree at most two, so original minimum degree three forces an
attachment to one of the two deleted endpoints. -/
theorem DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.of_degreeTwo
    (hdegree : DeleteEdgeEndsDegreeTwoTheorem.{u}) :
    DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hno _hdegree_ge p q hpq
  classical
  have hdegree_pq :
      forall z : {w : V | w ∉ ({p, q} : Set V)},
        (deleteEdgeEndsGraph G p q).degree z = 2 :=
    hdegree hG hlarge hmin hno hpq
  have hconn : (deleteEdgeEndsGraph G p q).Preconnected :=
    deleteEdgeEndsGraph_preconnected_of_degree_eq_two
      (G := G) hno hmin hpq hdegree_pq
  letI : Nonempty {w : V | w ∉ ({p, q} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin p q
  rcases
      exists_cycle_toSubgraph_verts_eq_univ_of_preconnected_degree_eq_two
        (G := deleteEdgeEndsGraph G p q) hconn hdegree_pq with
    ⟨r, C, hC, _hspanning⟩
  refine ⟨r, C, hC, r, C.start_mem_support, ?_⟩
  intro t _ht _ht_ne
  exact
    deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
      (G := G) (x := p) (y := q) hmin t (by
        have htdeg := hdegree_pq t
        omega)
end FourColor

end Schematic.Math.GraphTheory
