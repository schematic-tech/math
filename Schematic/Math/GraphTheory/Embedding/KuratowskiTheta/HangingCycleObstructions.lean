import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.UniqueCutLeaf

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- The spanning side of the hanging-cycle dichotomy immediately closes by the
already-checked final-cycle obstruction extraction.  After this theorem, the
only remaining local branch in Makarychev Lemma 3 is the unique cut-leaf
case, i.e. the source "3-prism" sentence. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_spans
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hspans :
      forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  have hspanning : C.toSubgraph.verts = Set.univ := by
    ext t
    constructor
    · intro _ht
      exact Set.mem_univ t
    · intro _ht
      exact C.mem_verts_toSubgraph.mpr (hspans t)
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_spanning_cycle_final
      (G := G) hmin C hC hxy hspanning hdegree_delete

/-- Source-attached cycle endpoint.  A deleted-end cycle with the
Makarychev/Skopenkov non-cut attachment condition already spans under minimum
deleted degree two, so the final-cycle Kuratowski extractor applies directly.
This is the preferred target for the block/cactus production step: it no
longer needs a global contact predicate or outside-component connectivity. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_cycle_degree_ge_two_of_noncut_vertices_attach
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hdegree_ge :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree t)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  have hspans :
      forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support :=
    deleteEdgeEndsGraph_cycle_spans_of_degree_ge_two_of_noncut_vertices_attach
      (G := G) hno hxy C hC hv hattach hdegree_ge
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_spans
      (G := G) hmin hxy C hC hspans hdegree_delete

/-- Source Lemma 3 hanging-cycle endpoint under Skopenkov condition (1).  The
minimum-degree-two deleted graph rules out the unique cut-leaf alternative
directly, so the hanging cycle spans and the final-cycle extractor produces a
strict Kuratowski subdivision. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hcontact :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v)
    (hdegree_ge :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree t)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  have hspans :
      forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support :=
    deleteEdgeEndsGraph_hanging_cycle_spans_of_degree_ge_two
      (G := G) hno hxy C hC hv hattach hcontact hdegree_ge
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_spans
      (G := G) hmin hxy C hC hspans hdegree_delete

/-- Hanging-cycle endpoint in the tighter source-derived contact form.  The
block/cactus proof only has to show that all outside vertices attach to the
displayed cut vertex `v`; the no-theta contact uniqueness and minimum deleted
degree then force the cycle to span, and the final-cycle extractor returns a
strict Kuratowski subdivision. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two_adj_contact
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hadj_contact :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∉ C.support -> (deleteEdgeEndsGraph G x y).Adj t v)
    (hdegree_ge :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree t)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  have hspans :
      forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support :=
    deleteEdgeEndsGraph_hanging_cycle_spans_of_degree_ge_two_adj_contact
      (G := G) hno hxy C hC hv hattach hadj_contact hdegree_ge
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_spans
      (G := G) hmin hxy C hC hspans hdegree_delete

/-- Hanging-cycle endpoint with the exact outside-component input produced by
the source block/cactus proof.  Once one outside vertex contacts the displayed
cut vertex `v` and the outside of the cycle is connected, the contact bridge
above derives adjacency to `v` for every outside vertex; minimum deleted degree
two then forces the hanging cycle to span, and the final-cycle Kuratowski
extractor applies. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two_connected_outside
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v p : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hp_outside : p ∉ C.support)
    (hpv : (deleteEdgeEndsGraph G x y).Adj p v)
    (houtside_preconnected :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).Preconnected)
    (hdegree_ge :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree t)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  have hadj_contact :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∉ C.support -> (deleteEdgeEndsGraph G x y).Adj t v :=
    deleteEdgeEndsGraph_outside_vertices_adj_contact_of_connected_outside
      (G := G) hno hxy C hC hv hattach hp_outside hpv
      houtside_preconnected
      (by
        intro t
        have ht := hdegree_ge t
        omega)
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two_adj_contact
      (G := G) hno hmin hxy C hC hv hattach hadj_contact
      hdegree_ge hdegree_delete

/-- Hanging-cycle endpoint with a named common outside component.  This is a
slightly more block-theoretic version of the connected-outside endpoint: the
end-block proof can name the outside component `K`, prove every off-cycle
vertex lies in it, and provide one contact to `v`; the contact bridge supplies
the all-outside adjacency needed by the final extraction. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two_common_external_component
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v p : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hp_outside : p ∉ C.support)
    (hpv : (deleteEdgeEndsGraph G x y).Adj p v)
    (K :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).ConnectedComponent)
    (hpK :
      (⟨p, hp_outside⟩ :
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hallK :
      forall (t : {w : V | w ∉ ({x, y} : Set V)}) (ht : t ∉ C.support),
        (⟨t, ht⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hdegree_ge :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree t)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  have hadj_contact :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∉ C.support -> (deleteEdgeEndsGraph G x y).Adj t v :=
    deleteEdgeEndsGraph_outside_vertices_adj_contact_of_common_external_component
      (G := G) hno hxy C hC hv hattach hp_outside hpv K hpK hallK
      (by
        intro t
        have ht := hdegree_ge t
        omega)
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two_adj_contact
      (G := G) hno hmin hxy C hC hv hattach hadj_contact
      hdegree_ge hdegree_delete

/-- Source Lemma 3 endpoint after the hanging-cycle/block reduction has supplied
one hanging cycle.  The unique cut-leaf alternative is now eliminated by
planarity, so the hanging cycle spans `G - x - y`; the already-checked final
cycle extractor then gives the strict Kuratowski subdivision. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_not_planar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hcontact :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  have hspans :
      forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support :=
    deleteEdgeEndsGraph_hanging_cycle_spans_of_not_planar
      (G := G) hnonplanar hno hmin hxy C hC hv hattach hcontact
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_spans
      (G := G) hmin hxy C hC hspans hdegree_delete


end FourColor

end Schematic.Math.GraphTheory
