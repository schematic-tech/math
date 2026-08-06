import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Local degree criterion for the non-cut attachment condition.  If every
cycle vertex except a distinguished possible cut vertex has degree at most two
inside `G - p - q`, source minimum degree three forces those vertices to be
adjacent to one of the two deleted endpoints in the original graph. -/
theorem deleteEdgeEndsGraph_noncut_attach_of_cycle_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    {r : {w : V | w ∉ ({p, q} : Set V)}}
    (C : (deleteEdgeEndsGraph G p q).Walk r r)
    {v : {w : V | w ∉ ({p, q} : Set V)}}
    (hv : v ∈ C.support)
    (hdegree_le :
      forall t : {w : V | w ∉ ({p, q} : Set V)},
        t ∈ C.support -> t ≠ v ->
          (deleteEdgeEndsGraph G p q).degree t <= 2) :
    Exists fun v : {w : V | w ∉ ({p, q} : Set V)} =>
      v ∈ C.support ∧
        (forall t : {w : V | w ∉ ({p, q} : Set V)},
          t ∈ C.support -> t ≠ v ->
            G.Adj (t : V) p ∨ G.Adj (t : V) q) := by
  refine ⟨v, hv, ?_⟩
  intro t ht ht_ne
  exact
    deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
      (G := G) (x := p) (y := q) hmin t
      (hdegree_le t ht ht_ne)

/-- No-outside-contact form of the local non-cut attachment criterion.  This
is the end-cycle target needed from the block/cactus step: once all external
contacts of the selected cycle pass through the distinguished cut vertex,
theta-free chordlessness bounds the deleted degree of every other cycle
vertex, and source minimum degree supplies attachment to one of the two
deleted endpoints. -/
theorem deleteEdgeEndsGraph_noncut_attach_of_cycle_no_external_contact
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    {r : {w : V | w ∉ ({p, q} : Set V)}}
    (C : (deleteEdgeEndsGraph G p q).Walk r r)
    (hC : C.IsCycle)
    (hno : Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {v : {w : V | w ∉ ({p, q} : Set V)}}
    (hv : v ∈ C.support)
    (hcontact :
      forall {t w : {z : V | z ∉ ({p, q} : Set V)}},
        t ∈ C.support -> t ≠ v ->
          (deleteEdgeEndsGraph G p q).Adj t w -> w ∈ C.support) :
    Exists fun v : {w : V | w ∉ ({p, q} : Set V)} =>
      v ∈ C.support ∧
        (forall t : {w : V | w ∉ ({p, q} : Set V)},
          t ∈ C.support -> t ≠ v ->
            G.Adj (t : V) p ∨ G.Adj (t : V) q) := by
  exact
    deleteEdgeEndsGraph_noncut_attach_of_cycle_degree_le_two
      (G := G) hmin C hv (by
        intro t ht htv
        exact
          degree_le_two_of_cycle_no_external_contact_no_homeomorphicTheta
            (G := deleteEdgeEndsGraph G p q) C hC hno ht htv
            (by
              intro a b ha hav hab
              exact hcontact ha hav hab))

/-- Hanging-cycle contact form of the local non-cut attachment criterion.  If
vertices outside the selected cycle can contact the cycle only at the
distinguished vertex `v`, then every other cycle vertex has no outside
neighbour.  The no-external-contact criterion then supplies the
Makarychev/Skopenkov attachment witness. -/
theorem deleteEdgeEndsGraph_noncut_attach_of_hanging_cycle_contact
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    {r : {w : V | w ∉ ({p, q} : Set V)}}
    (C : (deleteEdgeEndsGraph G p q).Walk r r)
    (hC : C.IsCycle)
    (hno : Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {v : {w : V | w ∉ ({p, q} : Set V)}}
    (hv : v ∈ C.support)
    (hcontact :
      forall {t c : {z : V | z ∉ ({p, q} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G p q).Adj t c -> c = v) :
    Exists fun v : {w : V | w ∉ ({p, q} : Set V)} =>
      v ∈ C.support ∧
        (forall t : {w : V | w ∉ ({p, q} : Set V)},
          t ∈ C.support -> t ≠ v ->
            G.Adj (t : V) p ∨ G.Adj (t : V) q) := by
  exact
    deleteEdgeEndsGraph_noncut_attach_of_cycle_no_external_contact
      (G := G) hmin C hC hno hv (by
        intro t w ht htv htw
        by_contra hw
        exact htv (hcontact hw ht htw.symm))

/-- Local connected-cycle exit for the Makarychev/Skopenkov graph side.  A
spanning cycle in a theta-free two-end deletion is chordless and hence
two-regular; the source minimum degree then forces every cycle vertex, except
for a harmless distinguished basepoint, to attach to one of the deleted
endpoints. -/
theorem deleteEdgeEndsGraph_noncut_attach_of_spanning_cycle_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    {r : {w : V | w ∉ ({p, q} : Set V)}}
    (C : (deleteEdgeEndsGraph G p q).Walk r r)
    (hC : C.IsCycle)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hno : Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q))) :
    Exists fun v : {w : V | w ∉ ({p, q} : Set V)} =>
      v ∈ C.support ∧
        (forall t : {w : V | w ∉ ({p, q} : Set V)},
          t ∈ C.support -> t ≠ v ->
            G.Adj (t : V) p ∨ G.Adj (t : V) q) := by
  classical
  have hdegree_pq :
      forall z : {w : V | w ∉ ({p, q} : Set V)},
        (deleteEdgeEndsGraph G p q).degree z = 2 :=
    degree_eq_two_of_spanning_cycle_no_homeomorphicTheta
      (G := deleteEdgeEndsGraph G p q) C hC hspanning hno
  exact
    deleteEdgeEndsGraph_noncut_attach_of_cycle_degree_le_two
      (G := G) hmin C C.start_mem_support (by
        intro t _ht _ht_ne
        have htdeg := hdegree_pq t
        omega)
end FourColor

end Schematic.Math.GraphTheory
