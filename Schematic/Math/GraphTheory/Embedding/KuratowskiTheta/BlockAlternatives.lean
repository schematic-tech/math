import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.DegreeTwoStructure

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Skopenkov Lemma `(2) -> (3)` endpoint in a form that avoids taking exact
degree-two deletions as primitive data.  If every edge-end deletion is
presented as a spanning chordless cycle, each such deletion is exactly
two-regular, and the existing final-cycle extractor gives a strict
Kuratowski subdivision. -/
theorem containsStrictSubdivision_K5_or_K33_of_all_deleteEdgeEnds_spanning_chordless_cycles
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    (hcycles :
      forall {p q : V} (_hpq : G.Adj p q),
        Exists fun r : {w : V | w ∉ ({p, q} : Set V)} =>
          Exists fun C : (deleteEdgeEndsGraph G p q).Walk r r =>
            C.IsCycle ∧ C.IsChordless ∧ C.toSubgraph.verts = Set.univ)
    {x y : V}
    (hxy : G.Adj x y) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  have hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2 := by
    intro p q hpq
    rcases hcycles hpq with ⟨r, C, hC, hchordless, hspanning⟩
    exact
      degree_eq_two_of_spanning_isChordless_cycle
        (G := deleteEdgeEndsGraph G p q) C hC hspanning hchordless
  rcases hcycles hxy with ⟨r, C, hC, _hchordless, hspanning⟩
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_spanning_cycle_final
      (G := G) hmin C hC hxy hspanning hdegree_delete

/-- Skopenkov Lemma `(2) -> (3)` endpoint with chordlessness proved internally
from the no-theta edge-end deletion hypothesis.  This is the source-aligned
form used by the bridge: every edge-end deletion is a spanning cycle; a chord
in any one of those cycles would create a theta in that deletion, so every
deleted graph is two-regular and the final-cycle extractor returns a strict
Kuratowski subdivision. -/
theorem containsStrictSubdivision_K5_or_K33_of_all_deleteEdgeEnds_spanning_cycles_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    (hcycles :
      forall {p q : V} (_hpq : G.Adj p q),
        Exists fun r : {w : V | w ∉ ({p, q} : Set V)} =>
          Exists fun C : (deleteEdgeEndsGraph G p q).Walk r r =>
            C.IsCycle ∧ C.toSubgraph.verts = Set.univ)
    {x y : V}
    (hxy : G.Adj x y) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  have hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2 := by
    intro p q hpq
    rcases hcycles hpq with ⟨r, C, hC, hspanning⟩
    exact
      degree_eq_two_of_spanning_cycle_no_homeomorphicTheta
        (G := deleteEdgeEndsGraph G p q) C hC hspanning (hno hpq)
  rcases hcycles hxy with ⟨r, C, hC, hspanning⟩
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_spanning_cycle_final
      (G := G) hmin C hC hxy hspanning hdegree_delete

/-- Corollary of the source-aligned final obstruction theorem under the
weaker maximum-degree-two deletion hypothesis, provided Lemma 2 has already
supplied uniqueness of low-degree deleted vertices.  This is the local form
needed by the existing Makarychev branch; the cleaner theorem above is the
preferred bridge target. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_le_two_not_planar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hconn : (deleteEdgeEndsGraph G x y).Preconnected)
    (hmax :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z <= 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G :=
  containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
    (G := G) hmin hxy hconn
    (by
      intro p q hpq
      exact
        deleteEdgeEndsGraph_degree_eq_two_of_degree_le_two_not_planar
          (G := G) hnonplanar hno hmin hpq (hmax hpq))

/-- Degree-at-most-two deletion endpoint with connectedness discharged by the
source two-regular connectedness lemma. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_degree_le_two_not_planar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hmax :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z <= 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G :=
  containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_degree_eq_two
    (G := G) hno hmin hxy
    (by
      intro p q hpq
      exact
        deleteEdgeEndsGraph_degree_eq_two_of_degree_le_two_not_planar
          (G := G) hnonplanar hno hmin hpq (hmax hpq))

/-- Makarychev Lemma 3 after the block/cactus reduction has done its only
structural job.  The source proof has two exits for `G - x - y`: either it is
already the connected two-regular final cycle, or the block tree supplies a
hanging cycle with a unique possible contact vertex.  Both exits are now
checked constructively, and each returns an actual strict Kuratowski
subdivision in the original graph.

The remaining bridge work is therefore not another endpoint case here: it is
the upstream block/cactus theorem that supplies this disjunction from the
theta-free two-end deletions. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_block_alternative
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2)
    (hblock :
      (deleteEdgeEndsGraph G x y).Preconnected ∨
        Exists fun r : {w : V | w ∉ ({x, y} : Set V)} =>
          Exists fun C : (deleteEdgeEndsGraph G x y).Walk r r =>
            C.IsCycle ∧
              Exists fun v : {w : V | w ∉ ({x, y} : Set V)} =>
                v ∈ C.support ∧
                  (forall t : {w : V | w ∉ ({x, y} : Set V)},
                    t ∈ C.support -> t ≠ v ->
                      G.Adj (t : V) x ∨ G.Adj (t : V) y) ∧
                    (forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
                      t ∉ C.support -> c ∈ C.support ->
                        (deleteEdgeEndsGraph G x y).Adj t c -> c = v)) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  rcases hblock with hconn | hhang
  · exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
        (G := G) hmin hxy hconn hdegree_delete
  · rcases hhang with
      ⟨_r, C, hC, v, hv, hattach, hcontact⟩
    exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two
        (G := G) hno hmin hxy C hC hv hattach hcontact
        (by
          intro t
          have htdeg :
              (deleteEdgeEndsGraph G x y).degree t = 2 :=
            hdegree_delete hxy t
          omega)
        hdegree_delete

/-- Block-alternative endpoint in the source-derived contact form.  The
hanging-cycle branch asks only for a displayed cut contact `v` adjacent to all
outside vertices; no global contact predicate is assumed. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_block_adj_contact_alternative
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2)
    (hblock :
      (deleteEdgeEndsGraph G x y).Preconnected ∨
        Exists fun r : {w : V | w ∉ ({x, y} : Set V)} =>
          Exists fun C : (deleteEdgeEndsGraph G x y).Walk r r =>
            C.IsCycle ∧
              Exists fun v : {w : V | w ∉ ({x, y} : Set V)} =>
                v ∈ C.support ∧
                  (forall t : {w : V | w ∉ ({x, y} : Set V)},
                    t ∈ C.support -> t ≠ v ->
                      G.Adj (t : V) x ∨ G.Adj (t : V) y) ∧
                    (forall t : {w : V | w ∉ ({x, y} : Set V)},
                      t ∉ C.support ->
                        (deleteEdgeEndsGraph G x y).Adj t v)) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  rcases hblock with hconn | hhang
  · exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
        (G := G) hmin hxy hconn hdegree_delete
  · rcases hhang with
      ⟨_r, C, hC, v, hv, hattach, hadj_contact⟩
    exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two_adj_contact
      (G := G) hno hmin hxy C hC hv hattach hadj_contact
        (by
          intro t
          have htdeg :
              (deleteEdgeEndsGraph G x y).degree t = 2 :=
            hdegree_delete hxy t
          omega)
        hdegree_delete

/-- Block-alternative endpoint in the form now targeted by the source
block/cactus proof.  The hanging branch does not need the legacy global
contact predicate: it may either show directly that the displayed cycle spans,
or provide the connected outside component together with one contact to the
displayed cut vertex `v`.  The connected-outside contact bridge above then
derives the all-outside adjacency needed for the final extraction. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_block_spanning_or_connected_outside_alternative
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2)
    (hblock :
      (deleteEdgeEndsGraph G x y).Preconnected ∨
        Exists fun r : {w : V | w ∉ ({x, y} : Set V)} =>
          Exists fun C : (deleteEdgeEndsGraph G x y).Walk r r =>
            C.IsCycle ∧
              Exists fun v : {w : V | w ∉ ({x, y} : Set V)} =>
                v ∈ C.support ∧
                  (forall t : {w : V | w ∉ ({x, y} : Set V)},
                    t ∈ C.support -> t ≠ v ->
                      G.Adj (t : V) x ∨ G.Adj (t : V) y) ∧
                    ((forall t : {w : V | w ∉ ({x, y} : Set V)},
                        t ∈ C.support) ∨
                      Exists fun p : {w : V | w ∉ ({x, y} : Set V)} =>
                        p ∉ C.support ∧
                          (deleteEdgeEndsGraph G x y).Adj p v ∧
                          ((deleteEdgeEndsGraph G x y).induce
                            {z : {w : V | w ∉ ({x, y} : Set V)} |
                              z ∉ C.support}).Preconnected)) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  rcases hblock with hconn | hhang
  · exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
        (G := G) hmin hxy hconn hdegree_delete
  · rcases hhang with
      ⟨_r, C, hC, v, hv, hattach, hspans_or_connected⟩
    rcases hspans_or_connected with hspans | hconnected
    · exact
        containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_spans
          (G := G) hmin hxy C hC hspans hdegree_delete
    · rcases hconnected with ⟨p, hp_outside, hpv, houtside_preconnected⟩
      exact
        containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_degree_ge_two_connected_outside
          (G := G) hno hmin hxy C hC hv hattach hp_outside hpv
          houtside_preconnected
          (by
            intro t
            have htdeg :
                (deleteEdgeEndsGraph G x y).degree t = 2 :=
              hdegree_delete hxy t
            omega)
          hdegree_delete

/-- Simplified block-alternative endpoint after the strong source-attached
cycle spanning lemma.  The remaining block/cactus production step only needs
to find, for `G - x - y`, either a connected deletion or a cycle `C` with a
single distinguished vertex `v` such that every other vertex of `C` attaches
to one deleted endpoint.  Minimum deleted degree two and the checked theta
obstructions force that cycle to span automatically. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_block_noncut_attach_alternative
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2)
    (hblock :
      (deleteEdgeEndsGraph G x y).Preconnected ∨
        Exists fun r : {w : V | w ∉ ({x, y} : Set V)} =>
          Exists fun C : (deleteEdgeEndsGraph G x y).Walk r r =>
            C.IsCycle ∧
              Exists fun v : {w : V | w ∉ ({x, y} : Set V)} =>
                v ∈ C.support ∧
                  (forall t : {w : V | w ∉ ({x, y} : Set V)},
                    t ∈ C.support -> t ≠ v ->
                      G.Adj (t : V) x ∨ G.Adj (t : V) y)) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  rcases hblock with hconn | hcycle
  · exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
        (G := G) hmin hxy hconn hdegree_delete
  · rcases hcycle with ⟨_r, C, hC, v, hv, hattach⟩
    exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_cycle_degree_ge_two_of_noncut_vertices_attach
        (G := G) hno hmin hxy C hC hv hattach
        (by
          intro t
          have htdeg :
              (deleteEdgeEndsGraph G x y).degree t = 2 :=
            hdegree_delete hxy t
          omega)
        hdegree_delete

/-- Source-facing block-alternative endpoint in the non-planar form.  This is
the preferred Makarychev/Skopenkov bridge target after the rebased unique-leaf
branch has been checked: the block/cactus production theorem only has to
produce either a connected deletion or a cycle with the source non-cut
attachment condition.  The hanging-cycle branch no longer needs a separate
minimum deleted degree argument to prove spanning; non-planarity eliminates
the unique-leaf residue internally. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_block_noncut_attach_not_planar_alternative
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2)
    (hblock :
      (deleteEdgeEndsGraph G x y).Preconnected ∨
        Exists fun r : {w : V | w ∉ ({x, y} : Set V)} =>
          Exists fun C : (deleteEdgeEndsGraph G x y).Walk r r =>
            C.IsCycle ∧
              Exists fun v : {w : V | w ∉ ({x, y} : Set V)} =>
                v ∈ C.support ∧
                  (forall t : {w : V | w ∉ ({x, y} : Set V)},
                    t ∈ C.support -> t ≠ v ->
                      G.Adj (t : V) x ∨ G.Adj (t : V) y)) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  rcases hblock with hconn | hcycle
  · exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
        (G := G) hmin hxy hconn hdegree_delete
  · rcases hcycle with ⟨_r, C, hC, v, hv, hattach⟩
    exact
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_cycle_noncut_attach_not_planar
        (G := G) hnonplanar hno hmin hxy C hC hv hattach hdegree_delete


end FourColor

end Schematic.Math.GraphTheory
