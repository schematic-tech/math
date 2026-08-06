import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Edge-extension formulation: every source edge can be deleted and
re-embedded with cofacial endpoint darts. -/
def CofacialDeletionExtensionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        IsPlanar G →
          4 < Fintype.card V →
            (forall v : V, 3 <= G.degree v) →
              ∀ {a b : V} (_hab : G.Adj a b),
                HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b) →
                  EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b

/-- Source formulation used by deletion-contraction induction.  In a
connected, large, minimum-degree-three planar graph, some edge deletion can be
embedded with cofacial endpoint insertion pivots. -/
def CofacialDeletionSourceTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        IsPlanar G →
          4 < Fintype.card V →
            (forall v : V, 3 <= G.degree v) →
              Exists fun a : V =>
                Exists fun b : V =>
                  Exists fun _hab : G.Adj a b =>
                    HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b) →
                      EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b

/-- Reference-faithful source theorem with the contraction embeddings carried
explicitly.  The Skopenkov/Makarychev theta branch uses a drawing of the
edge-contraction `G / ab`, so the source proposition available to the final
induction must retain the recursive contraction systems rather than only the
recursive edge-deletion systems. -/
def CofacialDeletionSourceWithContractionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        IsPlanar G →
          4 < Fintype.card V →
            (forall v : V, 3 <= G.degree v) →
              (∀ {a b : V} (hab : G.Adj a b),
                letI : DecidableRel
                    (GraphContraction.collapseEdge G hab).graph.Adj :=
                  Classical.decRel _
                HasEulerRotationSystem
                  (GraphContraction.collapseEdge G hab).graph) →
                Exists fun a : V =>
                  Exists fun b : V =>
                    Exists fun _hab : G.Adj a b =>
                      HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b) →
                        EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b

/-- Minimal-counterexample obstruction form of cofacial extension.  If every edge
deletion has already been embedded but no deleted embedding can place the two
source endpoints on a common face, then the original graph contains a strict
Kuratowski subdivision.

Unlike `CofacialDeletionSourceTheorem`, this statement does not assume
`IsPlanar G`; it concludes the strict `K5`/`K3,3` obstruction that contradicts
`IsPlanar`. -/
def CofacialDeletionObstructionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (∀ {a b : V} (_hab : G.Adj a b),
              HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b)) →
              (∀ {a b : V} (_hab : G.Adj a b),
                ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b) →
                ContainsStrictSubdivision K5Graph G ∨
                  ContainsStrictSubdivision K33Graph G

/-- Contraction-aware obstruction form.  This is the obstruction statement
aligned with the short Kuratowski proofs: in addition to recursive embeddings
of edge deletions, it records recursive embeddings of every edge contraction,
which are the embeddings used by the topological theta case. -/
def CofacialDeletionObstructionWithContractionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (∀ {a b : V} (hab : G.Adj a b),
              letI : DecidableRel
                  (GraphContraction.collapseEdge G hab).graph.Adj :=
                Classical.decRel _
              HasEulerRotationSystem
                (GraphContraction.collapseEdge G hab).graph) →
              (∀ {a b : V} (_hab : G.Adj a b),
                HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b)) →
                (∀ {a b : V} (_hab : G.Adj a b),
                  ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b) →
                  ContainsStrictSubdivision K5Graph G ∨
                    ContainsStrictSubdivision K33Graph G

/-- Face/theta conversion theorem.  In the
minimal-counterexample branch, a homeomorphic theta in `G - a - b` should let
one choose/rearrange the already constructed Euler-planar embedding of
`G - ab` so that endpoint darts at `a` and `b` are cofacial.  This is the
formal version of the topological face-boundary step used in the
Makarychev/Skopenkov proof. -/
def CofacialDeletionThetaForcesTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            ∀ {a b : V} (_hab : G.Adj a b),
              HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b) →
                ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b) →
                  EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b

/-- Contraction-aware theta/face conversion theorem: a theta in `G - a - b`
is handled using both
the recursive embedding of `G - ab` and the recursive embedding of the
contraction `G / ab`, matching the cited Skopenkov/Makarychev argument. -/
def CofacialDeletionThetaForcesWithContractionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            ∀ {a b : V} (hab : G.Adj a b),
              (letI : DecidableRel
                  (GraphContraction.collapseEdge G hab).graph.Adj :=
                Classical.decRel _
              HasEulerRotationSystem
                (GraphContraction.collapseEdge G hab).graph) →
                HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b) →
                  ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b) →
                    EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b

/-- Contraction-drawing form of the Makarychev/Skopenkov theta/face argument.
The topological argument starts
from a planar drawing/rotation system of the contraction `G / ab` and a theta
in `G - a - b`; it then constructs a deleted-edge embedding whose endpoint
darts are cofacial.  It does not need to preserve an arbitrary pre-existing
rotation system on `G - ab`. -/
def CofacialDeletionThetaEmbeddingWithContractionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            ∀ {a b : V} (hab : G.Adj a b),
              (letI : DecidableRel
                  (GraphContraction.collapseEdge G hab).graph.Adj :=
                Classical.decRel _
              HasEulerRotationSystem
                (GraphContraction.collapseEdge G hab).graph) →
                ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b) →
                  EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b

/-- Reference-faithful theta/face conversion target.  Makarychev's and
Skopenkov's proofs use two recursively planar graphs: the contraction
`G / ab`, which supplies the boundary cycle, and a proper edge deletion
`G - e` for an edge outside that boundary, which supplies the embedding to
be glued inside the cycle.  The obstruction branch already carries
Euler-planar rotation systems for every edge deletion.

The contraction-only theorem above is strictly stronger and is retained as
an optional interface, but it is not what the cited proof establishes. -/
def CofacialDeletionThetaEmbeddingReferenceTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (∀ {x y : V} (_hxy : G.Adj x y),
              HasEulerRotationSystem (EdgeDeletion.deletedGraph G x y)) →
              ∀ {a b : V} (hab : G.Adj a b),
                (letI : DecidableRel
                    (GraphContraction.collapseEdge G hab).graph.Adj :=
                  Classical.decRel _
                HasEulerRotationSystem
                  (GraphContraction.collapseEdge G hab).graph) →
                  ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b) →
                    EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b

/-- Concrete dart-level form of
`CofacialDeletionThetaForcesWithContractionTheorem`.  For a fixed recursive
rotation system on `G - ab`, the topology argument must find one dart at `a`
and one dart at `b` that lie on a common face. -/
def CofacialDeletionThetaDartsWithContractionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            ∀ {a b : V} (hab : G.Adj a b),
              (letI : DecidableRel
                  (GraphContraction.collapseEdge G hab).graph.Adj :=
                Classical.decRel _
              HasEulerRotationSystem
                (GraphContraction.collapseEdge G hab).graph) →
                (R : RotationSystem (EdgeDeletion.deletedGraph G a b)) →
                  (R.toHypermap).dual.EulerPlanar →
                    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b) →
                      Exists fun p : OrientedEdge
                          (EdgeDeletion.deletedGraph G a b) =>
                        Exists fun q : OrientedEdge
                            (EdgeDeletion.deletedGraph G a b) =>
                          p.tail = a ∧ q.tail = b ∧
                            EdgeDeletion.addEdgeCofacial R.toHypermap
                              (some p) (some q)

/-- Degree-two theorem for the graph side of the Makarychev/Skopenkov route:
every vertex surviving a theta-free edge-end deletion has degree exactly two. -/
def DeleteEdgeEndsDegreeTwoTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (forall {p q : V} (_hpq : G.Adj p q),
              Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q))) →
              forall {p q : V} (_hpq : G.Adj p q),
                forall z : {w : V | w ∉ ({p, q} : Set V)},
                  (deleteEdgeEndsGraph G p q).degree z = 2

/-- Obstruction-aware degree-two theorem for the graph side.  Unlike the
stronger pure no-theta formulation, it
retains the minimal-counterexample data that every edge deletion is already
embedded and that no deleted embedding has cofacial source endpoint darts. -/
def DeleteEdgeEndsDegreeTwoObstructionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (∀ {a b : V} (_hab : G.Adj a b),
              HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b)) →
              (∀ {a b : V} (_hab : G.Adj a b),
                ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b) →
                (forall {p q : V} (_hpq : G.Adj p q),
                  Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q))) →
                  forall {p q : V} (_hpq : G.Adj p q),
                    forall z : {w : V | w ∉ ({p, q} : Set V)},
                      (deleteEdgeEndsGraph G p q).degree z = 2

/-- Maximum-degree-two obstruction theorem for the graph side. -/
def DeleteEdgeEndsDegreeLeTwoObstructionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (∀ {a b : V} (_hab : G.Adj a b),
              HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b)) →
              (∀ {a b : V} (_hab : G.Adj a b),
                ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b) →
                (forall {p q : V} (_hpq : G.Adj p q),
                  Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q))) →
                  forall {p q : V} (_hpq : G.Adj p q),
                    forall z : {w : V | w ∉ ({p, q} : Set V)},
                      (deleteEdgeEndsGraph G p q).degree z <= 2

/-- No-low-degree obstruction target for the graph side.  This is the second
half of exact degree two: after maximum degree two has been proved, this rules
out the hanging-vertex residue in every two-end deletion. -/
def DeleteEdgeEndsNoLowDegreeObstructionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (∀ {a b : V} (_hab : G.Adj a b),
              HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b)) →
              (∀ {a b : V} (_hab : G.Adj a b),
                ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b) →
                (forall {p q : V} (_hpq : G.Adj p q),
                  Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q))) →
                  forall {p q : V} (_hpq : G.Adj p q),
                    forall z : {w : V | w ∉ ({p, q} : Set V)},
                      ¬ (deleteEdgeEndsGraph G p q).degree z <= 1

/-- Local face target for the no-low-degree obstruction branch.  If a
surviving vertex of `G - p - q` has degree at most one, then the
minimum-degree-three source hypotheses make it a hanging vertex adjacent to
both deleted endpoints.  Any
Euler-planar rotation system on `G - pq` can then be represented with
cofacial endpoint darts, contradicting the obstruction branch's no-cofacial
assumption. -/
def DeleteEdgeEndsLowDegreeForcesCofacialTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      (forall v : V, 3 <= G.degree v) →
        forall {p q : V} (_hpq : G.Adj p q),
          HasEulerRotationSystem (EdgeDeletion.deletedGraph G p q) →
            (Exists fun z : {w : V | w ∉ ({p, q} : Set V)} =>
              (deleteEdgeEndsGraph G p q).degree z <= 1) →
                EdgeDeletion.HasCofacialDeletedEmbedding (G := G) p q

/-- The local low-degree/cofacial theorem.  A degree-at-most-one survivor of
`G - p - q` is adjacent to both deleted endpoints and has original degree
three; after deleting only `pq`, the two endpoint darts into that survivor
share a head of degree at most three, so the rotation at that head puts
endpoint darts on a common face. -/
theorem deleteEdgeEnds_lowDegree_forces_cofacial :
    DeleteEdgeEndsLowDegreeForcesCofacialTheorem.{u} := by
  intro V _ _ G _ hmin p q hpq hdel hlow
  classical
  rcases hdel with ⟨R, hR⟩
  rcases hlow with ⟨z, hzlow⟩
  rcases deleteEdgeEndsGraph_hanging_vertex_of_min_degree_three
      (G := G) (x := p) (y := q) hmin z hzlow with
    ⟨_hzdel, hzp, hzq⟩
  have hzdegG : G.degree (z : V) = 3 :=
    deleteEdgeEndsGraph_hanging_vertex_original_degree_eq_three
      (G := G) (x := p) (y := q) hmin z hzlow
  have hzdegD :
      (EdgeDeletion.deletedGraph G p q).degree (z : V) <= 3 := by
    have hle :
        (EdgeDeletion.deletedGraph G p q).degree (z : V) <=
          G.degree (z : V) := by
      exact
        SimpleGraph.degree_le_of_le
          (G := EdgeDeletion.deletedGraph G p q) (H := G)
          (v := (z : V))
          (SimpleGraph.deleteEdges_le ({s(p, q)} : Set (Sym2 V)))
    omega
  rcases
      EdgeDeletion.exists_cofacial_endpointDarts_of_common_neighbor_degree_le_three
        (G := G) hpq hzp.symm hzq.symm R hzdegD with
    ⟨pD, qD, hpD, hqD, hcofacial⟩
  exact ⟨R, hR, pD, qD, hpD, hqD, hcofacial⟩

/-- Block/cactus production target for the graph side of the
Makarychev/Skopenkov route.  Once all two-end deletions are theta-free, this
provides the exact degree-two data and the connected-or-hanging-cycle
alternative consumed by the already checked strict `K5`/`K3,3` extractor. -/
def DeleteEdgeEndsBlockProductionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (forall {p q : V} (_hpq : G.Adj p q),
              Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q))) →
              Exists fun x : V =>
                Exists fun y : V =>
                  Exists fun _hxy : G.Adj x y =>
                    (forall {p q : V}, G.Adj p q ->
                      forall z : {w : V | w ∉ ({p, q} : Set V)},
                        (deleteEdgeEndsGraph G p q).degree z = 2) ∧
                    ((deleteEdgeEndsGraph G x y).Preconnected ∨
                      Exists fun r : {w : V | w ∉ ({x, y} : Set V)} =>
                        Exists fun C : (deleteEdgeEndsGraph G x y).Walk r r =>
                          C.IsCycle ∧
                            Exists fun v : {w : V | w ∉ ({x, y} : Set V)} =>
                              v ∈ C.support ∧
                                (forall t : {w : V | w ∉ ({x, y} : Set V)},
                                  t ∈ C.support -> t ≠ v ->
                                    G.Adj (t : V) x ∨ G.Adj (t : V) y))

/-- Reference-faithful Makarychev/Skopenkov Lemma `(1) -> (2)` target.
Given the no-theta condition and minimum degree at least two in every
two-end deletion, each such deletion is represented by a spanning simple
cycle.  Chordlessness and exact degree two are then derived by the already
checked endpoint lemmas, rather than assumed as primitive data. -/
def DeleteEdgeEndsSpanningCyclesObstructionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (forall {p q : V} (_hpq : G.Adj p q),
              Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q))) →
              (forall {p q : V} (_hpq : G.Adj p q),
                forall z : {w : V | w ∉ ({p, q} : Set V)},
                  2 <= (deleteEdgeEndsGraph G p q).degree z) →
                forall {p q : V} (_hpq : G.Adj p q),
                  Exists fun r : {w : V | w ∉ ({p, q} : Set V)} =>
                    Exists fun C : (deleteEdgeEndsGraph G p q).Walk r r =>
                      C.IsCycle ∧ C.toSubgraph.verts = Set.univ

/-- Block/cactus input to the reference-faithful spanning-cycle theorem.  It
asks for the exact local cycle that the Makarychev/Skopenkov
argument produces before the final spanning step: in every two-end deletion,
there is a simple cycle `C` and a distinguished possible cut vertex `v` such
that every other vertex of `C` attaches to one of the deleted endpoints. -/
def DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      G.Preconnected →
        4 < Fintype.card V →
          (forall v : V, 3 <= G.degree v) →
            (forall {p q : V} (_hpq : G.Adj p q),
              Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q))) →
              (forall {p q : V} (_hpq : G.Adj p q),
                forall z : {w : V | w ∉ ({p, q} : Set V)},
                  2 <= (deleteEdgeEndsGraph G p q).degree z) →
                forall {p q : V} (_hpq : G.Adj p q),
                  Exists fun r : {w : V | w ∉ ({p, q} : Set V)} =>
                    Exists fun C : (deleteEdgeEndsGraph G p q).Walk r r =>
                      C.IsCycle ∧
                        Exists fun v : {w : V | w ∉ ({p, q} : Set V)} =>
                          v ∈ C.support ∧
                            (forall t : {w : V | w ∉ ({p, q} : Set V)},
                              t ∈ C.support -> t ≠ v ->
                                G.Adj (t : V) p ∨ G.Adj (t : V) q)
end FourColor

end Schematic.Math.GraphTheory
