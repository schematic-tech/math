import Schematic.Math.GraphTheory.Embedding.Kuratowski.HangingCycles
import Schematic.Math.GraphTheory.Embedding.Kuratowski.InterfaceReductions

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- The local non-cut attachment cycle target implies the preferred
spanning-cycle target.  The proof is exactly the checked source spanning
lemma: minimum deleted degree two rules out all vertices outside such a cycle,
and the result is repackaged as `C.toSubgraph.verts = Set.univ`. -/
theorem DeleteEdgeEndsSpanningCyclesObstructionTheorem.of_noncutAttachCycles
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hno hdegree_ge p q hpq
  classical
  rcases hcycles hG hlarge hmin hno hdegree_ge hpq with
    ⟨r, C, hC, v, hv, hattach⟩
  have hspans :
      forall t : {w : V | w ∉ ({p, q} : Set V)}, t ∈ C.support :=
    deleteEdgeEndsGraph_cycle_spans_of_degree_ge_two_of_noncut_vertices_attach
      (G := G) hno hpq C hC hv hattach (hdegree_ge hpq)
  have hspanning : C.toSubgraph.verts = Set.univ := by
    ext t
    constructor
    · intro _ht
      exact Set.mem_univ t
    · intro _ht
      exact C.mem_verts_toSubgraph.mpr (hspans t)
  exact ⟨r, C, hC, hspanning⟩

/-- The reference-faithful spanning-cycle package follows from the proved
non-cut-attachment production theorem and the checked spanning endpoint. -/
theorem deleteEdgeEnds_spanningCycles_obstruction :
    DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u} :=
  DeleteEdgeEndsSpanningCyclesObstructionTheorem.of_noncutAttachCycles
    deleteEdgeEnds_noncutAttachCycles_obstruction

/-- A concrete dart-level theta theorem supplies the packaged
contraction-aware theta/cofacial theorem. -/
theorem CofacialDeletionThetaForcesWithContractionTheorem.of_darts
    (hdarts : CofacialDeletionThetaDartsWithContractionTheorem.{u}) :
    CofacialDeletionThetaForcesWithContractionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin a b hab hcontract hdeleted htheta
  rcases hdeleted with ⟨R, hR⟩
  rcases hdarts hG hlarge hmin hab hcontract R hR htheta with
    ⟨p, q, hp, hq, hcofacial⟩
  exact ⟨R, hR, p, q, hp, hq, hcofacial⟩

/-- The contraction-drawing theta embedding target implies the older
theta-forces-cofacial target by ignoring the arbitrary deleted-edge rotation
system supplied by induction.  This is the preferred reference-faithful route:
the embedding can be rebuilt from `G / ab` rather than forced into a fixed
rotation system for `G - ab`. -/
theorem CofacialDeletionThetaForcesWithContractionTheorem.of_embedding
    (hembed : CofacialDeletionThetaEmbeddingWithContractionTheorem.{u}) :
    CofacialDeletionThetaForcesWithContractionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin a b hab hcontract _hdeleted htheta
  exact hembed hG hlarge hmin hab hcontract htheta

/-- The graph and topology contracts imply the obstruction theorem.
First, theta-forces-cofacial turns extension failure into theta-free
two-end deletions.  Then the block/cactus production theorem supplies exactly
the hypotheses of the existing strict `K5`/`K3,3` extraction endpoint. -/
theorem CofacialDeletionObstructionTheorem.of_thetaForces_blockProduction
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hblock : DeleteEdgeEndsBlockProductionTheorem.{u}) :
    CofacialDeletionObstructionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hdeleted hnoco
  classical
  have hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)) := by
    intro p q hpq htheta_pq
    exact hnoco hpq
      (htheta hG hlarge hmin hpq (hdeleted hpq) htheta_pq)
  rcases hblock hG hlarge hmin hno with
    ⟨x, y, hxy, hdegree_delete, hblock_xy⟩
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_block_noncut_attach_alternative
      (G := G) hno hmin hxy hdegree_delete hblock_xy

/-- Theta-forces-cofacial plus the exact
degree-two deleted-end theorem already imply the obstruction theorem. -/
theorem CofacialDeletionObstructionTheorem.of_thetaForces_degreeTwo
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree : DeleteEdgeEndsDegreeTwoTheorem.{u}) :
    CofacialDeletionObstructionTheorem.{u} :=
  CofacialDeletionObstructionTheorem.of_thetaForces_blockProduction
    htheta (DeleteEdgeEndsBlockProductionTheorem.of_degreeTwo hdegree)

/-- Sound sharper obstruction reduction.  The degree theorem used here keeps
the obstruction-branch assumptions (`hdeleted` and `hnoco`), then the checked
two-regular connectedness and final-cycle extractor finish the strict
Kuratowski obstruction. -/
theorem CofacialDeletionObstructionTheorem.of_thetaForces_degreeTwoObstruction
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree : DeleteEdgeEndsDegreeTwoObstructionTheorem.{u}) :
    CofacialDeletionObstructionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hdeleted hnoco
  classical
  have hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)) := by
    intro p q hpq htheta_pq
    exact hnoco hpq
      (htheta hG hlarge hmin hpq (hdeleted hpq) htheta_pq)
  have hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2 := by
    intro p q hpq
    exact hdegree hG hlarge hmin hdeleted hnoco hno hpq
  rcases exists_adj_of_card_pos_min_degree_three
      (G := G) (by omega : 0 < Fintype.card V) hmin with
    ⟨x, y, hxy⟩
  have hconn : (deleteEdgeEndsGraph G x y).Preconnected :=
    deleteEdgeEndsGraph_preconnected_of_degree_eq_two
      (G := G) hno hmin hxy (hdegree_delete hxy)
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
      (G := G) hmin hxy hconn hdegree_delete

/-- Maximum-degree-two data plus no low-degree residue implies exact degree
two in the obstruction branch. -/
theorem DeleteEdgeEndsDegreeTwoObstructionTheorem.of_degreeLeTwo_noLow
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u})
    (hnolow : DeleteEdgeEndsNoLowDegreeObstructionTheorem.{u}) :
    DeleteEdgeEndsDegreeTwoObstructionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hdeleted hnoco hno p q hpq z
  have hle :
      (deleteEdgeEndsGraph G p q).degree z <= 2 :=
    hdegree_le hG hlarge hmin hdeleted hnoco hno hpq z
  have hnle :
      ¬ (deleteEdgeEndsGraph G p q).degree z <= 1 :=
    hnolow hG hlarge hmin hdeleted hnoco hno hpq z
  omega

/-- The local low-degree/cofacial face lemma closes the no-low-degree
obstruction target. -/
theorem DeleteEdgeEndsNoLowDegreeObstructionTheorem.of_lowDegreeForcesCofacial
    (hlow : DeleteEdgeEndsLowDegreeForcesCofacialTheorem.{u}) :
    DeleteEdgeEndsNoLowDegreeObstructionTheorem.{u} := by
  intro V _ _ G _ _hG _hlarge hmin hdeleted hnoco _hno p q hpq z hz
  exact hnoco hpq (hlow hmin hpq (hdeleted hpq) ⟨z, hz⟩)

/-- In the obstruction branch, every two-end deletion has minimum degree at
least two.  This is the degree half of the Skopenkov/Makarychev condition:
otherwise the local low-degree/cofacial theorem supplies the forbidden
cofacial deleted embedding. -/
theorem deleteEdgeEndsGraph_degree_ge_two_of_obstruction
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected)
    (hlarge : 4 < Fintype.card V)
    (hmin : forall v : V, 3 <= G.degree v)
    (hdeleted : ∀ {a b : V} (_hab : G.Adj a b),
      HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b))
    (hnoco : ∀ {a b : V} (_hab : G.Adj a b),
      ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b)
    (hno : forall {p q : V} (_hpq : G.Adj p q),
      Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {p q : V} (hpq : G.Adj p q)
    (z : {w : V | w ∉ ({p, q} : Set V)}) :
    2 <= (deleteEdgeEndsGraph G p q).degree z := by
  have hnolow :
      ¬ (deleteEdgeEndsGraph G p q).degree z <= 1 :=
    (DeleteEdgeEndsNoLowDegreeObstructionTheorem.of_lowDegreeForcesCofacial
      deleteEdgeEnds_lowDegree_forces_cofacial)
        hG hlarge hmin hdeleted hnoco hno hpq z
  omega

private theorem strictSubdivision_of_spanningCycles_obstruction
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected)
    (hlarge : 4 < Fintype.card V)
    (hmin : forall v : V, 3 <= G.degree v)
    (hdeleted : ∀ {a b : V} (_hab : G.Adj a b),
      HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b))
    (hnoco : ∀ {a b : V} (_hab : G.Adj a b),
      ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b)
    (hno : forall {p q : V} (_hpq : G.Adj p q),
      Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  have hdegree_ge :
      forall {p q : V} (_hpq : G.Adj p q),
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          2 <= (deleteEdgeEndsGraph G p q).degree z := by
    intro p q hpq z
    exact
      deleteEdgeEndsGraph_degree_ge_two_of_obstruction
        (G := G) hG hlarge hmin hdeleted hnoco hno hpq z
  have hcycles_all :
      forall {p q : V} (_hpq : G.Adj p q),
        Exists fun r : {w : V | w ∉ ({p, q} : Set V)} =>
          Exists fun C : (deleteEdgeEndsGraph G p q).Walk r r =>
            C.IsCycle ∧ C.toSubgraph.verts = Set.univ :=
    hcycles hG hlarge hmin hno hdegree_ge
  rcases exists_adj_of_card_pos_min_degree_three
      (G := G) (by omega : 0 < Fintype.card V) hmin with
    ⟨x, y, hxy⟩
  exact
    containsStrictSubdivision_K5_or_K33_of_all_deleteEdgeEnds_spanning_cycles_no_homeomorphicTheta
      (G := G) hno hmin hcycles_all hxy

/-- Reference-faithful obstruction reduction.  Theta-forces-cofacial gives the
no-theta side of the obstruction branch, the proved low-degree/cofacial lemma
gives minimum degree two in every two-end deletion, and the
Makarychev/Skopenkov spanning-cycle target supplies condition `(2)`.  The
checked endpoint then derives chordlessness, exact two-regularity, and the
strict `K5`/`K3,3` subdivision. -/
theorem CofacialDeletionObstructionTheorem.of_thetaForces_spanningCycles
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    CofacialDeletionObstructionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hdeleted hnoco
  classical
  have hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)) := by
    intro p q hpq htheta_pq
    exact hnoco hpq
      (htheta hG hlarge hmin hpq (hdeleted hpq) htheta_pq)
  exact
    strictSubdivision_of_spanningCycles_obstruction
      hG hlarge hmin hdeleted hnoco hno hcycles

/-- Reference-faithful obstruction reduction with the contraction embeddings
available to the theta step.  This is the preferred Makarychev/Skopenkov
route: a theta in `G - p - q` is discharged by the contraction-aware
face theorem; after that the already checked low-degree/cofacial lemma and
the spanning-cycle target give the strict Kuratowski obstruction. -/
theorem CofacialDeletionObstructionWithContractionTheorem.of_thetaForces_spanningCycles
    (htheta : CofacialDeletionThetaForcesWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    CofacialDeletionObstructionWithContractionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hcontract hdeleted hnoco
  classical
  have hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)) := by
    intro p q hpq htheta_pq
    exact hnoco hpq
      (htheta hG hlarge hmin hpq (hcontract hpq) (hdeleted hpq) htheta_pq)
  exact
    strictSubdivision_of_spanningCycles_obstruction
      hG hlarge hmin hdeleted hnoco hno hcycles

/-- Direct lowered-target obstruction reduction: the topology side works at
the concrete endpoint-dart level,
and the graph side only has to produce non-cut-attachment cycles. -/
theorem CofacialDeletionObstructionWithContractionTheorem.of_thetaDarts_noncutAttachCycles
    (hdarts : CofacialDeletionThetaDartsWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    CofacialDeletionObstructionWithContractionTheorem.{u} :=
  CofacialDeletionObstructionWithContractionTheorem.of_thetaForces_spanningCycles
    (CofacialDeletionThetaForcesWithContractionTheorem.of_darts hdarts)
    (DeleteEdgeEndsSpanningCyclesObstructionTheorem.of_noncutAttachCycles
      hcycles)

/-- Direct obstruction reduction from the contraction-drawing
theta embedding theorem and the proved graph-side non-cut-attachment cycle
target. -/
theorem CofacialDeletionObstructionWithContractionTheorem.of_thetaEmbedding_noncutAttachCycles
    (hembed : CofacialDeletionThetaEmbeddingWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    CofacialDeletionObstructionWithContractionTheorem.{u} :=
  CofacialDeletionObstructionWithContractionTheorem.of_thetaForces_spanningCycles
    (CofacialDeletionThetaForcesWithContractionTheorem.of_embedding hembed)
    (DeleteEdgeEndsSpanningCyclesObstructionTheorem.of_noncutAttachCycles
      hcycles)

/-- Reference-faithful obstruction reduction.  In the theta branch the
published gluing argument may choose a second edge deletion depending on the
boundary cycle, so the complete recursive edge-deletion family is passed to
the theta embedding theorem. -/
theorem CofacialDeletionObstructionWithContractionTheorem.of_referenceThetaEmbedding_noncutAttachCycles
    (hembed : CofacialDeletionThetaEmbeddingReferenceTheorem.{u})
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    CofacialDeletionObstructionWithContractionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hcontract hdeleted hnoco
  classical
  have hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)) := by
    intro p q hpq htheta_pq
    exact hnoco hpq
      (hembed hG hlarge hmin hdeleted hpq (hcontract hpq) htheta_pq)
  exact
    strictSubdivision_of_spanningCycles_obstruction
      hG hlarge hmin hdeleted hnoco hno
      (DeleteEdgeEndsSpanningCyclesObstructionTheorem.of_noncutAttachCycles
        hcycles)

/-- Final obstruction reduction from the split graph-side target:
theta-forces-cofacial plus maximum-degree-two/no-low-degree deleted-end data
imply the strict Kuratowski obstruction. -/
theorem CofacialDeletionObstructionTheorem.of_thetaForces_degreeLeTwo_noLow
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u})
    (hnolow : DeleteEdgeEndsNoLowDegreeObstructionTheorem.{u}) :
    CofacialDeletionObstructionTheorem.{u} :=
  CofacialDeletionObstructionTheorem.of_thetaForces_degreeTwoObstruction
    htheta
    (DeleteEdgeEndsDegreeTwoObstructionTheorem.of_degreeLeTwo_noLow
      hdegree_le hnolow)

/-- Final obstruction reduction using the local low-degree/cofacial face
lemma instead of taking no-low-degree as a separate target. -/
theorem CofacialDeletionObstructionTheorem.of_thetaForces_degreeLeTwo_lowDegreeForcesCofacial
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u})
    (hlow : DeleteEdgeEndsLowDegreeForcesCofacialTheorem.{u}) :
    CofacialDeletionObstructionTheorem.{u} :=
  CofacialDeletionObstructionTheorem.of_thetaForces_degreeLeTwo_noLow
    htheta hdegree_le
    (DeleteEdgeEndsNoLowDegreeObstructionTheorem.of_lowDegreeForcesCofacial
      hlow)

/-- Split bridge reduction from theta-forces-cofacial and the
maximum-degree-two graph theorem. -/
theorem CofacialDeletionObstructionTheorem.of_thetaForces_degreeLeTwo
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u}) :
    CofacialDeletionObstructionTheorem.{u} :=
  CofacialDeletionObstructionTheorem.of_thetaForces_degreeLeTwo_lowDegreeForcesCofacial
    htheta hdegree_le deleteEdgeEnds_lowDegree_forces_cofacial
end FourColor

end Schematic.Math.GraphTheory
