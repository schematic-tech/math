import Schematic.Math.GraphTheory.Embedding.Kuratowski.DeletionContractionInduction

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionExtension
    (hext : CofacialDeletionExtensionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionSource
    (CofacialDeletionSourceTheorem.of_extension hext)

theorem hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    (hobstruction : CofacialDeletionObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionSource
    (CofacialDeletionSourceTheorem.of_obstruction hobstruction)

theorem hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstructionWithContraction
    (hobstruction : CofacialDeletionObstructionWithContractionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionSourceWithContraction
    (CofacialDeletionSourceWithContractionTheorem.of_obstructionWithContraction
      hobstruction)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaForces_blockProduction
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hblock : DeleteEdgeEndsBlockProductionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    (CofacialDeletionObstructionTheorem.of_thetaForces_blockProduction
      htheta hblock)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaForces_spanningCycles
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    (CofacialDeletionObstructionTheorem.of_thetaForces_spanningCycles
      htheta hcycles)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaForcesWithContraction_spanningCycles
    (htheta : CofacialDeletionThetaForcesWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstructionWithContraction
    (CofacialDeletionObstructionWithContractionTheorem.of_thetaForces_spanningCycles
      htheta hcycles)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaDartsWithContraction_spanningCycles
    (hdarts : CofacialDeletionThetaDartsWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_thetaForcesWithContraction_spanningCycles
    (CofacialDeletionThetaForcesWithContractionTheorem.of_darts hdarts)
    hcycles

theorem hasEulerRotationSystem_of_isPlanar_of_thetaDartsWithContraction_noncutAttachCycles
    (hdarts : CofacialDeletionThetaDartsWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstructionWithContraction
    (CofacialDeletionObstructionWithContractionTheorem.of_thetaDarts_noncutAttachCycles
      hdarts hcycles)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaEmbeddingWithContraction_noncutAttachCycles
    (hembed : CofacialDeletionThetaEmbeddingWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstructionWithContraction
    (CofacialDeletionObstructionWithContractionTheorem.of_thetaEmbedding_noncutAttachCycles
      hembed hcycles)

/-- Full bridge reduction from the exact two-embedding theorem used by
Makarychev and Skopenkov. -/
theorem hasEulerRotationSystem_of_isPlanar_of_referenceThetaEmbedding_noncutAttachCycles
    (hembed : CofacialDeletionThetaEmbeddingReferenceTheorem.{u})
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstructionWithContraction
    (CofacialDeletionObstructionWithContractionTheorem.of_referenceThetaEmbedding_noncutAttachCycles
      hembed hcycles)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeTwo
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree : DeleteEdgeEndsDegreeTwoTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    (CofacialDeletionObstructionTheorem.of_thetaForces_degreeTwo
      htheta hdegree)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeTwoObstruction
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree : DeleteEdgeEndsDegreeTwoObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    (CofacialDeletionObstructionTheorem.of_thetaForces_degreeTwoObstruction
      htheta hdegree)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeLeTwo_noLow
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u})
    (hnolow : DeleteEdgeEndsNoLowDegreeObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    (CofacialDeletionObstructionTheorem.of_thetaForces_degreeLeTwo_noLow
      htheta hdegree_le hnolow)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeLeTwo_lowDegreeForcesCofacial
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u})
    (hlow : DeleteEdgeEndsLowDegreeForcesCofacialTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    (CofacialDeletionObstructionTheorem.of_thetaForces_degreeLeTwo_lowDegreeForcesCofacial
      htheta hdegree_le hlow)

theorem hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeLeTwo
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    (CofacialDeletionObstructionTheorem.of_thetaForces_degreeLeTwo
      htheta hdegree_le)

/-- Contrapositive form of the Euler-rotation low-degree reduction.  A
connected minimal counterexample to the embedding bridge, once every incident
edge contraction has already been embedded, has minimum degree at least three.
This is the rotation-system counterpart of
`min_degree_three_of_not_planar_preconnected_forall_collapseEdge`. -/
theorem min_degree_three_of_not_hasEulerRotationSystem_preconnected_forall_collapseEdge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        HasEulerRotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hnot : ¬ HasEulerRotationSystem G) :
    forall v : V, 3 <= G.degree v := by
  intro v
  by_contra hlt
  have hvdeg : G.degree v <= 2 := by omega
  exact hnot
    (HasEulerRotationSystem.of_preconnected_forall_collapseEdge_of_exists_degree_le_two
      (G := G) hG ⟨v, hvdeg⟩ (by
        intro a b hab
        exact hcontract hab))
end FourColor

end Schematic.Math.GraphTheory
