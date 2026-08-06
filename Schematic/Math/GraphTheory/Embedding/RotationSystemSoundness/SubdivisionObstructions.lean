import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.SubdivisionInduction
import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Paths.Reflection

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph

namespace RotationSoundness

theorem not_hasEulerRotationSystem_of_strictSubdivision_K5_aux
    (n : Nat) :
    forall {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
      Fintype.card V = n ->
      StrictSubdivisionModel K5Graph G ->
      Not (HasEulerRotationSystem G) := by
  intro V _ _ G _ hcard M
  let hcontract :
      forall {X : Type u} [Fintype X] [DecidableEq X]
        {J : SimpleGraph X} [DecidableRel J.Adj]
        {v w : X} (hvw : J.Adj v w),
        J.degree v <= 2 ->
        ContainsStrictSubdivision K5Graph J ->
        ContainsStrictSubdivision K5Graph
          (GraphContraction.collapseEdge J hvw).graph :=
    fun hvw hdegree h =>
      ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_two
        hvw hdegree h
  exact not_hasEulerRotationSystem_of_strictSubdivision_of_contraction_closed
    (W := Fin 5) (H := K5Graph) K5Graph_isTwoConnected
    not_hasEulerRotationSystem_K5Graph hcontract n hcard M

theorem not_hasEulerRotationSystem_of_containsStrictSubdivision_K5
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ContainsStrictSubdivision K5Graph G) :
    Not (HasEulerRotationSystem G) :=
  not_hasEulerRotationSystem_of_strictSubdivision_K5_aux
    (Fintype.card V) rfl (Classical.choice h)

theorem not_hasEulerRotationSystem_of_strictSubdivision_K33_aux
    (n : Nat) :
    forall {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
      Fintype.card V = n ->
      StrictSubdivisionModel K33Graph G ->
      Not (HasEulerRotationSystem G) := by
  intro V _ _ G _ hcard M
  let hcontract :
      forall {X : Type u} [Fintype X] [DecidableEq X]
        {J : SimpleGraph X} [DecidableRel J.Adj]
        {v w : X} (hvw : J.Adj v w),
        J.degree v <= 2 ->
        ContainsStrictSubdivision K33Graph J ->
        ContainsStrictSubdivision K33Graph
          (GraphContraction.collapseEdge J hvw).graph :=
    fun hvw hdegree h =>
      ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_two
        hvw hdegree h
  exact
    not_hasEulerRotationSystem_of_strictSubdivision_of_contraction_closed
      (W := K33Vertex) (H := K33Graph) K33Graph_isTwoConnected
      not_hasEulerRotationSystem_K33Graph hcontract n hcard M

theorem not_hasEulerRotationSystem_of_containsStrictSubdivision_K33
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ContainsStrictSubdivision K33Graph G) :
    Not (HasEulerRotationSystem G) :=
  not_hasEulerRotationSystem_of_strictSubdivision_K33_aux
    (Fintype.card V) rfl (Classical.choice h)

end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
