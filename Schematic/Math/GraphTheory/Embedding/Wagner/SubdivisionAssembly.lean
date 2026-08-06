import Schematic.Math.GraphTheory.Subdivisions.Models

/-! Shared assembly of strict-subdivision models from explicit edge paths. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace Wagner

/-- Assemble a strict subdivision from its branch embedding and checked edge
paths.  The concrete Wagner obstructions share this model-building step but
have different finite route classifications. -/
theorem containsStrictSubdivision_of_edgePaths
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (branchVertex : W ↪ V)
    (edgePath : forall {x y : W}, H.Adj x y ->
      G.Walk (branchVertex x) (branchVertex y))
    (edgePath_isPath : forall {x y : W} (hxy : H.Adj x y),
      (edgePath hxy).IsPath)
    (no_internal_branch_vertices :
      forall {x y : W} (hxy : H.Adj x y) {z : V},
        z ∈ Walk.InternalVertices (edgePath hxy) ->
          forall w : W, z ≠ branchVertex w)
    (internally_disjoint_edge_paths :
      forall {x y x' y' : W}
        (hxy : H.Adj x y) (hx'y' : H.Adj x' y'),
          Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) ->
            Disjoint
              (Walk.InternalVertices (edgePath hxy))
              (Walk.InternalVertices (edgePath hx'y'))) :
    ContainsStrictSubdivision H G :=
  ⟨{
    toSubdivisionModel := {
      branchVertex := branchVertex
      branchVertex_injective := branchVertex.injective
      edgePath := edgePath
      edgePath_isPath := edgePath_isPath
      no_internal_branch_vertices := True
      internally_disjoint_edge_paths := True
    }
    no_internal_branch_vertices' := no_internal_branch_vertices
    internally_disjoint_edge_paths' := internally_disjoint_edge_paths
  }⟩

end Wagner

end FourColor

end Schematic.Math.GraphTheory
