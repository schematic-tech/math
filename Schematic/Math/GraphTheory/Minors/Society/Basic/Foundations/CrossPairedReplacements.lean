import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.CrossEndpointReplacements

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- Lift a side cross to a larger society while replacing the two adjacent
endpoints `0,1` by two boundary tails.  The source-specific proof supplies the
pathness, disjointness, and internal-boundary checks; this constructor keeps
the endpoint bookkeeping and nontriviality argument in one place. -/
def Cross.lift_replaceEndpoints01_with_tails
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    {a0 a1 : V}
    (q0 : S.graph.Walk (X.endpoints.endpoint 0) a0)
    (q1 : S.graph.Walk (X.endpoints.endpoint 1) a1)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoints01 a0 a1 i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoints01 a0 a1))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoints01 a0 a1))
    (hfirst_path :
      (q0.reverse.append (X.firstPath.mapLe hgraph)).IsPath)
    (hsecond_path :
      (q1.reverse.append (X.secondPath.mapLe hgraph)).IsPath)
    (hpaths_disjoint :
      Disjoint
        {v : V | v ∈ (q0.reverse.append
          (X.firstPath.mapLe hgraph)).support}
        {v : V | v ∈ (q1.reverse.append
          (X.secondPath.mapLe hgraph)).support})
    (hfirst_internal :
      Walk.InternalVertices
          (q0.reverse.append (X.firstPath.mapLe hgraph)) ∩
        S.boundarySet = ∅)
    (hsecond_internal :
      Walk.InternalVertices
          (q1.reverse.append (X.secondPath.mapLe hgraph)) ∩
        S.boundarySet = ∅) :
    S.Cross := by
  classical
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe hgraph
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe hgraph
  let firstNew : S.graph.Walk a0 (X.endpoints.endpoint 2) :=
    q0.reverse.append p
  let secondNew : S.graph.Walk a1 (X.endpoints.endpoint 3) :=
    q1.reverse.append r
  refine Cross.ofPaths {
      endpoint := X.replaceEndpoints01 a0 a1
      endpoint_mem := hendpoint_mem
      endpoint_injective := hendpoint_injective
      cyclic_alternating := halternating
    } ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [firstNew, p, Cross.replaceEndpoints01]
  · simpa [secondNew, r, Cross.replaceEndpoints01]
  · simpa [firstNew, p] using hfirst_path
  · simpa [secondNew, r] using hsecond_path
  · change
      Disjoint
        {v : V | v ∈ (q0.reverse.append
          (X.firstPath.mapLe hgraph)).support}
        {v : V | v ∈ (q1.reverse.append
          (X.secondPath.mapLe hgraph)).support}
    exact hpaths_disjoint
  · simpa [firstNew, p] using hfirst_internal
  · simpa [secondNew, r] using hsecond_internal

/-- Lift a side cross while replacing adjacent endpoints `1,2` by boundary
tails. -/
def Cross.lift_replaceEndpoints12_with_tails
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    {a1 a2 : V}
    (q1 : S.graph.Walk (X.endpoints.endpoint 1) a1)
    (q2 : S.graph.Walk (X.endpoints.endpoint 2) a2)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoints12 a1 a2 i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoints12 a1 a2))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoints12 a1 a2))
    (hfirst_path :
      ((X.firstPath.mapLe hgraph).append q2).IsPath)
    (hsecond_path :
      (q1.reverse.append (X.secondPath.mapLe hgraph)).IsPath)
    (hpaths_disjoint :
      Disjoint
        {v : V | v ∈ ((X.firstPath.mapLe hgraph).append q2).support}
        {v : V | v ∈ (q1.reverse.append
          (X.secondPath.mapLe hgraph)).support})
    (hfirst_internal :
      Walk.InternalVertices ((X.firstPath.mapLe hgraph).append q2) ∩
        S.boundarySet = ∅)
    (hsecond_internal :
      Walk.InternalVertices
          (q1.reverse.append (X.secondPath.mapLe hgraph)) ∩
        S.boundarySet = ∅) :
    S.Cross := by
  classical
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe hgraph
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe hgraph
  let firstNew : S.graph.Walk (X.endpoints.endpoint 0) a2 :=
    p.append q2
  let secondNew : S.graph.Walk a1 (X.endpoints.endpoint 3) :=
    q1.reverse.append r
  refine Cross.ofPaths {
      endpoint := X.replaceEndpoints12 a1 a2
      endpoint_mem := hendpoint_mem
      endpoint_injective := hendpoint_injective
      cyclic_alternating := halternating
    } ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [firstNew, p, Cross.replaceEndpoints12]
  · simpa [secondNew, r, Cross.replaceEndpoints12]
  · simpa [firstNew, p] using hfirst_path
  · simpa [secondNew, r] using hsecond_path
  · change
      Disjoint
        {v : V | v ∈ ((X.firstPath.mapLe hgraph).append q2).support}
        {v : V | v ∈ (q1.reverse.append
          (X.secondPath.mapLe hgraph)).support}
    exact hpaths_disjoint
  · simpa [firstNew, p] using hfirst_internal
  · simpa [secondNew, r] using hsecond_internal

/-- Lift a side cross while replacing adjacent endpoints `2,3` by boundary
tails. -/
def Cross.lift_replaceEndpoints23_with_tails
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    {a2 a3 : V}
    (q2 : S.graph.Walk (X.endpoints.endpoint 2) a2)
    (q3 : S.graph.Walk (X.endpoints.endpoint 3) a3)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoints23 a2 a3 i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoints23 a2 a3))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoints23 a2 a3))
    (hfirst_path :
      ((X.firstPath.mapLe hgraph).append q2).IsPath)
    (hsecond_path :
      ((X.secondPath.mapLe hgraph).append q3).IsPath)
    (hpaths_disjoint :
      Disjoint
        {v : V | v ∈ ((X.firstPath.mapLe hgraph).append q2).support}
        {v : V | v ∈ ((X.secondPath.mapLe hgraph).append q3).support})
    (hfirst_internal :
      Walk.InternalVertices ((X.firstPath.mapLe hgraph).append q2) ∩
        S.boundarySet = ∅)
    (hsecond_internal :
      Walk.InternalVertices ((X.secondPath.mapLe hgraph).append q3) ∩
        S.boundarySet = ∅) :
    S.Cross := by
  classical
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe hgraph
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe hgraph
  let firstNew : S.graph.Walk (X.endpoints.endpoint 0) a2 :=
    p.append q2
  let secondNew : S.graph.Walk (X.endpoints.endpoint 1) a3 :=
    r.append q3
  refine Cross.ofPaths {
      endpoint := X.replaceEndpoints23 a2 a3
      endpoint_mem := hendpoint_mem
      endpoint_injective := hendpoint_injective
      cyclic_alternating := halternating
    } ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [firstNew, p, Cross.replaceEndpoints23]
  · simpa [secondNew, r, Cross.replaceEndpoints23]
  · simpa [firstNew, p] using hfirst_path
  · simpa [secondNew, r] using hsecond_path
  · change
      Disjoint
        {v : V | v ∈ ((X.firstPath.mapLe hgraph).append q2).support}
        {v : V | v ∈ ((X.secondPath.mapLe hgraph).append q3).support}
    exact hpaths_disjoint
  · simpa [firstNew, p] using hfirst_internal
  · simpa [secondNew, r] using hsecond_internal

/-- Lift a side cross while replacing adjacent endpoints `3,0` by boundary
tails. -/
def Cross.lift_replaceEndpoints30_with_tails
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    {a3 a0 : V}
    (q3 : S.graph.Walk (X.endpoints.endpoint 3) a3)
    (q0 : S.graph.Walk (X.endpoints.endpoint 0) a0)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoints30 a3 a0 i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoints30 a3 a0))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoints30 a3 a0))
    (hfirst_path :
      (q0.reverse.append (X.firstPath.mapLe hgraph)).IsPath)
    (hsecond_path :
      ((X.secondPath.mapLe hgraph).append q3).IsPath)
    (hpaths_disjoint :
      Disjoint
        {v : V | v ∈ (q0.reverse.append
          (X.firstPath.mapLe hgraph)).support}
        {v : V | v ∈ ((X.secondPath.mapLe hgraph).append q3).support})
    (hfirst_internal :
      Walk.InternalVertices
          (q0.reverse.append (X.firstPath.mapLe hgraph)) ∩
        S.boundarySet = ∅)
    (hsecond_internal :
      Walk.InternalVertices ((X.secondPath.mapLe hgraph).append q3) ∩
        S.boundarySet = ∅) :
    S.Cross := by
  classical
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe hgraph
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe hgraph
  let firstNew : S.graph.Walk a0 (X.endpoints.endpoint 2) :=
    q0.reverse.append p
  let secondNew : S.graph.Walk (X.endpoints.endpoint 1) a3 :=
    r.append q3
  refine Cross.ofPaths {
      endpoint := X.replaceEndpoints30 a3 a0
      endpoint_mem := hendpoint_mem
      endpoint_injective := hendpoint_injective
      cyclic_alternating := halternating
    } ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [firstNew, p, Cross.replaceEndpoints30]
  · simpa [secondNew, r, Cross.replaceEndpoints30]
  · simpa [firstNew, p] using hfirst_path
  · simpa [secondNew, r] using hsecond_path
  · change
      Disjoint
        {v : V | v ∈ (q0.reverse.append
          (X.firstPath.mapLe hgraph)).support}
        {v : V | v ∈ ((X.secondPath.mapLe hgraph).append q3).support}
    exact hpaths_disjoint
  · simpa [firstNew, p] using hfirst_internal
  · simpa [secondNew, r] using hsecond_internal


end GeneralSociety

end Schematic.Math.GraphTheory
