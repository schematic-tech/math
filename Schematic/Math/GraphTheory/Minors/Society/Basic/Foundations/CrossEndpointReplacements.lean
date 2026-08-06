import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.CrossCleanTails

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- Replace endpoint `2` of a lifted cross by a clean tail from an interior
point of the first cross path to a new society-boundary vertex.

This is the path-construction half of the GM IX `(2.4)` side-cross
`r = 1`/endpoint-replacement argument.  The caller still supplies the
cyclic-order and endpoint-injectivity facts for the new endpoint tuple, since
those are the source-specific order checks. -/
def Cross.lift_replaceEndpoint2_with_tail
    [DecidableEq V]
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint2 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hprefix_boundary :
      forall (hxS : x ∈ (X.firstPath.mapLe hgraph).support) (z : V),
        z ∈ ((X.firstPath.mapLe hgraph).takeUntil x hxS).support ->
          z ∈ S.boundarySet ->
            z = X.endpoints.endpoint 0 ∨ z = x)
    (hsecond_internal :
      Walk.InternalVertices (X.secondPath.mapLe hgraph) ∩ S.boundarySet =
        ∅) :
    S.Cross := by
  classical
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe hgraph
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe hgraph
  have hxS : x ∈ p.support := by
    simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hx
  let firstNew : S.graph.Walk (X.endpoints.endpoint 0) a :=
    (p.takeUntil x hxS).append q
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe hgraph X.firstPath_isPath
  have hr_path : r.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe hgraph X.secondPath_isPath
  have hfirst_path : firstNew.IsPath := by
    dsimp [firstNew]
    exact Walk.IsPath.takeUntil_append_of_clean hp_path hxS hq_path
      (by
        intro z hzq hzp
        exact hq_clean z hzq
          (Or.inl (by
            simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp)))
  have hdisjoint :
      Disjoint {v : V | v ∈ firstNew.support} {v : V | v ∈ r.support} := by
    rw [Set.disjoint_left]
    intro z hz_first hz_second
    have hz_second_X : z ∈ X.secondPath.support := by
      simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hz_second
    have hx_not_second : x ∉ X.secondPath.support := by
      intro hx_second
      exact Set.disjoint_left.mp X.paths_disjoint hx hx_second
    have hz_first' : z ∈ (p.takeUntil x hxS).support ∨ z ∈ q.support := by
      simpa [firstNew, SimpleGraph.Walk.mem_support_append_iff] using hz_first
    rcases hz_first' with hz_prefix | hzq
    · have hz_p : z ∈ p.support :=
        SimpleGraph.Walk.support_takeUntil_subset p hxS hz_prefix
      have hz_first_X : z ∈ X.firstPath.support := by
        simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hz_p
      exact Set.disjoint_left.mp X.paths_disjoint hz_first_X hz_second_X
    · have hzx : z = x := hq_clean z hzq (Or.inr hz_second_X)
      exact hx_not_second (by simpa [hzx] using hz_second_X)
  have hfirst_internal :
      Walk.InternalVertices firstNew ∩ S.boundarySet = ∅ := by
    dsimp [firstNew]
    exact Walk.InternalVertices.takeUntil_append_boundary_clean hxS
      (hprefix_boundary hxS) hq_boundary hx_not_boundary
  refine Cross.ofPaths {
      endpoint := X.replaceEndpoint2 a
      endpoint_mem := hendpoint_mem
      endpoint_injective := hendpoint_injective
      cyclic_alternating := halternating
    } ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [Cross.replaceEndpoint2] using firstNew
  · simpa [Cross.replaceEndpoint2] using r
  · simpa [Cross.replaceEndpoint2] using hfirst_path
  · simpa [Cross.replaceEndpoint2] using hr_path
  · simpa [Cross.replaceEndpoint2] using hdisjoint
  · simpa [Cross.replaceEndpoint2] using hfirst_internal
  · simpa [Cross.replaceEndpoint2] using hsecond_internal

/-- Symmetric endpoint-`0` version of
`Cross.lift_replaceEndpoint2_with_tail`: prepend the reversed clean tail to
the suffix of the first cross path from the last contact. -/
def Cross.lift_replaceEndpoint0_with_tail
    [DecidableEq V]
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint0 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hdrop_boundary :
      forall (hxS : x ∈ (X.firstPath.mapLe hgraph).support) (z : V),
        z ∈ ((X.firstPath.mapLe hgraph).dropUntil x hxS).support ->
          z ∈ S.boundarySet ->
            z = x ∨ z = X.endpoints.endpoint 2)
    (hsecond_internal :
      Walk.InternalVertices (X.secondPath.mapLe hgraph) ∩ S.boundarySet =
        ∅) :
    S.Cross := by
  classical
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe hgraph
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe hgraph
  have hxS : x ∈ p.support := by
    simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hx
  let firstNew : S.graph.Walk a (X.endpoints.endpoint 2) :=
    q.reverse.append (p.dropUntil x hxS)
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe hgraph X.firstPath_isPath
  have hr_path : r.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe hgraph X.secondPath_isPath
  have hfirst_path : firstNew.IsPath := by
    dsimp [firstNew]
    exact Walk.IsPath.reverse_append_dropUntil_of_clean hp_path hxS hq_path
      (by
        intro z hzq hzp
        exact hq_clean z hzq
          (Or.inl (by
            simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp)))
  have hdisjoint :
      Disjoint {v : V | v ∈ firstNew.support} {v : V | v ∈ r.support} := by
    rw [Set.disjoint_left]
    intro z hz_first hz_second
    have hz_second_X : z ∈ X.secondPath.support := by
      simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hz_second
    have hx_not_second : x ∉ X.secondPath.support := by
      intro hx_second
      exact Set.disjoint_left.mp X.paths_disjoint hx hx_second
    have hz_first' : z ∈ q.reverse.support ∨ z ∈ (p.dropUntil x hxS).support := by
      simpa [firstNew, SimpleGraph.Walk.mem_support_append_iff] using hz_first
    rcases hz_first' with hzq_rev | hz_drop
    · have hzq : z ∈ q.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzq_rev
        exact List.mem_reverse.mp hzq_rev
      have hzx : z = x := hq_clean z hzq (Or.inr hz_second_X)
      exact hx_not_second (by simpa [hzx] using hz_second_X)
    · have hz_p : z ∈ p.support :=
        SimpleGraph.Walk.support_dropUntil_subset p hxS hz_drop
      have hz_first_X : z ∈ X.firstPath.support := by
        simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hz_p
      exact Set.disjoint_left.mp X.paths_disjoint hz_first_X hz_second_X
  have hfirst_internal :
      Walk.InternalVertices firstNew ∩ S.boundarySet = ∅ := by
    dsimp [firstNew]
    exact Walk.InternalVertices.reverse_append_dropUntil_boundary_clean hxS
      (hdrop_boundary hxS) hq_boundary hx_not_boundary
  refine Cross.ofPaths {
      endpoint := X.replaceEndpoint0 a
      endpoint_mem := hendpoint_mem
      endpoint_injective := hendpoint_injective
      cyclic_alternating := halternating
    } ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [Cross.replaceEndpoint0] using firstNew
  · simpa [Cross.replaceEndpoint0] using r
  · simpa [Cross.replaceEndpoint0] using hfirst_path
  · simpa [Cross.replaceEndpoint0] using hr_path
  · simpa [Cross.replaceEndpoint0] using hdisjoint
  · simpa [Cross.replaceEndpoint0] using hfirst_internal
  · simpa [Cross.replaceEndpoint0] using hsecond_internal

/-- Replace endpoint `3` of a lifted cross by a clean tail from an interior
point of the second cross path to a new society-boundary vertex. -/
def Cross.lift_replaceEndpoint3_with_tail
    [DecidableEq V]
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint3 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hprefix_boundary :
      forall (hxS : x ∈ (X.secondPath.mapLe hgraph).support) (z : V),
        z ∈ ((X.secondPath.mapLe hgraph).takeUntil x hxS).support ->
          z ∈ S.boundarySet ->
            z = X.endpoints.endpoint 1 ∨ z = x)
    (hfirst_internal :
      Walk.InternalVertices (X.firstPath.mapLe hgraph) ∩ S.boundarySet =
        ∅) :
    S.Cross := by
  classical
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe hgraph
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe hgraph
  have hxS : x ∈ r.support := by
    simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hx
  let secondNew : S.graph.Walk (X.endpoints.endpoint 1) a :=
    (r.takeUntil x hxS).append q
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe hgraph X.firstPath_isPath
  have hr_path : r.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe hgraph X.secondPath_isPath
  have hsecond_path : secondNew.IsPath := by
    dsimp [secondNew]
    exact Walk.IsPath.takeUntil_append_of_clean hr_path hxS hq_path
      (by
        intro z hzq hzr
        exact hq_clean z hzq
          (Or.inr (by
            simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr)))
  have hdisjoint :
      Disjoint {v : V | v ∈ p.support} {v : V | v ∈ secondNew.support} := by
    rw [Set.disjoint_left]
    intro z hz_first hz_second
    have hz_first_X : z ∈ X.firstPath.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hz_first
    have hx_not_first : x ∉ X.firstPath.support := by
      intro hx_first
      exact Set.disjoint_left.mp X.paths_disjoint hx_first hx
    have hz_second' : z ∈ (r.takeUntil x hxS).support ∨ z ∈ q.support := by
      simpa [secondNew, SimpleGraph.Walk.mem_support_append_iff] using hz_second
    rcases hz_second' with hz_prefix | hzq
    · have hz_r : z ∈ r.support :=
        SimpleGraph.Walk.support_takeUntil_subset r hxS hz_prefix
      have hz_second_X : z ∈ X.secondPath.support := by
        simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hz_r
      exact Set.disjoint_left.mp X.paths_disjoint hz_first_X hz_second_X
    · have hzx : z = x := hq_clean z hzq (Or.inl hz_first_X)
      exact hx_not_first (by simpa [hzx] using hz_first_X)
  have hsecond_internal :
      Walk.InternalVertices secondNew ∩ S.boundarySet = ∅ := by
    dsimp [secondNew]
    exact Walk.InternalVertices.takeUntil_append_boundary_clean hxS
      (hprefix_boundary hxS) hq_boundary hx_not_boundary
  refine Cross.ofPaths {
      endpoint := X.replaceEndpoint3 a
      endpoint_mem := hendpoint_mem
      endpoint_injective := hendpoint_injective
      cyclic_alternating := halternating
    } ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [Cross.replaceEndpoint3] using p
  · simpa [Cross.replaceEndpoint3] using secondNew
  · simpa [Cross.replaceEndpoint3] using hp_path
  · simpa [Cross.replaceEndpoint3] using hsecond_path
  · simpa [Cross.replaceEndpoint3] using hdisjoint
  · simpa [Cross.replaceEndpoint3] using hfirst_internal
  · simpa [Cross.replaceEndpoint3] using hsecond_internal

/-- Symmetric endpoint-`1` version of
`Cross.lift_replaceEndpoint3_with_tail`: prepend the reversed clean tail to
the suffix of the second cross path from the last contact. -/
def Cross.lift_replaceEndpoint1_with_tail
    [DecidableEq V]
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint1 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hdrop_boundary :
      forall (hxS : x ∈ (X.secondPath.mapLe hgraph).support) (z : V),
        z ∈ ((X.secondPath.mapLe hgraph).dropUntil x hxS).support ->
          z ∈ S.boundarySet ->
            z = x ∨ z = X.endpoints.endpoint 3)
    (hfirst_internal :
      Walk.InternalVertices (X.firstPath.mapLe hgraph) ∩ S.boundarySet =
        ∅) :
    S.Cross := by
  classical
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe hgraph
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe hgraph
  have hxS : x ∈ r.support := by
    simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hx
  let secondNew : S.graph.Walk a (X.endpoints.endpoint 3) :=
    q.reverse.append (r.dropUntil x hxS)
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe hgraph X.firstPath_isPath
  have hr_path : r.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe hgraph X.secondPath_isPath
  have hsecond_path : secondNew.IsPath := by
    dsimp [secondNew]
    exact Walk.IsPath.reverse_append_dropUntil_of_clean hr_path hxS hq_path
      (by
        intro z hzq hzr
        exact hq_clean z hzq
          (Or.inr (by
            simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr)))
  have hdisjoint :
      Disjoint {v : V | v ∈ p.support} {v : V | v ∈ secondNew.support} := by
    rw [Set.disjoint_left]
    intro z hz_first hz_second
    have hz_first_X : z ∈ X.firstPath.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hz_first
    have hx_not_first : x ∉ X.firstPath.support := by
      intro hx_first
      exact Set.disjoint_left.mp X.paths_disjoint hx_first hx
    have hz_second' : z ∈ q.reverse.support ∨ z ∈ (r.dropUntil x hxS).support := by
      simpa [secondNew, SimpleGraph.Walk.mem_support_append_iff] using hz_second
    rcases hz_second' with hzq_rev | hz_drop
    · have hzq : z ∈ q.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzq_rev
        exact List.mem_reverse.mp hzq_rev
      have hzx : z = x := hq_clean z hzq (Or.inl hz_first_X)
      exact hx_not_first (by simpa [hzx] using hz_first_X)
    · have hz_r : z ∈ r.support :=
        SimpleGraph.Walk.support_dropUntil_subset r hxS hz_drop
      have hz_second_X : z ∈ X.secondPath.support := by
        simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hz_r
      exact Set.disjoint_left.mp X.paths_disjoint hz_first_X hz_second_X
  have hsecond_internal :
      Walk.InternalVertices secondNew ∩ S.boundarySet = ∅ := by
    dsimp [secondNew]
    exact Walk.InternalVertices.reverse_append_dropUntil_boundary_clean hxS
      (hdrop_boundary hxS) hq_boundary hx_not_boundary
  refine Cross.ofPaths {
      endpoint := X.replaceEndpoint1 a
      endpoint_mem := hendpoint_mem
      endpoint_injective := hendpoint_injective
      cyclic_alternating := halternating
    } ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [Cross.replaceEndpoint1] using p
  · simpa [Cross.replaceEndpoint1] using secondNew
  · simpa [Cross.replaceEndpoint1] using hp_path
  · simpa [Cross.replaceEndpoint1] using hsecond_path
  · simpa [Cross.replaceEndpoint1] using hdisjoint
  · simpa [Cross.replaceEndpoint1] using hfirst_internal
  · simpa [Cross.replaceEndpoint1] using hsecond_internal

/-- Same-society endpoint-`2` replacement by a clean tail.

This is the side-cross version of the GM IX `(2.4)` maximality move: the new
cross remains in the same society, so the generic lifted constructor only
needs the standard boundary-control consequences of the original cross. -/
def Cross.replaceEndpoint2_with_tail
    [DecidableEq V]
    {S : GeneralSociety V}
    (X : S.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint2 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    S.Cross :=
  X.lift_replaceEndpoint2_with_tail (le_refl S.graph) hx q
    hendpoint_mem hendpoint_injective halternating hq_path hq_boundary
    hx_not_boundary hq_clean
    (by
      intro hxS z hz hzB
      exact
        Walk.IsPath.takeUntil_boundary_subset_start_or_cut
          (SimpleGraph.Walk.IsPath.mapLe (le_refl S.graph)
            X.firstPath_isPath)
          hxS S.boundarySet
          (by
            simpa [Walk.internalVertices_mapLe] using
              X.first_internal_boundary)
          z hz hzB)
    (by
      simpa [Walk.internalVertices_mapLe] using
        X.second_internal_boundary)

/-- Same-society endpoint-`0` replacement by a clean tail. -/
def Cross.replaceEndpoint0_with_tail
    [DecidableEq V]
    {S : GeneralSociety V}
    (X : S.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint0 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    S.Cross :=
  X.lift_replaceEndpoint0_with_tail (le_refl S.graph) hx q
    hendpoint_mem hendpoint_injective halternating hq_path hq_boundary
    hx_not_boundary hq_clean
    (by
      intro hxS z hz hzB
      exact
        Walk.IsPath.dropUntil_boundary_subset_cut_or_end
          (SimpleGraph.Walk.IsPath.mapLe (le_refl S.graph)
            X.firstPath_isPath)
          hxS S.boundarySet
          (by
            simpa [Walk.internalVertices_mapLe] using
              X.first_internal_boundary)
          z hz hzB)
    (by
      simpa [Walk.internalVertices_mapLe] using
        X.second_internal_boundary)

/-- Same-society endpoint-`3` replacement by a clean tail. -/
def Cross.replaceEndpoint3_with_tail
    [DecidableEq V]
    {S : GeneralSociety V}
    (X : S.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint3 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    S.Cross :=
  X.lift_replaceEndpoint3_with_tail (le_refl S.graph) hx q
    hendpoint_mem hendpoint_injective halternating hq_path hq_boundary
    hx_not_boundary hq_clean
    (by
      intro hxS z hz hzB
      exact
        Walk.IsPath.takeUntil_boundary_subset_start_or_cut
          (SimpleGraph.Walk.IsPath.mapLe (le_refl S.graph)
            X.secondPath_isPath)
          hxS S.boundarySet
          (by
            simpa [Walk.internalVertices_mapLe] using
              X.second_internal_boundary)
          z hz hzB)
    (by
      simpa [Walk.internalVertices_mapLe] using
        X.first_internal_boundary)

/-- Same-society endpoint-`1` replacement by a clean tail. -/
def Cross.replaceEndpoint1_with_tail
    [DecidableEq V]
    {S : GeneralSociety V}
    (X : S.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint1 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    S.Cross :=
  X.lift_replaceEndpoint1_with_tail (le_refl S.graph) hx q
    hendpoint_mem hendpoint_injective halternating hq_path hq_boundary
    hx_not_boundary hq_clean
    (by
      intro hxS z hz hzB
      exact
        Walk.IsPath.dropUntil_boundary_subset_cut_or_end
          (SimpleGraph.Walk.IsPath.mapLe (le_refl S.graph)
            X.secondPath_isPath)
          hxS S.boundarySet
          (by
            simpa [Walk.internalVertices_mapLe] using
              X.second_internal_boundary)
          z hz hzB)
    (by
      simpa [Walk.internalVertices_mapLe] using
        X.first_internal_boundary)


end GeneralSociety

end Schematic.Math.GraphTheory
