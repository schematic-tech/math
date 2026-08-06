import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.CrossEndpoints

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

theorem Cross.endpoint_ne_of_not_boundary {S : GeneralSociety V}
    (X : S.Cross) {x : V}
    (hx_not_boundary : x ∉ S.boundarySet) :
    forall i : Fin 4, x ≠ X.endpoints.endpoint i := by
  intro i hxi
  exact hx_not_boundary (by
    simpa [GeneralSociety.boundarySet] using
      (hxi.symm ▸ X.endpoints.endpoint_mem i))

theorem Cross.firstPath_nonendpoint_not_boundary {S : GeneralSociety V}
    (X : S.Cross) {x : V}
    (hx : x ∈ X.firstPath.support)
    (hx0 : x ≠ X.endpoints.endpoint 0)
    (hx2 : x ≠ X.endpoints.endpoint 2) :
    x ∉ S.boundarySet :=
  Walk.not_mem_of_internalVertices_disjoint_of_mem_support_ne_endpoints
    X.first_internal_boundary hx hx0 hx2

theorem Cross.secondPath_nonendpoint_not_boundary {S : GeneralSociety V}
    (X : S.Cross) {x : V}
    (hx : x ∈ X.secondPath.support)
    (hx1 : x ≠ X.endpoints.endpoint 1)
    (hx3 : x ≠ X.endpoints.endpoint 3) :
    x ∉ S.boundarySet :=
  Walk.not_mem_of_internalVertices_disjoint_of_mem_support_ne_endpoints
    X.second_internal_boundary hx hx1 hx3

theorem Cross.clean_tail_endpoint_ne_of_hit
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (X : S.Cross)
    {x a : V}
    (q : G.Walk x a)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    {i : Fin 4}
    (hxi : x ≠ X.endpoints.endpoint i) :
    a ≠ X.endpoints.endpoint i := by
  intro hai
  have haX :
      a ∈ X.firstPath.support ∨ a ∈ X.secondPath.support := by
    simpa [hai] using X.endpoint_mem_path_support i
  have hax : a = x := hq_clean a q.end_mem_support haX
  exact hxi (hax ▸ hai)

theorem Cross.clean_tail_from_firstPath_hit_ne_endpoint
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (X : S.Cross)
    {x a : V}
    (q : G.Walk x a)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    {i : Fin 4}
    (hxi : x ≠ X.endpoints.endpoint i) :
    a ≠ X.endpoints.endpoint i :=
  X.clean_tail_endpoint_ne_of_hit q hq_clean hxi

theorem Cross.clean_tail_from_secondPath_hit_ne_endpoint
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (X : S.Cross)
    {x a : V}
    (q : G.Walk x a)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    {i : Fin 4}
    (hxi : x ≠ X.endpoints.endpoint i) :
    a ≠ X.endpoints.endpoint i :=
  X.clean_tail_endpoint_ne_of_hit q hq_clean hxi

theorem Cross.clean_tail_endpoint_ne_all_of_hit
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (X : S.Cross)
    {x a : V}
    (q : G.Walk x a)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i) :
    forall i : Fin 4, a ≠ X.endpoints.endpoint i := by
  intro i
  exact X.clean_tail_endpoint_ne_of_hit q hq_clean (hx_ne i)

theorem Cross.exists_clean_branch_path_first_to_second
    [DecidableEq V]
    {S : GeneralSociety V}
    (X : S.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzFirst : z ∈ X.firstPath.support)
    (hyq : y ∈ q.support)
    (hySecond : y ∈ X.secondPath.support)
    (hq_path : q.IsPath) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.firstPath.support ∧ y' ∈ X.secondPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y') ∧
              forall w : V, w ∈ r.support -> w ∈ q.support := by
  classical
  let p0 : S.graph.Walk z y := q.takeUntil y hyq
  have hp0_path : p0.IsPath := by
    simpa [p0] using hq_path.takeUntil hyq
  obtain ⟨y', hy'_p0, hy'_second, hfirst_second⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem
      (G := S.graph) hp0_path
      {w : V | w ∈ X.secondPath.support}
      (by simpa [p0] using hySecond)
  let p1 : S.graph.Walk z y' := p0.takeUntil y' hy'_p0
  have hp1_path : p1.IsPath := by
    simpa [p1] using hp0_path.takeUntil hy'_p0
  obtain ⟨x, hx_p1, hx_first, hr_path, hlast_first, hr_subset_p1,
      _hr_covers, _hr_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hp1_path
      {w : V | w ∈ X.firstPath.support}
      (by simpa [p1] using hzFirst)
  let r : S.graph.Walk x y' := p1.dropUntil x hx_p1
  refine ⟨x, y', r, hx_first, hy'_second, by simpa [r] using hr_path,
    ?_, ?_, ?_⟩
  · intro w hw hwFirst
    exact hlast_first w (by simpa [r] using hw) hwFirst
  · intro w hw hwSecond
    have hw_p1 : w ∈ p1.support := hr_subset_p1 w (by simpa [r] using hw)
    exact hfirst_second w (by simpa [p1] using hw_p1) hwSecond
  · intro w hw
    have hw_p1 : w ∈ p1.support := hr_subset_p1 w (by simpa [r] using hw)
    have hw_p0 : w ∈ p0.support :=
      SimpleGraph.Walk.support_takeUntil_subset p0 hy'_p0
        (by simpa [p1] using hw_p1)
    exact SimpleGraph.Walk.support_takeUntil_subset q hyq
      (by simpa [p0] using hw_p0)

theorem Cross.exists_clean_branch_path_second_to_first
    [DecidableEq V]
    {S : GeneralSociety V}
    (X : S.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzSecond : z ∈ X.secondPath.support)
    (hyq : y ∈ q.support)
    (hyFirst : y ∈ X.firstPath.support)
    (hq_path : q.IsPath) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.secondPath.support ∧ y' ∈ X.firstPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y') ∧
              forall w : V, w ∈ r.support -> w ∈ q.support := by
  obtain ⟨x, y', r, hx, hy, hr, hx_clean, hy_clean, hrq⟩ :=
    X.rotate1.exists_clean_branch_path_first_to_second q
      (by simpa [Cross.rotate1] using hzSecond) hyq
      (by simpa [Cross.rotate1] using hyFirst) hq_path
  refine ⟨x, y', r, ?_, ?_, hr, ?_, ?_, hrq⟩
  · simpa [Cross.rotate1] using hx
  · simpa [Cross.rotate1] using hy
  · simpa [Cross.rotate1] using hx_clean
  · simpa [Cross.rotate1] using hy_clean

theorem Cross.replaceEndpoint2_injective_of_clean_tail_from_nonboundary
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (X : S.Cross)
    {x a : V}
    (q : G.Walk x a)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Function.Injective (X.replaceEndpoint2 a) :=
  X.replaceEndpoint2_injective (by
    intro i _hi
    exact X.clean_tail_endpoint_ne_of_hit q hq_clean
      (X.endpoint_ne_of_not_boundary hx_not_boundary i))

theorem Cross.replaceEndpoint0_injective_of_clean_tail_from_nonboundary
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (X : S.Cross)
    {x a : V}
    (q : G.Walk x a)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Function.Injective (X.replaceEndpoint0 a) :=
  X.replaceEndpoint0_injective (by
    intro i _hi
    exact X.clean_tail_endpoint_ne_of_hit q hq_clean
      (X.endpoint_ne_of_not_boundary hx_not_boundary i))

theorem Cross.replaceEndpoint3_injective_of_clean_tail_from_nonboundary
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (X : S.Cross)
    {x a : V}
    (q : G.Walk x a)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Function.Injective (X.replaceEndpoint3 a) :=
  X.replaceEndpoint3_injective (by
    intro i _hi
    exact X.clean_tail_endpoint_ne_of_hit q hq_clean
      (X.endpoint_ne_of_not_boundary hx_not_boundary i))

theorem Cross.replaceEndpoint1_injective_of_clean_tail_from_nonboundary
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (X : S.Cross)
    {x a : V}
    (q : G.Walk x a)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Function.Injective (X.replaceEndpoint1 a) :=
  X.replaceEndpoint1_injective (by
    intro i _hi
    exact X.clean_tail_endpoint_ne_of_hit q hq_clean
      (X.endpoint_ne_of_not_boundary hx_not_boundary i))

end GeneralSociety

end Schematic.Math.GraphTheory
