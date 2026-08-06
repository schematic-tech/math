import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.CaughtRegions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The GM IX `(2.4)` 3-connected society hypothesis: no proper separation
of order `< 3` with all boundary vertices on one side. -/
def ThreeConnected (S : GeneralSociety V) : Prop :=
  forall T : Separation S.graph,
    S.boundarySet ⊆ T.left ->
      ((T.right \ T.left) ∩ S.activeSet).Nonempty ->
        T.OrderAtMost 2 ->
          False

/-- Endpoint data for a cross in a finite cyclic society.

The endpoint order is the concrete alternation `0,1,2,3` around the boundary:
endpoint `1` lies strictly clockwise from `0` to `2`, and endpoint `3` lies
strictly clockwise from `2` back to `0`. -/
noncomputable def CrossEndpointAlternating
    (Ω : CyclicBoundary V) (endpoint : Fin 4 -> V) : Prop :=
  letI := Classical.decEq V
  Ω.ClockwiseOpenBetween (endpoint 0) (endpoint 2) (endpoint 1) ∧
    Ω.ClockwiseOpenBetween (endpoint 2) (endpoint 0) (endpoint 3)

theorem CrossEndpointAlternating.not_opposite_02_of_13_before
    [DecidableEq V] {Ω : CyclicBoundary V} {endpoint : Fin 4 -> V}
    (h : CrossEndpointAlternating Ω endpoint)
    (h10 :
      Ω.indexOf (endpoint 1) < Ω.indexOf (endpoint 0))
    (h12 :
      Ω.indexOf (endpoint 1) < Ω.indexOf (endpoint 2))
    (h30 :
      Ω.indexOf (endpoint 3) < Ω.indexOf (endpoint 0))
    (h32 :
      Ω.indexOf (endpoint 3) < Ω.indexOf (endpoint 2)) :
    False := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h10' : idx (endpoint 1) < idx (endpoint 0) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h10
  have h12' : idx (endpoint 1) < idx (endpoint 2) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h12
  have h30' : idx (endpoint 3) < idx (endpoint 0) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h30
  have h32' : idx (endpoint 3) < idx (endpoint 2) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h32
  by_cases h02 : idx (endpoint 0) <= idx (endpoint 2)
  · have hbetween := h.1.1.2
    change
      (if idx (endpoint 0) <= idx (endpoint 2) then
        idx (endpoint 0) <= idx (endpoint 1) ∧
          idx (endpoint 1) <= idx (endpoint 2)
      else
        idx (endpoint 0) <= idx (endpoint 1) ∨
          idx (endpoint 1) <= idx (endpoint 2)) at hbetween
    rw [if_pos h02] at hbetween
    omega
  · have h20 : idx (endpoint 2) <= idx (endpoint 0) := by omega
    have hbetween := h.2.1.2
    change
      (if idx (endpoint 2) <= idx (endpoint 0) then
        idx (endpoint 2) <= idx (endpoint 3) ∧
          idx (endpoint 3) <= idx (endpoint 0)
      else
        idx (endpoint 2) <= idx (endpoint 3) ∨
          idx (endpoint 3) <= idx (endpoint 0)) at hbetween
    rw [if_pos h20] at hbetween
    omega

theorem CrossEndpointAlternating.not_opposite_13_of_02_before
    [DecidableEq V] {Ω : CyclicBoundary V} {endpoint : Fin 4 -> V}
    (h : CrossEndpointAlternating Ω endpoint)
    (h01 :
      Ω.indexOf (endpoint 0) < Ω.indexOf (endpoint 1))
    (h03 :
      Ω.indexOf (endpoint 0) < Ω.indexOf (endpoint 3))
    (h21 :
      Ω.indexOf (endpoint 2) < Ω.indexOf (endpoint 1))
    (h23 :
      Ω.indexOf (endpoint 2) < Ω.indexOf (endpoint 3)) :
    False := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h01' : idx (endpoint 0) < idx (endpoint 1) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h01
  have h03' : idx (endpoint 0) < idx (endpoint 3) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h03
  have h21' : idx (endpoint 2) < idx (endpoint 1) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h21
  have h23' : idx (endpoint 2) < idx (endpoint 3) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h23
  by_cases h02 : idx (endpoint 0) <= idx (endpoint 2)
  · have hbetween := h.1.1.2
    change
      (if idx (endpoint 0) <= idx (endpoint 2) then
        idx (endpoint 0) <= idx (endpoint 1) ∧
          idx (endpoint 1) <= idx (endpoint 2)
      else
        idx (endpoint 0) <= idx (endpoint 1) ∨
          idx (endpoint 1) <= idx (endpoint 2)) at hbetween
    rw [if_pos h02] at hbetween
    omega
  · have h20 : idx (endpoint 2) <= idx (endpoint 0) := by omega
    have hbetween := h.2.1.2
    change
      (if idx (endpoint 2) <= idx (endpoint 0) then
        idx (endpoint 2) <= idx (endpoint 3) ∧
          idx (endpoint 3) <= idx (endpoint 0)
      else
        idx (endpoint 2) <= idx (endpoint 3) ∨
          idx (endpoint 3) <= idx (endpoint 0)) at hbetween
    rw [if_pos h20] at hbetween
    omega

theorem CrossEndpointAlternating.index_le_01_of_23_before
    [DecidableEq V] {Ω : CyclicBoundary V} {endpoint : Fin 4 -> V}
    (h : CrossEndpointAlternating Ω endpoint)
    (h20 :
      Ω.indexOf (endpoint 2) < Ω.indexOf (endpoint 0))
    (h21 :
      Ω.indexOf (endpoint 2) < Ω.indexOf (endpoint 1))
    (h30 :
      Ω.indexOf (endpoint 3) < Ω.indexOf (endpoint 0)) :
    Ω.indexOf (endpoint 0) <= Ω.indexOf (endpoint 1) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h20' : idx (endpoint 2) < idx (endpoint 0) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h20
  have h21' : idx (endpoint 2) < idx (endpoint 1) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h21
  have h30' : idx (endpoint 3) < idx (endpoint 0) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h30
  have h02_not : ¬ idx (endpoint 0) <= idx (endpoint 2) := by omega
  have hbetween := h.1.1.2
  change
    (if idx (endpoint 0) <= idx (endpoint 2) then
      idx (endpoint 0) <= idx (endpoint 1) ∧
        idx (endpoint 1) <= idx (endpoint 2)
    else
      idx (endpoint 0) <= idx (endpoint 1) ∨
        idx (endpoint 1) <= idx (endpoint 2)) at hbetween
  rw [if_neg h02_not] at hbetween
  have h01 : idx (endpoint 0) <= idx (endpoint 1) := by
    rcases hbetween with h01 | h12
    · exact h01
    · omega
  simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h01

theorem CrossEndpointAlternating.index_le_12_of_03_before
    [DecidableEq V] {Ω : CyclicBoundary V} {endpoint : Fin 4 -> V}
    (h : CrossEndpointAlternating Ω endpoint)
    (h02 :
      Ω.indexOf (endpoint 0) < Ω.indexOf (endpoint 2)) :
    Ω.indexOf (endpoint 1) <= Ω.indexOf (endpoint 2) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h02' : idx (endpoint 0) < idx (endpoint 2) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h02
  have hbetween := h.1.1.2
  change
    (if idx (endpoint 0) <= idx (endpoint 2) then
      idx (endpoint 0) <= idx (endpoint 1) ∧
        idx (endpoint 1) <= idx (endpoint 2)
    else
      idx (endpoint 0) <= idx (endpoint 1) ∨
        idx (endpoint 1) <= idx (endpoint 2)) at hbetween
  rw [if_pos (Nat.le_of_lt h02')] at hbetween
  have h12 : idx (endpoint 1) <= idx (endpoint 2) := hbetween.2
  simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h12

theorem CrossEndpointAlternating.index_le_23_of_01_before
    [DecidableEq V] {Ω : CyclicBoundary V} {endpoint : Fin 4 -> V}
    (h : CrossEndpointAlternating Ω endpoint)
    (h02 :
      Ω.indexOf (endpoint 0) < Ω.indexOf (endpoint 2))
    (h03 :
      Ω.indexOf (endpoint 0) < Ω.indexOf (endpoint 3)) :
    Ω.indexOf (endpoint 2) <= Ω.indexOf (endpoint 3) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h02' : idx (endpoint 0) < idx (endpoint 2) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h02
  have h03' : idx (endpoint 0) < idx (endpoint 3) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h03
  have h20_not : ¬ idx (endpoint 2) <= idx (endpoint 0) := by omega
  have hbetween := h.2.1.2
  change
    (if idx (endpoint 2) <= idx (endpoint 0) then
      idx (endpoint 2) <= idx (endpoint 3) ∧
        idx (endpoint 3) <= idx (endpoint 0)
    else
      idx (endpoint 2) <= idx (endpoint 3) ∨
        idx (endpoint 3) <= idx (endpoint 0)) at hbetween
  rw [if_neg h20_not] at hbetween
  have h23 : idx (endpoint 2) <= idx (endpoint 3) := by
    rcases hbetween with h23 | h30
    · exact h23
    · omega
  simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h23

theorem CrossEndpointAlternating.index_le_30_of_12_before
    [DecidableEq V] {Ω : CyclicBoundary V} {endpoint : Fin 4 -> V}
    (h : CrossEndpointAlternating Ω endpoint)
    (h20 :
      Ω.indexOf (endpoint 2) < Ω.indexOf (endpoint 0)) :
    Ω.indexOf (endpoint 3) <= Ω.indexOf (endpoint 0) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h20' : idx (endpoint 2) < idx (endpoint 0) := by
    simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h20
  have hbetween := h.2.1.2
  change
    (if idx (endpoint 2) <= idx (endpoint 0) then
      idx (endpoint 2) <= idx (endpoint 3) ∧
        idx (endpoint 3) <= idx (endpoint 0)
    else
      idx (endpoint 2) <= idx (endpoint 3) ∨
        idx (endpoint 3) <= idx (endpoint 0)) at hbetween
  rw [if_pos (Nat.le_of_lt h20')] at hbetween
  have h30 : idx (endpoint 3) <= idx (endpoint 0) := hbetween.2
  simpa [idx, CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using h30

structure CrossEndpoints (Ω : CyclicBoundary V) where
  endpoint : Fin 4 -> V
  endpoint_mem : forall i : Fin 4, endpoint i ∈ Ω.vertexSet
  endpoint_injective : Function.Injective endpoint
  cyclic_alternating : CrossEndpointAlternating Ω endpoint

/-- A general society cross: two disjoint nontrivial paths whose endpoints
alternate on the cyclic boundary. -/
structure Cross (S : GeneralSociety V) where
  endpoints : CrossEndpoints S.boundary
  firstPath : S.graph.Walk (endpoints.endpoint 0) (endpoints.endpoint 2)
  secondPath : S.graph.Walk (endpoints.endpoint 1) (endpoints.endpoint 3)
  firstPath_isPath : firstPath.IsPath
  secondPath_isPath : secondPath.IsPath
  firstPath_nontrivial : firstPath.length ≠ 0
  secondPath_nontrivial : secondPath.length ≠ 0
  paths_disjoint :
    Disjoint {v : V | v ∈ firstPath.support}
      {v : V | v ∈ secondPath.support}
  first_internal_boundary :
    Walk.InternalVertices firstPath ∩ S.boundarySet = ∅
  second_internal_boundary :
    Walk.InternalVertices secondPath ∩ S.boundarySet = ∅

/-- Build a cross from disjoint boundary-clean paths.  Endpoint injectivity
already forces both opposite-endpoint paths to be nontrivial. -/
def Cross.ofPaths {S : GeneralSociety V}
    (endpoints : CrossEndpoints S.boundary)
    (firstPath : S.graph.Walk (endpoints.endpoint 0) (endpoints.endpoint 2))
    (secondPath : S.graph.Walk (endpoints.endpoint 1) (endpoints.endpoint 3))
    (firstPath_isPath : firstPath.IsPath)
    (secondPath_isPath : secondPath.IsPath)
    (paths_disjoint :
      Disjoint {v : V | v ∈ firstPath.support}
        {v : V | v ∈ secondPath.support})
    (first_internal_boundary :
      Walk.InternalVertices firstPath ∩ S.boundarySet = ∅)
    (second_internal_boundary :
      Walk.InternalVertices secondPath ∩ S.boundarySet = ∅) :
    S.Cross where
  endpoints := endpoints
  firstPath := firstPath
  secondPath := secondPath
  firstPath_isPath := firstPath_isPath
  secondPath_isPath := secondPath_isPath
  firstPath_nontrivial := by
    intro hlen
    exact (by decide : (0 : Fin 4) ≠ 2)
      (endpoints.endpoint_injective (SimpleGraph.Walk.eq_of_length_eq_zero hlen))
  secondPath_nontrivial := by
    intro hlen
    exact (by decide : (1 : Fin 4) ≠ 3)
      (endpoints.endpoint_injective (SimpleGraph.Walk.eq_of_length_eq_zero hlen))
  paths_disjoint := paths_disjoint
  first_internal_boundary := first_internal_boundary
  second_internal_boundary := second_internal_boundary

@[simp]
theorem Cross.cast_endpoint {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (i : Fin 4) :
    ((h ▸ X : T.Cross).endpoints.endpoint i) =
      X.endpoints.endpoint i := by
  cases h
  rfl

@[simp]
theorem Cross.cast_endpointFunction {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) :
    (h ▸ X : T.Cross).endpoints.endpoint = X.endpoints.endpoint := by
  funext i
  exact X.cast_endpoint h i

@[simp]
theorem Cross.cast_firstPath_support {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) :
    ((h ▸ X : T.Cross).firstPath.support) = X.firstPath.support := by
  cases h
  rfl

@[simp]
theorem Cross.cast_secondPath_support {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) :
    ((h ▸ X : T.Cross).secondPath.support) = X.secondPath.support := by
  cases h
  rfl

def Cross.lift_of_le
    {S H : GeneralSociety V}
    (X : H.Cross)
    (hgraph : H.graph ≤ S.graph)
    (hendpoint_mem :
      forall i : Fin 4, X.endpoints.endpoint i ∈ S.boundary.vertexSet)
    (halternating :
      CrossEndpointAlternating S.boundary X.endpoints.endpoint)
    (hfirst_internal :
      Walk.InternalVertices (X.firstPath.mapLe hgraph) ∩ S.boundarySet = ∅)
    (hsecond_internal :
      Walk.InternalVertices (X.secondPath.mapLe hgraph) ∩ S.boundarySet = ∅) :
    S.Cross := by
  refine Cross.ofPaths {
    endpoint := X.endpoints.endpoint
    endpoint_mem := hendpoint_mem
    endpoint_injective := X.endpoints.endpoint_injective
    cyclic_alternating := halternating
    } (X.firstPath.mapLe hgraph) (X.secondPath.mapLe hgraph) ?_ ?_ ?_ ?_ ?_
  · exact SimpleGraph.Walk.IsPath.mapLe hgraph X.firstPath_isPath
  · exact SimpleGraph.Walk.IsPath.mapLe hgraph X.secondPath_isPath
  · simpa [SimpleGraph.Walk.support_mapLe_eq_support] using X.paths_disjoint
  · exact hfirst_internal
  · exact hsecond_internal

def Cross.replaceEndpoint2 {S : GeneralSociety V} (X : S.Cross) (a : V) :
    Fin 4 -> V := fun i =>
  if i = 2 then a else X.endpoints.endpoint i

def Cross.replaceEndpoint0 {S : GeneralSociety V} (X : S.Cross) (a : V) :
    Fin 4 -> V := fun i =>
  if i = 0 then a else X.endpoints.endpoint i

def Cross.replaceEndpoint3 {S : GeneralSociety V} (X : S.Cross) (a : V) :
    Fin 4 -> V := fun i =>
  if i = 3 then a else X.endpoints.endpoint i

def Cross.replaceEndpoint1 {S : GeneralSociety V} (X : S.Cross) (a : V) :
    Fin 4 -> V := fun i =>
  if i = 1 then a else X.endpoints.endpoint i

@[simp]
theorem Cross.cast_replaceEndpoint2 {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (a : V) :
    (h ▸ X : T.Cross).replaceEndpoint2 a = X.replaceEndpoint2 a := by
  cases h
  rfl

@[simp]
theorem Cross.cast_replaceEndpoint0 {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (a : V) :
    (h ▸ X : T.Cross).replaceEndpoint0 a = X.replaceEndpoint0 a := by
  cases h
  rfl

@[simp]
theorem Cross.cast_replaceEndpoint3 {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (a : V) :
    (h ▸ X : T.Cross).replaceEndpoint3 a = X.replaceEndpoint3 a := by
  cases h
  rfl

@[simp]
theorem Cross.cast_replaceEndpoint1 {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (a : V) :
    (h ▸ X : T.Cross).replaceEndpoint1 a = X.replaceEndpoint1 a := by
  cases h
  rfl

def Cross.replaceEndpoints01 {S : GeneralSociety V}
    (X : S.Cross) (a0 a1 : V) : Fin 4 -> V := fun i =>
  if i = 0 then a0 else if i = 1 then a1 else X.endpoints.endpoint i

def Cross.replaceEndpoints12 {S : GeneralSociety V}
    (X : S.Cross) (a1 a2 : V) : Fin 4 -> V := fun i =>
  if i = 1 then a1 else if i = 2 then a2 else X.endpoints.endpoint i

def Cross.replaceEndpoints23 {S : GeneralSociety V}
    (X : S.Cross) (a2 a3 : V) : Fin 4 -> V := fun i =>
  if i = 2 then a2 else if i = 3 then a3 else X.endpoints.endpoint i

def Cross.replaceEndpoints30 {S : GeneralSociety V}
    (X : S.Cross) (a3 a0 : V) : Fin 4 -> V := fun i =>
  if i = 3 then a3 else if i = 0 then a0 else X.endpoints.endpoint i

@[simp]
theorem Cross.cast_replaceEndpoints01 {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (a0 a1 : V) :
    (h ▸ X : T.Cross).replaceEndpoints01 a0 a1 =
      X.replaceEndpoints01 a0 a1 := by
  cases h
  rfl

@[simp]
theorem Cross.cast_replaceEndpoints12 {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (a1 a2 : V) :
    (h ▸ X : T.Cross).replaceEndpoints12 a1 a2 =
      X.replaceEndpoints12 a1 a2 := by
  cases h
  rfl

@[simp]
theorem Cross.cast_replaceEndpoints23 {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (a2 a3 : V) :
    (h ▸ X : T.Cross).replaceEndpoints23 a2 a3 =
      X.replaceEndpoints23 a2 a3 := by
  cases h
  rfl

@[simp]
theorem Cross.cast_replaceEndpoints30 {S T : GeneralSociety V}
    (h : S = T) (X : S.Cross) (a3 a0 : V) :
    (h ▸ X : T.Cross).replaceEndpoints30 a3 a0 =
      X.replaceEndpoints30 a3 a0 := by
  cases h
  rfl

private theorem replaceEndpoint_injective
    {S : GeneralSociety V} (X : S.Cross) (k : Fin 4) {a : V}
    (ha_ne : forall i : Fin 4, i ≠ k -> a ≠ X.endpoints.endpoint i) :
    Function.Injective (fun i => if i = k then a else X.endpoints.endpoint i) := by
  intro i j hij
  by_cases hi : i = k
  · subst i
    by_cases hj : j = k
    · exact hj.symm
    · have ha_eq : a = X.endpoints.endpoint j := by
        simpa [hj] using hij
      exact False.elim ((ha_ne j hj) ha_eq)
  · by_cases hj : j = k
    · subst j
      have hi_eq : X.endpoints.endpoint i = a := by
        simpa [hi] using hij
      exact False.elim ((ha_ne i hi) hi_eq.symm)
    · have hold : X.endpoints.endpoint i = X.endpoints.endpoint j := by
        simpa [hi, hj] using hij
      exact X.endpoints.endpoint_injective hold

theorem Cross.replaceEndpoint2_injective
    {S : GeneralSociety V} (X : S.Cross) {a : V}
    (ha_ne : forall i : Fin 4, i ≠ 2 -> a ≠ X.endpoints.endpoint i) :
    Function.Injective (X.replaceEndpoint2 a) := by
  simpa only [Cross.replaceEndpoint2] using
    replaceEndpoint_injective X 2 ha_ne

theorem Cross.replaceEndpoint0_injective
    {S : GeneralSociety V} (X : S.Cross) {a : V}
    (ha_ne : forall i : Fin 4, i ≠ 0 -> a ≠ X.endpoints.endpoint i) :
    Function.Injective (X.replaceEndpoint0 a) := by
  simpa only [Cross.replaceEndpoint0] using
    replaceEndpoint_injective X 0 ha_ne

theorem Cross.replaceEndpoint3_injective
    {S : GeneralSociety V} (X : S.Cross) {a : V}
    (ha_ne : forall i : Fin 4, i ≠ 3 -> a ≠ X.endpoints.endpoint i) :
    Function.Injective (X.replaceEndpoint3 a) := by
  simpa only [Cross.replaceEndpoint3] using
    replaceEndpoint_injective X 3 ha_ne

theorem Cross.replaceEndpoint1_injective
    {S : GeneralSociety V} (X : S.Cross) {a : V}
    (ha_ne : forall i : Fin 4, i ≠ 1 -> a ≠ X.endpoints.endpoint i) :
    Function.Injective (X.replaceEndpoint1 a) := by
  simpa only [Cross.replaceEndpoint1] using
    replaceEndpoint_injective X 1 ha_ne

private theorem replaceEndpoints_injective
    {S : GeneralSociety V} (X : S.Cross) {k l : Fin 4} (hkl : k ≠ l)
    {a b : V} (hab : a ≠ b)
    (ha_ne : forall i : Fin 4, i ≠ k -> i ≠ l ->
      a ≠ X.endpoints.endpoint i)
    (hb_ne : forall i : Fin 4, i ≠ k -> i ≠ l ->
      b ≠ X.endpoints.endpoint i) :
    Function.Injective (fun i =>
      if i = k then a else if i = l then b else X.endpoints.endpoint i) := by
  have hlk : l ≠ k := Ne.symm hkl
  intro i j hij
  by_cases hik : i = k
  · subst i
    by_cases hjk : j = k
    · exact hjk.symm
    · by_cases hjl : j = l
      · subst j
        exact False.elim (hab (by simpa [hlk] using hij))
      · have ha_eq : a = X.endpoints.endpoint j := by
          simpa [hjk, hjl] using hij
        exact False.elim ((ha_ne j hjk hjl) ha_eq)
  · by_cases hil : i = l
    · subst i
      by_cases hjk : j = k
      · subst j
        have hba : b = a := by simpa [hlk] using hij
        exact False.elim (hab hba.symm)
      · by_cases hjl : j = l
        · exact hjl.symm
        · have hb_eq : b = X.endpoints.endpoint j := by
            simpa [hlk, hjk, hjl] using hij
          exact False.elim ((hb_ne j hjk hjl) hb_eq)
    · by_cases hjk : j = k
      · subst j
        have ha_eq : X.endpoints.endpoint i = a := by
          simpa [hik, hil] using hij
        exact False.elim ((ha_ne i hik hil) ha_eq.symm)
      · by_cases hjl : j = l
        · subst j
          have hb_eq : X.endpoints.endpoint i = b := by
            simpa [hik, hil, hlk] using hij
          exact False.elim ((hb_ne i hik hil) hb_eq.symm)
        · exact X.endpoints.endpoint_injective (by
            simpa [hik, hil, hjk, hjl] using hij)

theorem Cross.replaceEndpoints01_injective
    {S : GeneralSociety V} (X : S.Cross) {a0 a1 : V}
    (h01 : a0 ≠ a1)
    (ha0_2 : a0 ≠ X.endpoints.endpoint 2)
    (ha0_3 : a0 ≠ X.endpoints.endpoint 3)
    (ha1_2 : a1 ≠ X.endpoints.endpoint 2)
    (ha1_3 : a1 ≠ X.endpoints.endpoint 3) :
    Function.Injective (X.replaceEndpoints01 a0 a1) := by
  simpa only [Cross.replaceEndpoints01] using
    replaceEndpoints_injective X (by decide : (0 : Fin 4) ≠ 1) h01
      (by intro i hi0 hi1; fin_cases i <;> simp_all)
      (by intro i hi0 hi1; fin_cases i <;> simp_all)

theorem Cross.replaceEndpoints12_injective
    {S : GeneralSociety V} (X : S.Cross) {a1 a2 : V}
    (h12 : a1 ≠ a2)
    (ha1_0 : a1 ≠ X.endpoints.endpoint 0)
    (ha1_3 : a1 ≠ X.endpoints.endpoint 3)
    (ha2_0 : a2 ≠ X.endpoints.endpoint 0)
    (ha2_3 : a2 ≠ X.endpoints.endpoint 3) :
    Function.Injective (X.replaceEndpoints12 a1 a2) := by
  simpa only [Cross.replaceEndpoints12] using
    replaceEndpoints_injective X (by decide : (1 : Fin 4) ≠ 2) h12
      (by intro i hi1 hi2; fin_cases i <;> simp_all)
      (by intro i hi1 hi2; fin_cases i <;> simp_all)

theorem Cross.replaceEndpoints23_injective
    {S : GeneralSociety V} (X : S.Cross) {a2 a3 : V}
    (h23 : a2 ≠ a3)
    (ha2_0 : a2 ≠ X.endpoints.endpoint 0)
    (ha2_1 : a2 ≠ X.endpoints.endpoint 1)
    (ha3_0 : a3 ≠ X.endpoints.endpoint 0)
    (ha3_1 : a3 ≠ X.endpoints.endpoint 1) :
    Function.Injective (X.replaceEndpoints23 a2 a3) := by
  simpa only [Cross.replaceEndpoints23] using
    replaceEndpoints_injective X (by decide : (2 : Fin 4) ≠ 3) h23
      (by intro i hi2 hi3; fin_cases i <;> simp_all)
      (by intro i hi2 hi3; fin_cases i <;> simp_all)

theorem Cross.replaceEndpoints30_injective
    {S : GeneralSociety V} (X : S.Cross) {a3 a0 : V}
    (h30 : a3 ≠ a0)
    (ha3_1 : a3 ≠ X.endpoints.endpoint 1)
    (ha3_2 : a3 ≠ X.endpoints.endpoint 2)
    (ha0_1 : a0 ≠ X.endpoints.endpoint 1)
    (ha0_2 : a0 ≠ X.endpoints.endpoint 2) :
    Function.Injective (X.replaceEndpoints30 a3 a0) := by
  simpa only [Cross.replaceEndpoints30] using
    replaceEndpoints_injective X (by decide : (3 : Fin 4) ≠ 0) h30
      (by intro i hi3 hi0; fin_cases i <;> simp_all)
      (by intro i hi3 hi0; fin_cases i <;> simp_all)

theorem Cross.endpoint_mem_path_support {S : GeneralSociety V}
    (X : S.Cross) (i : Fin 4) :
    X.endpoints.endpoint i ∈ X.firstPath.support ∨
      X.endpoints.endpoint i ∈ X.secondPath.support := by
  fin_cases i
  · exact Or.inl X.firstPath.start_mem_support
  · exact Or.inr X.secondPath.start_mem_support
  · exact Or.inl X.firstPath.end_mem_support
  · exact Or.inr X.secondPath.end_mem_support

theorem CrossEndpointAlternating.rotate1
    {Ω : CyclicBoundary V} {endpoint : Fin 4 -> V}
    (hmem : forall i : Fin 4, endpoint i ∈ Ω.vertexSet)
    (hinj : Function.Injective endpoint)
    (h : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (fun i =>
      if i = 0 then endpoint 1
      else if i = 1 then endpoint 2
      else if i = 2 then endpoint 3
      else endpoint 0) := by
  letI := Classical.decEq V
  let idx : Fin 4 -> Nat := fun i =>
    @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i)
  have h01 : idx 0 ≠ idx 1 := by
    simpa [idx] using
      CyclicBoundary.indexOf_ne_of_ne (hmem 0) (by
        intro h01
        exact (by decide : (0 : Fin 4) ≠ 1) (hinj h01))
  have h02 : idx 0 ≠ idx 2 := by
    simpa [idx] using
      CyclicBoundary.indexOf_ne_of_ne (hmem 0) (by
        intro h02
        exact (by decide : (0 : Fin 4) ≠ 2) (hinj h02))
  have h12 : idx 1 ≠ idx 2 := by
    simpa [idx] using
      CyclicBoundary.indexOf_ne_of_ne (hmem 1) (by
        intro h12
        exact (by decide : (1 : Fin 4) ≠ 2) (hinj h12))
  have h13 : idx 1 ≠ idx 3 := by
    simpa [idx] using
      CyclicBoundary.indexOf_ne_of_ne (hmem 1) (by
        intro h13
        exact (by decide : (1 : Fin 4) ≠ 3) (hinj h13))
  have h23 : idx 2 ≠ idx 3 := by
    simpa [idx] using
      CyclicBoundary.indexOf_ne_of_ne (hmem 2) (by
        intro h23
        exact (by decide : (2 : Fin 4) ≠ 3) (hinj h23))
  have hfirst_order := h.1.1.2
  change
    (if idx 0 <= idx 2 then
      idx 0 <= idx 1 ∧ idx 1 <= idx 2
    else
      idx 0 <= idx 1 ∨ idx 1 <= idx 2) at hfirst_order
  have hsecond_order := h.2.1.2
  change
    (if idx 2 <= idx 0 then
      idx 2 <= idx 3 ∧ idx 3 <= idx 0
    else
      idx 2 <= idx 3 ∨ idx 3 <= idx 0) at hsecond_order
  constructor
  · change
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        Ω (endpoint 1) (endpoint 3) (endpoint 2)
    by_cases h13le : idx 1 <= idx 3
    · refine ⟨⟨hmem 2, ?_⟩, ?_, ?_⟩
      · change
          (if idx 1 <= idx 3 then
            idx 1 <= idx 2 ∧ idx 2 <= idx 3
          else
            idx 1 <= idx 2 ∨ idx 2 <= idx 3)
        rw [if_pos h13le]
        constructor
        · by_cases h02le : idx 0 <= idx 2
          · rw [if_pos h02le] at hfirst_order
            exact hfirst_order.2
          · have h20le : idx 2 <= idx 0 := by omega
            rw [if_neg h02le] at hfirst_order
            rw [if_pos h20le] at hsecond_order
            rcases hfirst_order with h01le | h12le
            · omega
            · exact h12le
        · by_cases h02le : idx 0 <= idx 2
          · rw [if_pos h02le] at hfirst_order
            have h20not : ¬ idx 2 <= idx 0 := by omega
            rw [if_neg h20not] at hsecond_order
            rcases hsecond_order with h23le | h30le
            · exact h23le
            · omega
          · have h20le : idx 2 <= idx 0 := by omega
            rw [if_pos h20le] at hsecond_order
            exact hsecond_order.1
      · intro h21
        exact (by decide : (2 : Fin 4) ≠ 1) (hinj h21)
      · intro h23'
        exact (by decide : (2 : Fin 4) ≠ 3) (hinj h23')
    · refine ⟨⟨hmem 2, ?_⟩, ?_, ?_⟩
      · change
          (if idx 1 <= idx 3 then
            idx 1 <= idx 2 ∧ idx 2 <= idx 3
          else
            idx 1 <= idx 2 ∨ idx 2 <= idx 3)
        rw [if_neg h13le]
        by_cases h02le : idx 0 <= idx 2
        · rw [if_pos h02le] at hfirst_order
          exact Or.inl hfirst_order.2
        · have h20le : idx 2 <= idx 0 := by omega
          rw [if_pos h20le] at hsecond_order
          exact Or.inr hsecond_order.1
      · intro h21
        exact (by decide : (2 : Fin 4) ≠ 1) (hinj h21)
      · intro h23'
        exact (by decide : (2 : Fin 4) ≠ 3) (hinj h23')
  · change
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        Ω (endpoint 3) (endpoint 1) (endpoint 0)
    by_cases h31le : idx 3 <= idx 1
    · refine ⟨⟨hmem 0, ?_⟩, ?_, ?_⟩
      · change
          (if idx 3 <= idx 1 then
            idx 3 <= idx 0 ∧ idx 0 <= idx 1
          else
            idx 3 <= idx 0 ∨ idx 0 <= idx 1)
        rw [if_pos h31le]
        constructor
        · by_cases h02le : idx 0 <= idx 2
          · rw [if_pos h02le] at hfirst_order
            have h20not : ¬ idx 2 <= idx 0 := by omega
            rw [if_neg h20not] at hsecond_order
            rcases hsecond_order with h23le | h30le
            · omega
            · exact h30le
          · have h20le : idx 2 <= idx 0 := by omega
            rw [if_pos h20le] at hsecond_order
            exact hsecond_order.2
        · by_cases h02le : idx 0 <= idx 2
          · rw [if_pos h02le] at hfirst_order
            exact hfirst_order.1
          · have h20le : idx 2 <= idx 0 := by omega
            rw [if_neg h02le] at hfirst_order
            rw [if_pos h20le] at hsecond_order
            rcases hfirst_order with h01le | h12le
            · exact h01le
            · omega
      · intro h03
        exact (by decide : (0 : Fin 4) ≠ 3) (hinj h03)
      · intro h01'
        exact (by decide : (0 : Fin 4) ≠ 1) (hinj h01')
    · refine ⟨⟨hmem 0, ?_⟩, ?_, ?_⟩
      · change
          (if idx 3 <= idx 1 then
            idx 3 <= idx 0 ∧ idx 0 <= idx 1
          else
            idx 3 <= idx 0 ∨ idx 0 <= idx 1)
        rw [if_neg h31le]
        by_cases h02le : idx 0 <= idx 2
        · rw [if_pos h02le] at hfirst_order
          exact Or.inr hfirst_order.1
        · have h20le : idx 2 <= idx 0 := by omega
          rw [if_pos h20le] at hsecond_order
          exact Or.inl hsecond_order.2
      · intro h03
        exact (by decide : (0 : Fin 4) ≠ 3) (hinj h03)
      · intro h01'
        exact (by decide : (0 : Fin 4) ≠ 1) (hinj h01')

def Cross.rotate1 {S : GeneralSociety V} (X : S.Cross) : S.Cross where
  endpoints := {
    endpoint := fun i =>
      if i = 0 then X.endpoints.endpoint 1
      else if i = 1 then X.endpoints.endpoint 2
      else if i = 2 then X.endpoints.endpoint 3
      else X.endpoints.endpoint 0
    endpoint_mem := by
      intro i
      fin_cases i <;> simp [X.endpoints.endpoint_mem]
    endpoint_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact False.elim ((by decide : (1 : Fin 4) ≠ 2)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (1 : Fin 4) ≠ 3)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (1 : Fin 4) ≠ 0)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (2 : Fin 4) ≠ 1)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (2 : Fin 4) ≠ 3)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (2 : Fin 4) ≠ 0)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (3 : Fin 4) ≠ 1)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (3 : Fin 4) ≠ 2)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (3 : Fin 4) ≠ 0)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (0 : Fin 4) ≠ 1)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (0 : Fin 4) ≠ 2)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (0 : Fin 4) ≠ 3)
          (X.endpoints.endpoint_injective hij))
    cyclic_alternating := by
      exact CrossEndpointAlternating.rotate1 X.endpoints.endpoint_mem
        X.endpoints.endpoint_injective X.endpoints.cyclic_alternating
  }
  firstPath := X.secondPath
  secondPath := X.firstPath.reverse
  firstPath_isPath := X.secondPath_isPath
  secondPath_isPath := X.firstPath_isPath.reverse
  firstPath_nontrivial := X.secondPath_nontrivial
  secondPath_nontrivial := by
    simpa using X.firstPath_nontrivial
  paths_disjoint := by
    rw [Set.disjoint_left]
    intro z hzFirst hzSecond
    have hzSecondRev : z ∈ X.firstPath.reverse.support := by
      simpa using hzSecond
    have hzSecond' : z ∈ X.firstPath.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzSecondRev
      exact List.mem_reverse.mp hzSecondRev
    exact Set.disjoint_left.mp X.paths_disjoint hzSecond' hzFirst
  first_internal_boundary := X.second_internal_boundary
  second_internal_boundary := by
    simpa [Walk.internalVertices_reverse] using X.first_internal_boundary

def Cross.rotate2 {S : GeneralSociety V} (X : S.Cross) : S.Cross where
  endpoints := {
    endpoint := fun i =>
      if i = 0 then X.endpoints.endpoint 2
      else if i = 1 then X.endpoints.endpoint 3
      else if i = 2 then X.endpoints.endpoint 0
      else X.endpoints.endpoint 1
    endpoint_mem := by
      intro i
      fin_cases i <;> simp [X.endpoints.endpoint_mem]
    endpoint_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact False.elim ((by decide : (2 : Fin 4) ≠ 3)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (2 : Fin 4) ≠ 0)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (2 : Fin 4) ≠ 1)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (3 : Fin 4) ≠ 2)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (3 : Fin 4) ≠ 0)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (3 : Fin 4) ≠ 1)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (0 : Fin 4) ≠ 2)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (0 : Fin 4) ≠ 3)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (0 : Fin 4) ≠ 1)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (1 : Fin 4) ≠ 2)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (1 : Fin 4) ≠ 3)
          (X.endpoints.endpoint_injective hij))
      · exact False.elim ((by decide : (1 : Fin 4) ≠ 0)
          (X.endpoints.endpoint_injective hij))
    cyclic_alternating := by
      simpa [CrossEndpointAlternating] using
        And.symm X.endpoints.cyclic_alternating
  }
  firstPath := X.firstPath.reverse
  secondPath := X.secondPath.reverse
  firstPath_isPath := X.firstPath_isPath.reverse
  secondPath_isPath := X.secondPath_isPath.reverse
  firstPath_nontrivial := by
    simpa using X.firstPath_nontrivial
  secondPath_nontrivial := by
    simpa using X.secondPath_nontrivial
  paths_disjoint := by
    rw [Set.disjoint_left]
    intro z hzFirst hzSecond
    have hzFirstRev : z ∈ X.firstPath.reverse.support := by
      simpa using hzFirst
    have hzSecondRev : z ∈ X.secondPath.reverse.support := by
      simpa using hzSecond
    have hzFirst' : z ∈ X.firstPath.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzFirstRev
      exact List.mem_reverse.mp hzFirstRev
    have hzSecond' : z ∈ X.secondPath.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzSecondRev
      exact List.mem_reverse.mp hzSecondRev
    exact Set.disjoint_left.mp X.paths_disjoint hzFirst' hzSecond'
  first_internal_boundary := by
    simpa [Walk.internalVertices_reverse] using X.first_internal_boundary
  second_internal_boundary := by
    simpa [Walk.internalVertices_reverse] using X.second_internal_boundary


end GeneralSociety

end Schematic.Math.GraphTheory
