import Schematic.Math.GraphTheory.Embedding.Wagner.CycleData

/-! The two complementary arcs between two vertices of a simple cycle. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner

/-- The two internally disjoint paths between two distinct vertices of a
simple cycle, oriented in the same direction and covering the cycle. -/
structure CycleTwoArcs
    {V : Type u} {G : SimpleGraph V}
    {r x1 x2 : V}
    (C : G.Walk r r) where
  first : G.Walk x1 x2
  second : G.Walk x1 x2
  endpoints_ne : x1 ≠ x2
  first_isPath : first.IsPath
  second_isPath : second.IsPath
  first_support : forall z, z ∈ first.support -> z ∈ C.support
  second_support : forall z, z ∈ second.support -> z ∈ C.support
  first_edges : forall e, e ∈ first.edges -> e ∈ C.edges
  second_edges : forall e, e ∈ second.edges -> e ∈ C.edges
  internally_disjoint :
    Disjoint (Walk.InternalVertices first) (Walk.InternalVertices second)
  cover : forall z, z ∈ C.support -> z ∈ first.support ∨ z ∈ second.support

noncomputable def cycleTwoArcs
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x1 x2 : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hx1 : x1 ∈ C.support)
    (hx2 : x2 ∈ C.support)
    (hne : x1 ≠ x2) :
    CycleTwoArcs C (x1 := x1) (x2 := x2) := by
  classical
  let C' : G.Walk x1 x1 := C.rotate x1 hx1
  have hC' : C'.IsCycle := by
    simpa [C'] using SimpleGraph.Walk.IsCycle.rotate hx1 hC
  have hx2' : x2 ∈ C'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mpr hx2
  let P : G.Walk x1 x2 := C'.takeUntil x2 hx2'
  let D : G.Walk x2 x1 := C'.dropUntil x2 hx2'
  let Q : G.Walk x1 x2 := D.reverse
  have hP : P.IsPath := by
    simpa [P] using hC'.isPath_takeUntil hx2'
  have hD : D.IsPath := by
    have hP_non_nil : ¬ P.Nil := by
      rw [SimpleGraph.Walk.nil_takeUntil]
      exact hne
    have hcycle_append : (P.append D).IsCycle := by
      simpa [P, D] using hC'
    exact hcycle_append.isPath_of_append_right hP_non_nil
  refine {
    first := P
    second := Q
    endpoints_ne := hne
    first_isPath := hP
    second_isPath := by simpa [Q] using hD.reverse
    first_support := ?_
    second_support := ?_
    first_edges := ?_
    second_edges := ?_
    internally_disjoint := ?_
    cover := ?_
  }
  · intro z hz
    have hzC' : z ∈ C'.support :=
      SimpleGraph.Walk.support_takeUntil_subset C' hx2'
        (by simpa [P] using hz)
    exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mp hzC'
  · intro z hz
    have hzD : z ∈ D.support := by
      have hzQ : z ∈ D.reverse.support := by simpa [Q] using hz
      rw [SimpleGraph.Walk.support_reverse] at hzQ
      exact List.mem_reverse.mp hzQ
    have hzC' : z ∈ C'.support :=
      SimpleGraph.Walk.support_dropUntil_subset C' hx2' hzD
    exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mp hzC'
  · intro e he
    have heC' : e ∈ C'.edges :=
      SimpleGraph.Walk.edges_takeUntil_subset C' hx2' he
    exact (SimpleGraph.Walk.rotate_edges C x1 hx1).mem_iff.mp heC'
  · intro e he
    have heD : e ∈ D.edges := by
      rw [SimpleGraph.Walk.edges_reverse] at he
      exact List.mem_reverse.mp he
    have heC' : e ∈ C'.edges :=
      SimpleGraph.Walk.edges_dropUntil_subset C' hx2' heD
    exact (SimpleGraph.Walk.rotate_edges C x1 hx1).mem_iff.mp heC'
  · have hsplit :=
      Walk.IsCycle.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) hC' hx2'
    simpa [P, Q, D, Walk.internalVertices_reverse] using hsplit
  · intro z hzC
    have hzC' : z ∈ C'.support :=
      (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mpr hzC
    have hzAppend : z ∈ (P.append D).support := by
      simpa [P, D, SimpleGraph.Walk.take_spec C' hx2'] using hzC'
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzAppend
    rcases hzAppend with hzP | hzD
    · exact Or.inl hzP
    · right
      have hzQ : z ∈ D.reverse.support := by
        rw [SimpleGraph.Walk.support_reverse]
        exact List.mem_reverse.mpr hzD
      simpa [Q] using hzQ

/-- The edge-containment invariant makes every abstract `CycleTwoArcs.first`
one of the two literal cyclic intervals between its endpoints. -/
theorem CycleTwoArcs.first_eq_forward_or_reverse_dropUntil
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x1 x2 : V} {C : G.Walk r r}
    (A : CycleTwoArcs C (x1 := x1) (x2 := x2))
    (hC : C.IsCycle) (hne : x1 ≠ x2) :
    let hx1C : x1 ∈ C.support :=
      A.first_support x1 A.first.start_mem_support
    let C' := C.rotate x1 hx1C
    let hx2C' : x2 ∈ C'.support :=
      (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1C).mpr
        (A.first_support x2 A.first.end_mem_support)
    A.first = C'.takeUntil x2 hx2C' ∨
      A.first = (C'.dropUntil x2 hx2C').reverse := by
  classical
  let hx1C : x1 ∈ C.support :=
    A.first_support x1 A.first.start_mem_support
  let C' := C.rotate x1 hx1C
  have hC' : C'.IsCycle := by
    simpa [C'] using SimpleGraph.Walk.IsCycle.rotate hx1C hC
  let hx2C' : x2 ∈ C'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1C).mpr
      (A.first_support x2 A.first.end_mem_support)
  let P : G.Walk x1 x2 := C'.takeUntil x2 hx2C'
  let D : G.Walk x2 x1 := C'.dropUntil x2 hx2C'
  let Q : G.Walk x1 x2 := D.reverse
  have hAne : ¬ A.first.Nil := by
    intro hnil
    exact hne hnil.eq
  have hPne : ¬ P.Nil := by
    intro hnil
    exact hne hnil.eq
  have hDne : ¬ D.Nil := by
    intro hnil
    exact hne hnil.eq.symm
  have hPpath : P.IsPath := by
    simpa [P] using hC'.isPath_takeUntil hx2C'
  have hDpath : D.IsPath := by
    have hcycleAppend : (P.append D).IsCycle := by
      simpa [P, D] using hC'
    exact hcycleAppend.isPath_of_append_right hPne
  have hQpath : Q.IsPath := by
    simpa [Q] using hDpath.reverse
  have hAEdgesC' : forall e, e ∈ A.first.edges -> e ∈ C'.edges := by
    intro e he
    exact (SimpleGraph.Walk.rotate_edges C x1 hx1C).mem_iff.mpr
      (A.first_edges e he)
  have hPEdgesC' : forall e, e ∈ P.edges -> e ∈ C'.edges := by
    intro e he
    exact SimpleGraph.Walk.edges_takeUntil_subset C' hx2C' he
  have hQEdgesC' : forall e, e ∈ Q.edges -> e ∈ C'.edges := by
    intro e he
    have heD : e ∈ D.edges := by
      change e ∈ D.reverse.edges at he
      rw [SimpleGraph.Walk.edges_reverse] at he
      exact List.mem_reverse.mp he
    exact SimpleGraph.Walk.edges_dropUntil_subset C' hx2C' heD
  have hAdjCycle : C'.toSubgraph.Adj x1 A.first.snd := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    exact hAEdgesC' _ (A.first.mk_start_snd_mem_edges hAne)
  have hSndChoice :
      A.first.snd = C'.snd ∨ A.first.snd = C'.penultimate := by
    have hmem : A.first.snd ∈ C'.toSubgraph.neighborSet x1 := hAdjCycle
    rw [hC'.neighborSet_toSubgraph_endpoint] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hPsnd : P.snd = C'.snd := by
    exact SimpleGraph.Walk.snd_takeUntil hne.symm C' hx2C'
  have hCedgesNe : C'.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr hC'.not_nil
  rcases hSndChoice with hAforward | hAbackward
  · let T := C'.reverse.tail.reverse
    have hTpath : T.IsPath := by
      exact hC'.reverse.isPath_tail.reverse
    have subsetForward :
        forall (W : G.Walk x1 x2), W.IsPath -> ¬ W.Nil ->
          W.snd = C'.snd ->
          (forall e, e ∈ W.edges -> e ∈ C'.edges) ->
          forall e, e ∈ W.edges -> e ∈ T.edges := by
      intro W hWpath hWne hWsnd hWEdges e he
      have heC' : e ∈ C'.edges := hWEdges e he
      have heNeLast : e ≠ C'.edges.getLast hCedgesNe := by
        intro heLast
        have hlastW : C'.edges.getLast hCedgesNe ∈ W.edges := by
          simpa [heLast] using he
        have hremoved : s(x1, C'.penultimate) ∈ W.edges := by
          simpa [Sym2.eq_swap] using hlastW
        have hpen : C'.penultimate = W.snd :=
          hWpath.eq_snd_of_mem_edges hremoved
        exact hC'.snd_ne_penultimate (hpen.trans hWsnd).symm
      have heDrop : e ∈ C'.edges.dropLast :=
        List.mem_dropLast_of_mem_of_ne_getLast heC' heNeLast
      change e ∈ C'.reverse.tail.reverse.edges
      rw [SimpleGraph.Walk.edges_reverse]
      have htailEdges : C'.reverse.tail.edges = C'.edges.reverse.drop 1 := by
        change (C'.reverse.drop 1).edges = C'.edges.reverse.drop 1
        rw [SimpleGraph.Walk.edges_drop, SimpleGraph.Walk.edges_reverse]
      rw [htailEdges]
      simpa [List.tail_reverse] using heDrop
    have hAT : forall e, e ∈ A.first.edges -> e ∈ T.edges :=
      subsetForward A.first A.first_isPath hAne hAforward hAEdgesC'
    have hPT : forall e, e ∈ P.edges -> e ∈ T.edges :=
      subsetForward P hPpath hPne hPsnd hPEdgesC'
    left
    exact Walk.IsPath.eq_of_edges_subset_of_common_path
      hTpath hPpath A.first_isPath hPT hAT
  · let T : G.Walk x1 C'.snd := C'.tail.reverse
    have hTpath : T.IsPath := hC'.isPath_tail.reverse
    have subsetBackward :
        forall (W : G.Walk x1 x2),
          (forall e, e ∈ W.edges -> e ∈ C'.edges) ->
          C'.edges.head hCedgesNe ∉ W.edges ->
          forall e, e ∈ W.edges -> e ∈ T.edges := by
      intro W hWEdges hheadNot e he
      have heC' : e ∈ C'.edges := hWEdges e he
      have heTail : e ∈ C'.edges.tail := by
        have hcons := List.cons_head_tail hCedgesNe
        rw [← hcons, List.mem_cons] at heC'
        exact heC'.resolve_left (fun heHead => hheadNot (by simpa [heHead] using he))
      change e ∈ C'.tail.reverse.edges
      rw [SimpleGraph.Walk.edges_reverse]
      apply List.mem_reverse.mpr
      simpa [SimpleGraph.Walk.tail, SimpleGraph.Walk.edges_drop] using heTail
    have hheadNotA : C'.edges.head hCedgesNe ∉ A.first.edges := by
      intro hhead
      have hremoved : s(x1, C'.snd) ∈ A.first.edges := by
        simpa using hhead
      have hsnd : C'.snd = A.first.snd :=
        A.first_isPath.eq_snd_of_mem_edges hremoved
      exact hC'.snd_ne_penultimate (hsnd.trans hAbackward)
    have hsplitTrail : (P.append D).IsTrail := by
      simpa [P, D] using hC'.isTrail
    have hPDdisjoint :
        forall e, e ∈ P.edges -> e ∈ D.edges -> False := by
      rw [SimpleGraph.Walk.isTrail_def,
        SimpleGraph.Walk.edges_append, List.nodup_append] at hsplitTrail
      intro e heP heD
      exact hsplitTrail.2.2 e heP e heD rfl
    have hheadP : C'.edges.head hCedgesNe ∈ P.edges := by
      have hfirstP : s(x1, P.snd) ∈ P.edges :=
        P.mk_start_snd_mem_edges hPne
      simpa [hPsnd] using hfirstP
    have hheadNotQ : C'.edges.head hCedgesNe ∉ Q.edges := by
      intro hheadQ
      have hheadD : C'.edges.head hCedgesNe ∈ D.edges := by
        change C'.edges.head hCedgesNe ∈ D.reverse.edges at hheadQ
        rw [SimpleGraph.Walk.edges_reverse] at hheadQ
        exact List.mem_reverse.mp hheadQ
      exact hPDdisjoint _ hheadP hheadD
    have hAT : forall e, e ∈ A.first.edges -> e ∈ T.edges :=
      subsetBackward A.first hAEdgesC' hheadNotA
    have hQT : forall e, e ∈ Q.edges -> e ∈ T.edges :=
      subsetBackward Q hQEdgesC' hheadNotQ
    right
    exact Walk.IsPath.eq_of_edges_subset_of_common_path
      hTpath hQpath A.first_isPath hQT hAT

theorem CycleTwoArcs.support_inter_subset_endpoints
    {V : Type u} {G : SimpleGraph V}
    {r x1 x2 z : V} {C : G.Walk r r}
    (A : CycleTwoArcs C (x1 := x1) (x2 := x2))
    (hz1 : z ∈ A.first.support)
    (hz2 : z ∈ A.second.support) :
    z = x1 ∨ z = x2 := by
  by_cases hzx1 : z = x1
  · exact Or.inl hzx1
  by_cases hzx2 : z = x2
  · exact Or.inr hzx2
  have hzFirst : z ∈ Walk.InternalVertices A.first :=
    ⟨hz1, hzx1, hzx2⟩
  have hzSecond : z ∈ Walk.InternalVertices A.second :=
    ⟨hz2, hzx1, hzx2⟩
  exact False.elim
    (Set.disjoint_left.mp A.internally_disjoint hzFirst hzSecond)

/-- Exchange the two complementary arcs of a cycle decomposition. -/
def CycleTwoArcs.swap
    {V : Type u} {G : SimpleGraph V}
    {r x1 x2 : V} {C : G.Walk r r}
    (A : CycleTwoArcs C (x1 := x1) (x2 := x2)) :
    CycleTwoArcs C (x1 := x1) (x2 := x2) where
  first := A.second
  second := A.first
  endpoints_ne := A.endpoints_ne
  first_isPath := A.second_isPath
  second_isPath := A.first_isPath
  first_support := A.second_support
  second_support := A.first_support
  first_edges := A.second_edges
  second_edges := A.first_edges
  internally_disjoint := A.internally_disjoint.symm
  cover := by
    intro z hzC
    rcases A.cover z hzC with hzFirst | hzSecond
    · exact Or.inr hzFirst
    · exact Or.inl hzSecond

end Wagner

end FourColor

end Schematic.Math.GraphTheory
