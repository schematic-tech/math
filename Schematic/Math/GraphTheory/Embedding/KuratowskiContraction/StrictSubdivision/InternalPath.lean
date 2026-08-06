import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.StrictSubdivision.CleanLift

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- If the collapsed vertex occurs internally on a quotient source-edge path,
then both halves adjacent to it expose original neighbours on one of the two
contracted endpoints.  This is the local data needed to replace the internal
quotient occurrence by the original edge `ab`. -/
theorem strictSubdivisionModel_collapseEdge_internal_path_two_sides
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy)) :
    Exists fun v₁ : V =>
      Exists fun hv₁ : v₁ ∉ ({a, b} : Set V) =>
        Exists fun v₂ : V =>
          Exists fun hv₂ : v₂ ∉ ({a, b} : Set V) =>
            ((M.edgePath hxy).dropUntil
                (none : (GraphContraction.collapseEdge G hab).Target)
                hnone.1).snd =
                GraphContraction.collapseEdgeOutside G hab v₁ hv₁ ∧
              (G.Adj a v₁ ∨ G.Adj b v₁) ∧
              ((M.edgePath hxy).reverse.dropUntil
                (none : (GraphContraction.collapseEdge G hab).Target)
                (by
                  rw [SimpleGraph.Walk.support_reverse]
                  exact List.mem_reverse.mpr hnone.1)).snd =
                GraphContraction.collapseEdgeOutside G hab v₂ hv₂ ∧
              (G.Adj a v₂ ∨ G.Adj b v₂) := by
  classical
  let p := M.edgePath hxy
  have hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target) :=
    hnone.2.2.symm
  have hfirst₁ :=
    GraphContraction.collapseEdge_walk_first_step_side G hab
      (p.dropUntil
        (none : (GraphContraction.collapseEdge G hab).Target) hnone.1)
      hy
  have hnone_rev :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        p.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr (by simpa [p] using hnone.1)
  have hx :
      M.branchVertex x ≠
        (none : (GraphContraction.collapseEdge G hab).Target) :=
    hnone.2.1.symm
  have hfirst₂ :=
    GraphContraction.collapseEdge_walk_first_step_side G hab
      (p.reverse.dropUntil
        (none : (GraphContraction.collapseEdge G hab).Target) hnone_rev)
      hx
  rcases hfirst₁ with ⟨v₁, hv₁, hsnd₁, hside₁⟩
  rcases hfirst₂ with ⟨v₂, hv₂, hsnd₂, hside₂⟩
  exact ⟨v₁, hv₁, v₂, hv₂, by simpa [p] using hsnd₁, hside₁,
    by simpa [p] using hsnd₂, hside₂⟩

/-- If the collapsed vertex occurs internally on a quotient edge path, both
clean tails on either side lift back to source-graph paths.  The right tail is
oriented from the source-side attachment to the `y` branch vertex; the left
tail is extracted from the reversed quotient path and is oriented from the
other source-side attachment to the `x` branch vertex. -/
theorem strictSubdivisionModel_collapseEdge_internal_path_tail_lifts
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy)) :
    Exists fun hx :
        M.branchVertex x ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
      Exists fun hy :
        M.branchVertex y ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
        Exists fun vR : V =>
          vR ∉ ({a, b} : Set V) ∧
            Exists fun qR : G.Walk vR
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) hy) =>
              Exists fun vL : V =>
                vL ∉ ({a, b} : Set V) ∧
                  Exists fun qL : G.Walk vL
                    (GraphContraction.collapseEdgeUncollapse G hab
                      (M.branchVertex x) hx) =>
                      (G.Adj a vR ∨ G.Adj b vR) ∧ qR.IsPath ∧
                      (forall t : V, t ∈ qR.support ->
                        t ∉ ({a, b} : Set V)) ∧
                      (forall t : V, t ∈ qR.support ->
                        Exists fun qv :
                            (GraphContraction.collapseEdge G hab).Target =>
                          qv ∈ (M.edgePath hxy).support ∧
                            Exists fun hqv_ne :
                              qv ≠
                                (none :
                                  (GraphContraction.collapseEdge G hab).Target) =>
                              GraphContraction.collapseEdgeUncollapse
                                G hab qv hqv_ne = t) ∧
                      (G.Adj a vL ∨ G.Adj b vL) ∧ qL.IsPath ∧
                        (forall t : V, t ∈ qL.support ->
                          t ∉ ({a, b} : Set V)) ∧
                        (forall t : V, t ∈ qL.support ->
                          Exists fun qv :
                              (GraphContraction.collapseEdge G hab).Target =>
                            qv ∈ (M.edgePath hxy).support ∧
                              Exists fun hqv_ne :
                                qv ≠
                                  (none :
                                    (GraphContraction.collapseEdge G hab).Target) =>
                                GraphContraction.collapseEdgeUncollapse
                                  G hab qv hqv_ne = t) ∧
                        Disjoint
                          {t : V | t ∈ qR.support}
                          {t : V | t ∈ qL.support} ∧
                        vL ≠ vR := by
  classical
  let p := M.edgePath hxy
  have hp : p.IsPath := by
    simpa [p] using M.edgePath_isPath hxy
  have hx :
      M.branchVertex x ≠
        (none : (GraphContraction.collapseEdge G hab).Target) :=
    hnone.2.1.symm
  have hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target) :=
    hnone.2.2.symm
  obtain ⟨vR, hvR, vL, hvL, hsndR, hsideR, hsndL, hsideL⟩ :=
    strictSubdivisionModel_collapseEdge_internal_path_two_sides
      hab M hxy hnone
  let pR : (GraphContraction.collapseEdge G hab).graph.Walk
      (none : (GraphContraction.collapseEdge G hab).Target)
      (M.branchVertex y) :=
    p.dropUntil (none : (GraphContraction.collapseEdge G hab).Target)
      hnone.1
  have hpR : pR.IsPath := by
    simpa [pR, p] using hp.dropUntil hnone.1
  have hpR_not_nil : ¬ pR.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pR) hy.symm
  have hsndR_ne :
      pR.snd ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    rw [hsndR]
    simp [GraphContraction.collapseEdgeOutside]
  have hpavoidR : forall t, t ∈ pR.tail.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro t ht ht_none
    have hnone_tail :
        (none : (GraphContraction.collapseEdge G hab).Target) ∈
          pR.tail.support := by
      simpa [ht_none] using ht
    have hnone_tail_list :
        (none : (GraphContraction.collapseEdge G hab).Target) ∈
          pR.support.tail := by
      rwa [← pR.support_tail_of_not_nil hpR_not_nil]
    exact Walk.IsPath.start_notMem_tail_support hpR hnone_tail_list
  let qR0 :=
    GraphContraction.collapseEdgeWalkOutside G hab hsndR_ne hy pR.tail
      hpavoidR
  have hqR0 : qR0.IsPath :=
    GraphContraction.collapseEdgeWalkOutside_isPath G hab hsndR_ne hy
      pR.tail hpavoidR hpR.tail
  have hstartR :
      GraphContraction.collapseEdgeUncollapse G hab pR.snd hsndR_ne = vR := by
    calc
      GraphContraction.collapseEdgeUncollapse G hab pR.snd hsndR_ne =
          GraphContraction.collapseEdgeUncollapse G hab
            (GraphContraction.collapseEdgeOutside G hab vR hvR)
            (by simp [GraphContraction.collapseEdgeOutside]) :=
        GraphContraction.collapseEdgeUncollapse_congr G hab hsndR_ne
          (by simp [GraphContraction.collapseEdgeOutside]) hsndR
      _ = vR :=
        GraphContraction.collapseEdgeUncollapse_outside G hab hvR
          (by simp [GraphContraction.collapseEdgeOutside])
  let qR : G.Walk vR
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy) :=
    qR0.copy hstartR rfl
  have hqR : qR.IsPath := by
    simpa [qR] using (SimpleGraph.Walk.isPath_copy qR0 hstartR rfl).mpr hqR0
  have hqR_outside :
      forall t : V, t ∈ qR.support -> t ∉ ({a, b} : Set V) := by
    intro t ht
    exact
      GraphContraction.collapseEdgeWalkOutside_support_outside G hab hsndR_ne
        hy pR.tail hpavoidR
        (by simpa [qR, SimpleGraph.Walk.support_copy] using ht)
  have hqR_reflect :
      forall t : V, t ∈ qR.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hxy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t := by
    intro t ht
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab hsndR_ne hy pR.tail hpavoidR
          (by simpa [qR, SimpleGraph.Walk.support_copy] using ht) with
      ⟨qv, hqv_tail, hqv_ne, hqv_eq⟩
    have hqv_tail_list : qv ∈ pR.support.tail := by
      rwa [← pR.support_tail_of_not_nil hpR_not_nil]
    have hqv_pR : qv ∈ pR.support := List.mem_of_mem_tail hqv_tail_list
    have hqv_p : qv ∈ p.support :=
      SimpleGraph.Walk.support_dropUntil_subset p hnone.1 hqv_pR
    exact ⟨qv, by simpa [p] using hqv_p, hqv_ne, hqv_eq⟩
  have hnone_rev :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        p.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr (by simpa [p] using hnone.1)
  let pL : (GraphContraction.collapseEdge G hab).graph.Walk
      (none : (GraphContraction.collapseEdge G hab).Target)
      (M.branchVertex x) :=
    p.reverse.dropUntil
      (none : (GraphContraction.collapseEdge G hab).Target) hnone_rev
  have hpL : pL.IsPath := by
    simpa [pL, p] using hp.reverse.dropUntil hnone_rev
  have hpL_not_nil : ¬ pL.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pL) hx.symm
  have hsndL_ne :
      pL.snd ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    rw [hsndL]
    simp [GraphContraction.collapseEdgeOutside]
  have hpavoidL : forall t, t ∈ pL.tail.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro t ht ht_none
    have hnone_tail :
        (none : (GraphContraction.collapseEdge G hab).Target) ∈
          pL.tail.support := by
      simpa [ht_none] using ht
    have hnone_tail_list :
        (none : (GraphContraction.collapseEdge G hab).Target) ∈
          pL.support.tail := by
      rwa [← pL.support_tail_of_not_nil hpL_not_nil]
    exact Walk.IsPath.start_notMem_tail_support hpL hnone_tail_list
  let qL0 :=
    GraphContraction.collapseEdgeWalkOutside G hab hsndL_ne hx pL.tail
      hpavoidL
  have hqL0 : qL0.IsPath :=
    GraphContraction.collapseEdgeWalkOutside_isPath G hab hsndL_ne hx
      pL.tail hpavoidL hpL.tail
  have hstartL :
      GraphContraction.collapseEdgeUncollapse G hab pL.snd hsndL_ne = vL := by
    calc
      GraphContraction.collapseEdgeUncollapse G hab pL.snd hsndL_ne =
          GraphContraction.collapseEdgeUncollapse G hab
            (GraphContraction.collapseEdgeOutside G hab vL hvL)
            (by simp [GraphContraction.collapseEdgeOutside]) :=
        GraphContraction.collapseEdgeUncollapse_congr G hab hsndL_ne
          (by simp [GraphContraction.collapseEdgeOutside]) hsndL
      _ = vL :=
        GraphContraction.collapseEdgeUncollapse_outside G hab hvL
          (by simp [GraphContraction.collapseEdgeOutside])
  let qL : G.Walk vL
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex x) hx) :=
    qL0.copy hstartL rfl
  have hqL : qL.IsPath := by
    simpa [qL] using (SimpleGraph.Walk.isPath_copy qL0 hstartL rfl).mpr hqL0
  have hqL_outside :
      forall t : V, t ∈ qL.support -> t ∉ ({a, b} : Set V) := by
    intro t ht
    exact
      GraphContraction.collapseEdgeWalkOutside_support_outside G hab hsndL_ne
        hx pL.tail hpavoidL
        (by simpa [qL, SimpleGraph.Walk.support_copy] using ht)
  have hqL_reflect :
      forall t : V, t ∈ qL.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hxy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t := by
    intro t ht
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab hsndL_ne hx pL.tail hpavoidL
          (by simpa [qL, SimpleGraph.Walk.support_copy] using ht) with
      ⟨qv, hqv_tail, hqv_ne, hqv_eq⟩
    have hqv_tail_list : qv ∈ pL.support.tail := by
      rwa [← pL.support_tail_of_not_nil hpL_not_nil]
    have hqv_pL : qv ∈ pL.support := List.mem_of_mem_tail hqv_tail_list
    have hqv_prev : qv ∈ p.reverse.support :=
      SimpleGraph.Walk.support_dropUntil_subset p.reverse hnone_rev hqv_pL
    have hqv_p : qv ∈ p.support := by
      rw [SimpleGraph.Walk.support_reverse] at hqv_prev
      exact List.mem_reverse.mp hqv_prev
    exact ⟨qv, by simpa [p] using hqv_p, hqv_ne, hqv_eq⟩
  have hqR_qL_disjoint :
      Disjoint
        {t : V | t ∈ qR.support}
        {t : V | t ∈ qL.support} := by
    rw [Set.disjoint_left]
    intro t htR htL
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab hsndR_ne hy pR.tail hpavoidR
          (by simpa [qR, SimpleGraph.Walk.support_copy] using htR) with
      ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab hsndL_ne hx pL.tail hpavoidL
          (by simpa [qL, SimpleGraph.Walk.support_copy] using htL) with
      ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
    have hqv_rv : qv = rv :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
        (hqv_eq.trans hrv_eq.symm)
    have htail_disjoint :
        Disjoint
          {t : (GraphContraction.collapseEdge G hab).Target |
            t ∈ pR.tail.support}
          {t : (GraphContraction.collapseEdge G hab).Target |
            t ∈ pL.tail.support} := by
      simpa [pR, pL, p] using
        (Walk.IsPath.dropUntil_tail_support_disjoint_reverse_dropUntil_tail_support_of_internal
          hp hnone)
    exact Set.disjoint_left.mp htail_disjoint hqv_mem
      (by simpa [hqv_rv] using hrv_mem)
  have hsnd_split_ne : pR.snd ≠ pL.snd := by
    simpa [pR, pL, p] using
      Walk.IsPath.snd_dropUntil_ne_snd_reverse_dropUntil_of_internal hp hnone
  have hvL_ne_vR : vL ≠ vR := by
    intro hv_eq
    apply hsnd_split_ne
    calc
      pR.snd = GraphContraction.collapseEdgeOutside G hab vR hvR := hsndR
      _ = GraphContraction.collapseEdgeOutside G hab vL hvL := by
        cases hv_eq
        rfl
      _ = pL.snd := hsndL.symm
  exact ⟨hx, hy, vR, hvR, qR, vL, hvL, qL, hsideR, hqR, hqR_outside,
    hqR_reflect, hsideL, hqL, hqL_outside, hqL_reflect, hqR_qL_disjoint,
    hvL_ne_vR⟩

/-- The short middle replacement associated to an internal occurrence of the
collapsed vertex is a genuine source path.  This isolates the source-side
`a`/`b` bridge used between the two lifted clean tails. -/
theorem strictSubdivisionModel_collapseEdge_internal_middle_bridge
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy)) :
    Exists fun vR : V =>
      Exists fun vL : V =>
        vR ∉ ({a, b} : Set V) ∧ vL ∉ ({a, b} : Set V) ∧
          Exists fun bridge : G.Walk vL vR =>
            bridge.IsPath ∧
              {z : V | z ∈ bridge.support} ⊆ ({a, b, vL, vR} : Set V) := by
  classical
  obtain ⟨_hx, _hy, vR, hvR, _qR, vL, hvL, _qL,
    hsideR, _hqR, _hqR_out, _hqR_reflect, hsideL, _hqL, _hqL_out,
    _hqL_reflect, _hdisj, hne⟩ :=
    strictSubdivisionModel_collapseEdge_internal_path_tail_lifts
      hab M hxy hnone
  let bridge : G.Walk vL vR :=
    Walk.pairAttachmentBridge hab hsideL hsideR
  have hbridge : bridge.IsPath := by
    simpa [bridge] using
      Walk.pairAttachmentBridge_isPath hab hsideL hsideR hvL hvR hne
  have hsupport :
          {z : V | z ∈ bridge.support} ⊆ ({a, b, vL, vR} : Set V) := by
    simpa [bridge] using
      Walk.pairAttachmentBridge_support_subset hab hsideL hsideR
  exact ⟨vR, vL, hvR, hvL, bridge, hbridge, hsupport⟩

/-- Replace an internal occurrence of the collapsed quotient vertex on a
single quotient model path by an actual source path through the contracted
edge endpoints.  This is the checked path-splicing core of the
Makarychev/Skopenkov uncontraction step. -/
theorem strictSubdivisionModel_collapseEdge_internal_path_replacement
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy)) :
    Exists fun hx :
        M.branchVertex x ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
      Exists fun hy :
        M.branchVertex y ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
        Exists fun r : G.Walk
          (GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex x) hx)
          (GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex y) hy) =>
          r.IsPath ∧
            forall t : V, t ∈ r.support ->
              t ∈ ({a, b} : Set V) ∨
                Exists fun qv :
                    (GraphContraction.collapseEdge G hab).Target =>
                  qv ∈ (M.edgePath hxy).support ∧
                    Exists fun hqv_ne :
                      qv ≠
                        (none :
                          (GraphContraction.collapseEdge G hab).Target) =>
                      GraphContraction.collapseEdgeUncollapse
                        G hab qv hqv_ne = t := by
  classical
  obtain ⟨hx, hy, vR, hvR, qR, vL, hvL, qL,
    hsideR, hqR, hqR_out, hqR_reflect, hsideL, hqL, hqL_out,
    hqL_reflect, hdisj, hne⟩ :=
    strictSubdivisionModel_collapseEdge_internal_path_tail_lifts
      hab M hxy hnone
  let bridge : G.Walk vL vR :=
    Walk.pairAttachmentBridge hab hsideL hsideR
  have hbridge : bridge.IsPath := by
    simpa [bridge] using
      Walk.pairAttachmentBridge_isPath hab hsideL hsideR hvL hvR hne
  have hbridge_support :
      {z : V | z ∈ bridge.support} ⊆ ({a, b, vL, vR} : Set V) := by
    simpa [bridge] using
      Walk.pairAttachmentBridge_support_subset hab hsideL hsideR
  have hbridge_qR_clean :
      forall z : V, z ∈ bridge.support -> z ∈ qR.support -> z = vR := by
    intro z hzbridge hzqR
    have hz_cases : z = a ∨ z = b ∨ z = vL ∨ z = vR := by
      have hzset : z ∈ ({a, b, vL, vR} : Set V) :=
        hbridge_support hzbridge
      simp at hzset
      tauto
    rcases hz_cases with rfl | rfl | rfl | rfl
    · exact False.elim (hqR_out _ hzqR (by simp))
    · exact False.elim (hqR_out _ hzqR (by simp))
    · exact False.elim
        (Set.disjoint_left.mp hdisj hzqR qL.start_mem_support)
    · rfl
  have hbridge_qR : (bridge.append qR).IsPath :=
    Walk.IsPath.append_of_support_inter_eq_endpoint hbridge hqR
      hbridge_qR_clean
  have hqL_bridge_qR_clean :
      forall z : V, z ∈ qL.reverse.support ->
        z ∈ (bridge.append qR).support -> z = vL := by
    intro z hzqLrev hzrest
    have hzqL : z ∈ qL.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzqLrev
      exact List.mem_reverse.mp hzqLrev
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzrest
    rcases hzrest with hzbridge | hzqR
    · have hz_cases : z = a ∨ z = b ∨ z = vL ∨ z = vR := by
        have hzset : z ∈ ({a, b, vL, vR} : Set V) :=
          hbridge_support hzbridge
        simp at hzset
        tauto
      rcases hz_cases with rfl | rfl | rfl | rfl
      · exact False.elim (hqL_out _ hzqL (by simp))
      · exact False.elim (hqL_out _ hzqL (by simp))
      · rfl
      · exact False.elim
          (Set.disjoint_left.mp hdisj qR.start_mem_support hzqL)
    · exact False.elim (Set.disjoint_left.mp hdisj hzqR hzqL)
  let r : G.Walk
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex x) hx)
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy) :=
    qL.reverse.append (bridge.append qR)
  have hr : r.IsPath := by
    simpa [r] using
      Walk.IsPath.append_of_support_inter_eq_endpoint hqL.reverse
        hbridge_qR hqL_bridge_qR_clean
  have hr_support :
      forall t : V, t ∈ r.support ->
        t ∈ ({a, b} : Set V) ∨
          Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
            qv ∈ (M.edgePath hxy).support ∧
              Exists fun hqv_ne :
                qv ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t := by
    intro t ht
    rw [SimpleGraph.Walk.mem_support_append_iff] at ht
    rcases ht with htqLrev | htrest
    · have htqL : t ∈ qL.support := by
        rw [SimpleGraph.Walk.support_reverse] at htqLrev
        exact List.mem_reverse.mp htqLrev
      exact Or.inr (hqL_reflect t htqL)
    · rw [SimpleGraph.Walk.mem_support_append_iff] at htrest
      rcases htrest with htbridge | htqR
      · have ht_cases : t = a ∨ t = b ∨ t = vL ∨ t = vR := by
          have htset : t ∈ ({a, b, vL, vR} : Set V) :=
            hbridge_support htbridge
          simp at htset
          tauto
        rcases ht_cases with rfl | rfl | rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inl (by simp)
        · exact Or.inr (hqL_reflect _ qL.start_mem_support)
        · exact Or.inr (hqR_reflect _ qR.start_mem_support)
      · exact Or.inr (hqR_reflect t htqR)
  exact ⟨hx, hy, r, hr, hr_support⟩

theorem strictSubdivisionModel_collapseEdge_internal_path_replacement_with_branch
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy))
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun r : G.Walk
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex x) (hbranch x))
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) (hbranch y)) =>
      r.IsPath ∧
        forall t : V, t ∈ r.support ->
          t ∈ ({a, b} : Set V) ∨
            Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
              qv ∈ (M.edgePath hxy).support ∧
                Exists fun hqv_ne :
                  qv ≠
                    (none : (GraphContraction.collapseEdge G hab).Target) =>
                  GraphContraction.collapseEdgeUncollapse
                    G hab qv hqv_ne = t := by
  classical
  rcases
      strictSubdivisionModel_collapseEdge_internal_path_replacement
        hab M hxy hnone with
    ⟨hx, hy, r0, hr0, hsupp0⟩
  have hstart :
      GraphContraction.collapseEdgeUncollapse G hab (M.branchVertex x) hx =
        GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex x) (hbranch x) :=
    GraphContraction.collapseEdgeUncollapse_congr G hab hx (hbranch x) rfl
  have hend :
      GraphContraction.collapseEdgeUncollapse G hab (M.branchVertex y) hy =
        GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex y) (hbranch y) :=
    GraphContraction.collapseEdgeUncollapse_congr G hab hy (hbranch y) rfl
  let r := r0.copy hstart hend
  have hr : r.IsPath := by
    simpa [r] using (SimpleGraph.Walk.isPath_copy r0 hstart hend).mpr hr0
  have hsupp :
      forall t : V, t ∈ r.support ->
        t ∈ ({a, b} : Set V) ∨
          Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
            qv ∈ (M.edgePath hxy).support ∧
              Exists fun hqv_ne :
                qv ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t := by
    intro t ht
    exact hsupp0 t (by simpa [r, SimpleGraph.Walk.support_copy] using ht)
  exact ⟨r, hr, hsupp⟩

theorem strictSubdivisionModel_collapseEdge_internal_all_branches_avoid_collapsed
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy)) :
    forall w : W,
      M.branchVertex w ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
  intro w hw
  exact M.no_internal_branch_vertices' hxy hnone w hw.symm

theorem strictSubdivisionModel_collapseEdge_internal_replacement_no_internal_branch_vertices
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target))
    {r : G.Walk
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex x) (hbranch x))
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) (hbranch y))}
    (hr_support :
      forall t : V, t ∈ r.support ->
        t ∈ ({a, b} : Set V) ∨
          Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
            qv ∈ (M.edgePath hxy).support ∧
              Exists fun hqv_ne :
                qv ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t)
    {z : V}
    (hz : z ∈ Walk.InternalVertices r)
    (w : W) :
    z ≠
      GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex w) (hbranch w) := by
  intro hzw
  rcases hr_support z hz.1 with hzpair | hzreflect
  · have hbranch_out :=
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab (hbranch w)
    exact hbranch_out (by simpa [hzw] using hzpair)
  · rcases hzreflect with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    have hqv_branch : qv = M.branchVertex w :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne
        (hbranch w) (hqv_eq.trans hzw)
    have hw_endpoint : w = x ∨ w = y := by
      have hmem : M.branchVertex w ∈ (M.edgePath hxy).support := by
        simpa [hqv_branch] using hqv_mem
      exact (M.branchVertex_mem_edgePath_support_iff hxy).mp hmem
    rcases hw_endpoint with rfl | rfl
    · exact hz.2.1 hzw
    · exact hz.2.2 hzw

theorem strictSubdivisionModel_collapseEdge_internal_replacement_disjoint_clean_lift
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target))
    {x y s t : W}
    (hxy : K.Adj x y)
    (hst : K.Adj s t)
    (hne : Not ((x = s ∧ y = t) ∨ (x = t ∧ y = s)))
    {r : G.Walk
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex x) (hbranch x))
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) (hbranch y))}
    (hr_support :
      forall z : V, z ∈ r.support ->
        z ∈ ({a, b} : Set V) ∨
          Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
            qv ∈ (M.edgePath hxy).support ∧
              Exists fun hqv_ne :
                qv ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z)
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    Disjoint
      (Walk.InternalVertices r)
      (Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          (hbranch s) (hbranch t) (M.edgePath hst) havoid)) := by
  classical
  rw [Set.disjoint_left]
  intro z hzrep hzclean
  rcases hr_support z hzrep.1 with hzpair | hzreflect
  · have hzclean_out :=
      GraphContraction.collapseEdgeWalkOutside_support_outside G hab
        (hbranch s) (hbranch t) (M.edgePath hst) havoid hzclean.1
    exact hzclean_out hzpair
  · rcases hzreflect with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab (hbranch s) (hbranch t) (M.edgePath hst) havoid hzclean.1 with
      ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
    have hqv_rv : qv = rv :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
        (hqv_eq.trans hrv_eq.symm)
    have hqv_internal : qv ∈ Walk.InternalVertices (M.edgePath hxy) := by
      refine ⟨hqv_mem, ?_, ?_⟩
      · intro hqx
        have hz_start :
            z = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex x) (hbranch x) := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
              hqv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex x) (hbranch x) :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
                (hbranch x) hqx
        exact hzrep.2.1 hz_start
      · intro hqy
        have hz_end :
            z = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) (hbranch y) := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
              hqv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) (hbranch y) :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
                (hbranch y) hqy
        exact hzrep.2.2 hz_end
    have hrv_internal : rv ∈ Walk.InternalVertices (M.edgePath hst) := by
      refine ⟨hrv_mem, ?_, ?_⟩
      · intro hrs
        have hz_start :
            z = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex s) (hbranch s) := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
              hrv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) (hbranch s) :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
                (hbranch s) hrs
        exact hzclean.2.1 hz_start
      · intro hrt
        have hz_end :
            z = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex t) (hbranch t) := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
              hrv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex t) (hbranch t) :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
                (hbranch t) hrt
        exact hzclean.2.2 hz_end
    exact Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hxy hst hne)
      hqv_internal (by simpa [hqv_rv] using hrv_internal)

theorem strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y x' y' : W}
    (hxy : K.Adj x y)
    (hx'y' : K.Adj x' y')
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy))
    (hne : Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))) :
    forall t, t ∈ (M.edgePath hx'y').support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target) := by
  have hbranch_ne :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target) :=
    strictSubdivisionModel_collapseEdge_internal_all_branches_avoid_collapsed
      hab M hxy hnone
  intro t ht ht_none
  have hnone_other :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hx'y') := by
    refine ⟨by simpa [ht_none] using ht, ?_, ?_⟩
    · exact (hbranch_ne x').symm
    · exact (hbranch_ne y').symm
  exact Set.disjoint_left.mp
    (M.internally_disjoint_edge_paths' hxy hx'y' hne)
    hnone hnone_other

/-- The source-side branch vertex obtained by uncollapsing every quotient
branch vertex once a quotient model path uses the collapsed edge vertex
internally. -/
noncomputable def strictSubdivisionModel_collapseEdge_internal_branchVertex
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target)) :
    W -> V :=
  fun w => GraphContraction.collapseEdgeUncollapse G hab
    (M.branchVertex w) (hbranch w)

/-- The edge-path selector for the internal-edge uncontraction branch.  The
distinguished quotient source-edge path is replaced by the repaired source
path `rxy`, the opposite orientation uses `rxy.reverse`, and every other
source edge is lifted cleanly because the collapsed vertex is forced to avoid
that quotient path. -/
noncomputable def strictSubdivisionModel_collapseEdge_internal_edgePath
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy))
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target))
    (rxy : G.Walk
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch x)
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch y))
    {s t : W}
    (hst : K.Adj s t) :
    G.Walk
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch s)
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch t) :=
  if hsxy : s = x ∧ t = y then
    rxy.copy
      (by rcases hsxy with ⟨rfl, rfl⟩; rfl)
      (by rcases hsxy with ⟨rfl, rfl⟩; rfl)
  else if hsyx : s = y ∧ t = x then
    rxy.reverse.copy
      (by rcases hsyx with ⟨rfl, rfl⟩; rfl)
      (by rcases hsyx with ⟨rfl, rfl⟩; rfl)
  else
    GraphContraction.collapseEdgeWalkOutside G hab
      (hbranch s) (hbranch t) (M.edgePath hst)
      (strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
        hab M hxy hst hnone
        (by
          intro hsame
          rcases hsame with hsame | hsame
          · exact hsxy ⟨hsame.1.symm, hsame.2.symm⟩
          · exact hsyx ⟨hsame.2.symm, hsame.1.symm⟩))

theorem strictSubdivisionModel_collapseEdge_internal_edgePath_isPath
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy))
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target))
    {rxy : G.Walk
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch x)
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch y)}
    (hrxy : rxy.IsPath)
    {s t : W}
    (hst : K.Adj s t) :
    (strictSubdivisionModel_collapseEdge_internal_edgePath
      hab M hxy hnone hbranch rxy hst).IsPath := by
  classical
  unfold strictSubdivisionModel_collapseEdge_internal_edgePath
  split_ifs with hsxy hsyx
  · exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr hrxy
  · exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr hrxy.reverse
  · exact
      GraphContraction.collapseEdgeWalkOutside_isPath G hab
        (hbranch s) (hbranch t) (M.edgePath hst) _ (M.edgePath_isPath hst)

theorem strictSubdivisionModel_collapseEdge_internal_edgePath_no_internal_branch_vertices
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy))
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target))
    {rxy : G.Walk
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch x)
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch y)}
    (hrxy_support :
      forall z : V, z ∈ rxy.support ->
        z ∈ ({a, b} : Set V) ∨
          Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
            qv ∈ (M.edgePath hxy).support ∧
              Exists fun hqv_ne :
                qv ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z)
    {s t : W}
    (hst : K.Adj s t)
    {z : V}
    (hz : z ∈ Walk.InternalVertices
      (strictSubdivisionModel_collapseEdge_internal_edgePath
        hab M hxy hnone hbranch rxy hst))
    (w : W) :
    z ≠ strictSubdivisionModel_collapseEdge_internal_branchVertex
      hab M hbranch w := by
  classical
  unfold strictSubdivisionModel_collapseEdge_internal_edgePath at hz
  split_ifs at hz with hsxy hsyx
  · exact
      strictSubdivisionModel_collapseEdge_internal_replacement_no_internal_branch_vertices
        hab M hxy hbranch hrxy_support
        (by simpa [Walk.internalVertices_copy] using hz) w
  · have hz_rxy : z ∈ Walk.InternalVertices rxy := by
      have hz_rev : z ∈ Walk.InternalVertices rxy.reverse := by
        simpa [Walk.internalVertices_copy] using hz
      simpa [Walk.internalVertices_reverse] using hz_rev
    exact
      strictSubdivisionModel_collapseEdge_internal_replacement_no_internal_branch_vertices
        hab M hxy hbranch hrxy_support hz_rxy w
  · let havoid :=
      strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
        hab M hxy hst hnone
        (by
          intro hsame
          rcases hsame with hsame | hsame
          · exact hsxy ⟨hsame.1.symm, hsame.2.symm⟩
          · exact hsyx ⟨hsame.2.symm, hsame.1.symm⟩)
    exact
      strictSubdivisionModel_collapseEdge_clean_lift_no_internal_branch_vertices
        hab M hbranch hst havoid hz w

theorem strictSubdivisionModel_collapseEdge_internal_edgePaths_internally_disjoint
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy))
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target))
    {rxy : G.Walk
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch x)
      (strictSubdivisionModel_collapseEdge_internal_branchVertex
        hab M hbranch y)}
    (hrxy_support :
      forall z : V, z ∈ rxy.support ->
        z ∈ ({a, b} : Set V) ∨
          Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
            qv ∈ (M.edgePath hxy).support ∧
              Exists fun hqv_ne :
                qv ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z)
    {s t s' t' : W}
    (hst : K.Adj s t)
    (hs't' : K.Adj s' t')
    (hne : Not ((s = s' ∧ t = t') ∨ (s = t' ∧ t = s'))) :
    Disjoint
      (Walk.InternalVertices
        (strictSubdivisionModel_collapseEdge_internal_edgePath
          hab M hxy hnone hbranch rxy hst))
      (Walk.InternalVertices
        (strictSubdivisionModel_collapseEdge_internal_edgePath
          hab M hxy hnone hbranch rxy hs't')) := by
  classical
  rw [Set.disjoint_left]
  intro z hz hz'
  unfold strictSubdivisionModel_collapseEdge_internal_edgePath at hz hz'
  split_ifs at hz with hsxy hsyx
  · split_ifs at hz' with hsxy' hsyx'
    · exact hne (Or.inl
        ⟨by rw [hsxy.1, hsxy'.1], by rw [hsxy.2, hsxy'.2]⟩)
    · exact hne (Or.inr
        ⟨by rw [hsxy.1, hsyx'.2], by rw [hsxy.2, hsyx'.1]⟩)
    · have hz_rxy : z ∈ Walk.InternalVertices rxy := by
        simpa [Walk.internalVertices_copy] using hz
      let havoid' :=
        strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
          hab M hxy hs't' hnone
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy' ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx' ⟨hsame.2.symm, hsame.1.symm⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_internal_replacement_disjoint_clean_lift
          hab M hbranch hxy hs't'
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy' ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx' ⟨hsame.2.symm, hsame.1.symm⟩)
          hrxy_support havoid')
        hz_rxy hz'
  · split_ifs at hz' with hsxy' hsyx'
    · exact hne (Or.inr
        ⟨by rw [hsyx.1, hsxy'.2], by rw [hsyx.2, hsxy'.1]⟩)
    · exact hne (Or.inl
        ⟨by rw [hsyx.1, hsyx'.1], by rw [hsyx.2, hsyx'.2]⟩)
    · have hz_rxy : z ∈ Walk.InternalVertices rxy := by
        have hz_rev : z ∈ Walk.InternalVertices rxy.reverse := by
          simpa [Walk.internalVertices_copy] using hz
        simpa [Walk.internalVertices_reverse] using hz_rev
      let havoid' :=
        strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
          hab M hxy hs't' hnone
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy' ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx' ⟨hsame.2.symm, hsame.1.symm⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_internal_replacement_disjoint_clean_lift
          hab M hbranch hxy hs't'
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy' ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx' ⟨hsame.2.symm, hsame.1.symm⟩)
          hrxy_support havoid')
        hz_rxy hz'
  · split_ifs at hz' with hsxy' hsyx'
    · have hz'_rxy : z ∈ Walk.InternalVertices rxy := by
        simpa [Walk.internalVertices_copy] using hz'
      let havoid :=
        strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
          hab M hxy hst hnone
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx ⟨hsame.2.symm, hsame.1.symm⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_internal_replacement_disjoint_clean_lift
          hab M hbranch hxy hst
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx ⟨hsame.2.symm, hsame.1.symm⟩)
          hrxy_support havoid).symm
        hz hz'_rxy
    · have hz'_rxy : z ∈ Walk.InternalVertices rxy := by
        have hz'_rev : z ∈ Walk.InternalVertices rxy.reverse := by
          simpa [Walk.internalVertices_copy] using hz'
        simpa [Walk.internalVertices_reverse] using hz'_rev
      let havoid :=
        strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
          hab M hxy hst hnone
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx ⟨hsame.2.symm, hsame.1.symm⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_internal_replacement_disjoint_clean_lift
          hab M hbranch hxy hst
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx ⟨hsame.2.symm, hsame.1.symm⟩)
          hrxy_support havoid).symm
        hz hz'_rxy
    · let havoid :=
        strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
          hab M hxy hst hnone
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx ⟨hsame.2.symm, hsame.1.symm⟩)
      let havoid' :=
        strictSubdivisionModel_collapseEdge_internal_other_edgePath_avoids_collapsed
          hab M hxy hs't' hnone
          (by
            intro hsame
            rcases hsame with hsame | hsame
            · exact hsxy' ⟨hsame.1.symm, hsame.2.symm⟩
            · exact hsyx' ⟨hsame.2.symm, hsame.1.symm⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint
          hab M hbranch hst hs't' hne havoid havoid')
        hz hz'

/-- Full internal-edge uncontraction for strict subdivisions.  If the
collapsed vertex of an edge contraction occurs internally on one quotient
source-edge path, then the quotient strict subdivision lifts to a strict
subdivision in the original graph by replacing that occurrence with the
source-side bridge through the contracted edge. -/
theorem containsStrictSubdivision_of_collapseEdge_internal_edgePath
    {W : Type*} {V : Type u} [DecidableEq W] [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hnone :
      (none : (GraphContraction.collapseEdge G hab).Target) ∈
        Walk.InternalVertices (M.edgePath hxy)) :
    ContainsStrictSubdivision K G := by
  classical
  let hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target) :=
    strictSubdivisionModel_collapseEdge_internal_all_branches_avoid_collapsed
      hab M hxy hnone
  rcases
      strictSubdivisionModel_collapseEdge_internal_path_replacement_with_branch
        hab M hxy hnone hbranch with
    ⟨rxy, hrxy, hrxy_support⟩
  exact ⟨{
    toSubdivisionModel := {
      branchVertex :=
        strictSubdivisionModel_collapseEdge_internal_branchVertex
          hab M hbranch
      branchVertex_injective := by
        intro s t hst
        exact M.branchVertex_injective
          (GraphContraction.collapseEdgeUncollapse_injective G hab
            (hbranch s) (hbranch t)
            (by
              simpa [strictSubdivisionModel_collapseEdge_internal_branchVertex]
                using hst))
      edgePath := fun {s t} hst =>
        strictSubdivisionModel_collapseEdge_internal_edgePath
          hab M hxy hnone hbranch rxy hst
      edgePath_isPath := by
        intro s t hst
        exact
          strictSubdivisionModel_collapseEdge_internal_edgePath_isPath
            hab M hxy hnone hbranch hrxy hst
      no_internal_branch_vertices :=
        forall {s t : W} (hst : K.Adj s t) {z : V},
          z ∈ Walk.InternalVertices
            (strictSubdivisionModel_collapseEdge_internal_edgePath
              hab M hxy hnone hbranch rxy hst) ->
          forall w : W,
            z ≠ strictSubdivisionModel_collapseEdge_internal_branchVertex
              hab M hbranch w
      internally_disjoint_edge_paths :=
        forall {s t s' t' : W}
          (hst : K.Adj s t) (hs't' : K.Adj s' t'),
            Not ((s = s' ∧ t = t') ∨ (s = t' ∧ t = s')) ->
              Disjoint
                (Walk.InternalVertices
                  (strictSubdivisionModel_collapseEdge_internal_edgePath
                    hab M hxy hnone hbranch rxy hst))
                (Walk.InternalVertices
                  (strictSubdivisionModel_collapseEdge_internal_edgePath
                    hab M hxy hnone hbranch rxy hs't')) }
    no_internal_branch_vertices' := by
      intro s t hst z hz w hzw
      exact
        strictSubdivisionModel_collapseEdge_internal_edgePath_no_internal_branch_vertices
          hab M hxy hnone hbranch hrxy_support hst hz w hzw
    internally_disjoint_edge_paths' := by
      intro s t s' t' hst hs't' hne
      exact
        strictSubdivisionModel_collapseEdge_internal_edgePaths_internally_disjoint
          hab M hxy hnone hbranch hrxy_support hst hs't' hne }⟩
end FourColor

end Schematic.Math.GraphTheory
