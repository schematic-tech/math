import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion
import Schematic.Math.GraphTheory.Planarity.Basic

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- If a strict subdivision in a connected-subgraph contraction avoids the new
contracted vertex, it already exists in the original graph.  This is the
checked easy branch of the Makarychev/Skopenkov uncontraction step. -/
theorem containsStrictSubdivision_of_collapseSubgraph_outside
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (h :
      ContainsStrictSubdivision K
        ((GraphContraction.collapseSubgraph G H hH_connected).graph.induce
          {y : (GraphContraction.collapseSubgraph G H hH_connected).Target |
            y ≠ none})) :
    ContainsStrictSubdivision K G :=
  ContainsStrictSubdivision.map
    (GraphContraction.collapseSubgraphOutsideEmbedding G H hH_connected)
    (GraphContraction.collapseSubgraphOutsideEmbedding_injective
      G H hH_connected)
    h

/-- If the whole support of a strict subdivision in a connected-subgraph
contraction avoids the collapsed vertex, then the subdivision lifts to the
original graph. -/
theorem containsStrictSubdivision_of_collapseSubgraph_support_avoids
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hsource : forall x : W, Exists fun y : W => K.Adj x y)
    (hsupport :
      (GraphContraction.collapseSubgraph G H hH_connected).graph.support ⊆
        {y : (GraphContraction.collapseSubgraph G H hH_connected).Target |
          y ≠ none})
    (h :
      ContainsStrictSubdivision K
        (GraphContraction.collapseSubgraph G H hH_connected).graph) :
    ContainsStrictSubdivision K G :=
  containsStrictSubdivision_of_collapseSubgraph_outside
    (H := H) hH_connected
    (h.targetRestrictOfSupportSubset hsource hsupport)

theorem not_containsStrictSubdivision_K5_collapseSubgraph_of_support_avoids
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hsupport :
      (GraphContraction.collapseSubgraph G H hH_connected).graph.support ⊆
        {y : (GraphContraction.collapseSubgraph G H hH_connected).Target |
          y ≠ none}) :
    Not (ContainsStrictSubdivision K5Graph
      (GraphContraction.collapseSubgraph G H hH_connected).graph) := by
  intro hK5
  exact h_planar.no_K5_subdivision
    (containsStrictSubdivision_of_collapseSubgraph_support_avoids
      (H := H) hH_connected K5Graph_exists_adj hsupport hK5)

theorem not_containsStrictSubdivision_K33_collapseSubgraph_of_support_avoids
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hsupport :
      (GraphContraction.collapseSubgraph G H hH_connected).graph.support ⊆
        {y : (GraphContraction.collapseSubgraph G H hH_connected).Target |
          y ≠ none}) :
    Not (ContainsStrictSubdivision K33Graph
      (GraphContraction.collapseSubgraph G H hH_connected).graph) := by
  intro hK33
  exact h_planar.no_K33_subdivision
      (containsStrictSubdivision_of_collapseSubgraph_support_avoids
        (H := H) hH_connected K33Graph_exists_adj hsupport hK33)

/-- Model-specific version of the easy uncontraction branch: if a particular
strict subdivision in the quotient avoids the collapsed vertex on all branch
vertices and source-edge paths, then it lifts to the original graph. -/
theorem containsStrictSubdivision_of_collapseSubgraph_model_avoids_collapsed
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (M :
      StrictSubdivisionModel K
        (GraphContraction.collapseSubgraph G H hH_connected).graph)
    (hbranch :
      forall x : W,
        M.branchVertex x ≠
          (none :
            (GraphContraction.collapseSubgraph G H hH_connected).Target))
    (hpath :
      forall {x y : W} (hxy : K.Adj x y) {z :
          (GraphContraction.collapseSubgraph G H hH_connected).Target},
        z ∈ (M.edgePath hxy).support ->
          z ≠
            (none :
              (GraphContraction.collapseSubgraph G H hH_connected).Target)) :
    ContainsStrictSubdivision K G := by
  exact
    containsStrictSubdivision_of_collapseSubgraph_outside
      (H := H) hH_connected
      ⟨M.targetRestrict
        {y : (GraphContraction.collapseSubgraph G H hH_connected).Target |
          y ≠ none}
        (by
          intro x
          exact hbranch x)
        (by
          intro x y hxy z hz
          exact hpath hxy hz)⟩

/-- In a connected-subgraph contraction of a planar-source graph, every strict
`K_5` model in the quotient must actually use the collapsed vertex.  This is
the precise remaining branch of the Makarychev/Skopenkov uncontraction step. -/
theorem strictSubdivisionModel_K5_collapseSubgraph_uses_collapsed_of_planar
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseSubgraph G H hH_connected).graph) :
    (Exists fun x : Fin 5 =>
      M.branchVertex x =
        (none :
          (GraphContraction.collapseSubgraph G H hH_connected).Target)) ∨
      Exists fun x : Fin 5 =>
        Exists fun y : Fin 5 =>
          Exists fun hxy : K5Graph.Adj x y =>
            (none :
              (GraphContraction.collapseSubgraph G H hH_connected).Target) ∈
              (M.edgePath hxy).support := by
  classical
  by_contra havoid
  have hbranch :
      forall x : Fin 5,
        M.branchVertex x ≠
          (none :
            (GraphContraction.collapseSubgraph G H hH_connected).Target) := by
    intro x hx
    exact havoid (Or.inl ⟨x, hx⟩)
  have hpath :
      forall {x y : Fin 5} (hxy : K5Graph.Adj x y) {z :
          (GraphContraction.collapseSubgraph G H hH_connected).Target},
        z ∈ (M.edgePath hxy).support ->
          z ≠
            (none :
              (GraphContraction.collapseSubgraph G H hH_connected).Target) := by
    intro x y hxy z hz hz_none
    exact havoid
      (Or.inr ⟨x, y, hxy, by simpa [hz_none] using hz⟩)
  exact h_planar.no_K5_subdivision
    (containsStrictSubdivision_of_collapseSubgraph_model_avoids_collapsed
      (H := H) hH_connected M hbranch hpath)

/-- In a connected-subgraph contraction of a planar-source graph, every strict
`K_{3,3}` model in the quotient must actually use the collapsed vertex. -/
theorem strictSubdivisionModel_K33_collapseSubgraph_uses_collapsed_of_planar
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (M :
      StrictSubdivisionModel K33Graph
        (GraphContraction.collapseSubgraph G H hH_connected).graph) :
    (Exists fun x : K33Vertex =>
      M.branchVertex x =
        (none :
          (GraphContraction.collapseSubgraph G H hH_connected).Target)) ∨
      Exists fun x : K33Vertex =>
        Exists fun y : K33Vertex =>
          Exists fun hxy : K33Graph.Adj x y =>
            (none :
              (GraphContraction.collapseSubgraph G H hH_connected).Target) ∈
              (M.edgePath hxy).support := by
  classical
  by_contra havoid
  have hbranch :
      forall x : K33Vertex,
        M.branchVertex x ≠
          (none :
            (GraphContraction.collapseSubgraph G H hH_connected).Target) := by
    intro x hx
    exact havoid (Or.inl ⟨x, hx⟩)
  have hpath :
      forall {x y : K33Vertex} (hxy : K33Graph.Adj x y) {z :
          (GraphContraction.collapseSubgraph G H hH_connected).Target},
        z ∈ (M.edgePath hxy).support ->
          z ≠
            (none :
              (GraphContraction.collapseSubgraph G H hH_connected).Target) := by
    intro x y hxy z hz hz_none
    exact havoid
      (Or.inr ⟨x, y, hxy, by simpa [hz_none] using hz⟩)
  exact h_planar.no_K33_subdivision
    (containsStrictSubdivision_of_collapseSubgraph_model_avoids_collapsed
      (H := H) hH_connected M hbranch hpath)

/-- Edge-contraction specialization of
`strictSubdivisionModel_K5_collapseSubgraph_uses_collapsed_of_planar`. -/
theorem strictSubdivisionModel_K5_collapseEdge_uses_collapsed_of_planar
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph) :
    (Exists fun x : Fin 5 =>
      M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target)) ∨
      Exists fun x : Fin 5 =>
        Exists fun y : Fin 5 =>
          Exists fun hxy : K5Graph.Adj x y =>
            (none : (GraphContraction.collapseEdge G hab).Target) ∈
              (M.edgePath hxy).support := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected := GraphContraction.connected_top_induce_pair_of_adj
    (G := G) hab
  have huses :
      (Exists fun x : Fin 5 =>
        M.branchVertex x =
          (none :
            (GraphContraction.collapseSubgraph G H hH).Target)) ∨
        Exists fun x : Fin 5 =>
          Exists fun y : Fin 5 =>
            Exists fun hxy : K5Graph.Adj x y =>
              (none :
                (GraphContraction.collapseSubgraph G H hH).Target) ∈
                (M.edgePath hxy).support := by
    simpa [GraphContraction.collapseEdge, H, hH] using
      strictSubdivisionModel_K5_collapseSubgraph_uses_collapsed_of_planar
        h_planar H hH M
  simpa [GraphContraction.collapseEdge, H, hH] using huses

/-- Edge-contraction specialization of
`strictSubdivisionModel_K33_collapseSubgraph_uses_collapsed_of_planar`. -/
theorem strictSubdivisionModel_K33_collapseEdge_uses_collapsed_of_planar
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K33Graph
        (GraphContraction.collapseEdge G hab).graph) :
    (Exists fun x : K33Vertex =>
      M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target)) ∨
      Exists fun x : K33Vertex =>
        Exists fun y : K33Vertex =>
          Exists fun hxy : K33Graph.Adj x y =>
            (none : (GraphContraction.collapseEdge G hab).Target) ∈
              (M.edgePath hxy).support := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected := GraphContraction.connected_top_induce_pair_of_adj
    (G := G) hab
  have huses :
      (Exists fun x : K33Vertex =>
        M.branchVertex x =
          (none :
            (GraphContraction.collapseSubgraph G H hH).Target)) ∨
        Exists fun x : K33Vertex =>
          Exists fun y : K33Vertex =>
            Exists fun hxy : K33Graph.Adj x y =>
              (none :
                (GraphContraction.collapseSubgraph G H hH).Target) ∈
                (M.edgePath hxy).support := by
    simpa [GraphContraction.collapseEdge, H, hH] using
      strictSubdivisionModel_K33_collapseSubgraph_uses_collapsed_of_planar
        h_planar H hH M
  simpa [GraphContraction.collapseEdge, H, hH] using huses

/-- If the collapsed vertex is a branch vertex of a quotient strict
subdivision model, then the first step of every incident source-edge path
comes from one of the two original endpoints of the contracted edge. -/
theorem strictSubdivisionModel_collapseEdge_branch_incident_first_step_side
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hx :
      M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        (M.edgePath hxy).snd =
            GraphContraction.collapseEdgeOutside G hab v hv ∧
          (G.Adj a v ∨ G.Adj b v) := by
  classical
  have hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro hy
    have hxy_eq : x = y := M.branchVertex_injective (hx.trans hy.symm)
    exact hxy.ne hxy_eq
  let p' := (M.edgePath hxy).copy hx rfl
  obtain ⟨v, hv, hsnd, hside⟩ :=
    GraphContraction.collapseEdge_walk_first_step_side G hab p' hy
  exact ⟨v, hv, by simpa [p'] using hsnd, hside⟩

/-- For an edge path incident with a collapsed branch vertex, remove the
collapsed first vertex and lift the remaining clean quotient tail back to the
source graph.  This is the path-level object used in the branch-expansion
cases of the Makarychev/Skopenkov uncontraction step. -/
theorem strictSubdivisionModel_collapseEdge_branch_incident_tail_lift
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hx :
      M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun hy :
        M.branchVertex y ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
      Exists fun v : V =>
        v ∉ ({a, b} : Set V) ∧
          Exists fun q : G.Walk v
            (GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy) =>
            (G.Adj a v ∨ G.Adj b v) ∧ q.IsPath ∧
              (forall t : V, t ∈ q.support -> t ∉ ({a, b} : Set V)) ∧
              (forall t : V, t ∈ q.support ->
                Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
                  qv ∈ (M.edgePath hxy).support ∧
                    Exists fun hqv_ne :
                      qv ≠
                        (none : (GraphContraction.collapseEdge G hab).Target) =>
                      GraphContraction.collapseEdgeUncollapse
                        G hab qv hqv_ne = t) := by
  classical
  have hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro hy
    have hxy_eq : x = y := M.branchVertex_injective (hx.trans hy.symm)
    exact hxy.ne hxy_eq
  let p : (GraphContraction.collapseEdge G hab).graph.Walk
      (M.branchVertex x) (M.branchVertex y) := M.edgePath hxy
  let p' : (GraphContraction.collapseEdge G hab).graph.Walk
      (none : (GraphContraction.collapseEdge G hab).Target)
      (M.branchVertex y) := p.copy hx rfl
  have hp' : p'.IsPath := by
    simpa [p', p] using (M.edgePath_isPath hxy)
  obtain ⟨v, hv, hsnd, hside⟩ :=
    GraphContraction.collapseEdge_walk_first_step_side G hab p' hy
  have hsnd_ne :
      p'.snd ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    rw [hsnd]
    simp [GraphContraction.collapseEdgeOutside]
  have hp'_not_nil : ¬ p'.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p') hy.symm
  have hpavoid : forall t, t ∈ p'.tail.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro t ht ht_none
    have hnone_tail :
        (none : (GraphContraction.collapseEdge G hab).Target) ∈
          p'.tail.support := by
      simpa [ht_none] using ht
    have hnone_tail_list :
        (none : (GraphContraction.collapseEdge G hab).Target) ∈
          p'.support.tail := by
      rwa [← p'.support_tail_of_not_nil hp'_not_nil]
    exact Walk.IsPath.start_notMem_tail_support hp' hnone_tail_list
  let q0 :=
    GraphContraction.collapseEdgeWalkOutside G hab hsnd_ne hy p'.tail hpavoid
  have hq0 : q0.IsPath :=
    GraphContraction.collapseEdgeWalkOutside_isPath G hab hsnd_ne hy
      p'.tail hpavoid hp'.tail
  have hstart :
      GraphContraction.collapseEdgeUncollapse G hab p'.snd hsnd_ne = v := by
    calc
      GraphContraction.collapseEdgeUncollapse G hab p'.snd hsnd_ne =
          GraphContraction.collapseEdgeUncollapse G hab
            (GraphContraction.collapseEdgeOutside G hab v hv)
            (by simp [GraphContraction.collapseEdgeOutside]) :=
        GraphContraction.collapseEdgeUncollapse_congr G hab hsnd_ne
          (by simp [GraphContraction.collapseEdgeOutside]) hsnd
      _ = v :=
        GraphContraction.collapseEdgeUncollapse_outside G hab hv
          (by simp [GraphContraction.collapseEdgeOutside])
  let q : G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy) :=
    q0.copy hstart rfl
  have hq : q.IsPath := by
    simpa [q] using (SimpleGraph.Walk.isPath_copy q0 hstart rfl).mpr hq0
  have hq_outside :
      forall t : V, t ∈ q.support -> t ∉ ({a, b} : Set V) := by
    intro t ht
    exact
      GraphContraction.collapseEdgeWalkOutside_support_outside G hab hsnd_ne
        hy p'.tail hpavoid
        (by simpa [q, SimpleGraph.Walk.support_copy] using ht)
  have hq_reflect :
      forall t : V, t ∈ q.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hxy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t := by
    intro t ht
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab hsnd_ne hy p'.tail hpavoid
          (by simpa [q, SimpleGraph.Walk.support_copy] using ht) with
      ⟨qv, hqv_tail, hqv_ne, hqv_eq⟩
    have hqv_tail_list : qv ∈ p'.support.tail := by
      rwa [← p'.support_tail_of_not_nil hp'_not_nil]
    have hqv_p' : qv ∈ p'.support := List.mem_of_mem_tail hqv_tail_list
    have hqv_p : qv ∈ p.support := by
      simpa [p'] using hqv_p'
    exact ⟨qv, by simpa [p] using hqv_p, hqv_ne, hqv_eq⟩
  exact ⟨hy, v, hv, q, hside, hq, hq_outside, hq_reflect⟩

/-- Expand an incident arm of a quotient model whose branch vertex is the
collapsed vertex, choosing `a` as the expanded source branch endpoint. -/
theorem strictSubdivisionModel_collapseEdge_branch_incident_expanded_path_from_a
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hx :
      M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun hy :
        M.branchVertex y ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
      Exists fun r : G.Walk a
        (GraphContraction.collapseEdgeUncollapse G hab (M.branchVertex y) hy) =>
        r.IsPath := by
  classical
  obtain ⟨hy, v, _hv, q, hside, hq, hq_out, _hq_reflect⟩ :=
    strictSubdivisionModel_collapseEdge_branch_incident_tail_lift hab M hxy hx
  have ha_not : a ∉ q.support := by
    intro ha
    exact hq_out a ha (by simp)
  have hb_not : b ∉ q.support := by
    intro hb
    exact hq_out b hb (by simp)
  let r : G.Walk a
      (GraphContraction.collapseEdgeUncollapse G hab (M.branchVertex y) hy) :=
    Walk.branchAttachmentPath hab hside q
  have hr : r.IsPath := by
    simpa [r] using Walk.branchAttachmentPath_isPath hab hside hq ha_not hb_not
  exact ⟨hy, r, hr⟩

/-- Expand an incident arm of a quotient model whose branch vertex is the
collapsed vertex, choosing `b` as the expanded source branch endpoint. -/
theorem strictSubdivisionModel_collapseEdge_branch_incident_expanded_path_from_b
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hx :
      M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun hy :
        M.branchVertex y ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
      Exists fun r : G.Walk b
        (GraphContraction.collapseEdgeUncollapse G hab (M.branchVertex y) hy) =>
        r.IsPath := by
  classical
  obtain ⟨hy, v, _hv, q, hside, hq, hq_out, _hq_reflect⟩ :=
    strictSubdivisionModel_collapseEdge_branch_incident_tail_lift hab M hxy hx
  have hb_not : b ∉ q.support := by
    intro hb
    exact hq_out b hb (by simp)
  have ha_not : a ∉ q.support := by
    intro ha
    exact hq_out a ha (by simp)
  have hside' : G.Adj b v ∨ G.Adj a v := hside.symm
  let r : G.Walk b
      (GraphContraction.collapseEdgeUncollapse G hab (M.branchVertex y) hy) :=
    Walk.branchAttachmentPath hab.symm hside' q
  have hr : r.IsPath := by
    simpa [r] using
      Walk.branchAttachmentPath_isPath hab.symm hside' hq hb_not ha_not
  exact ⟨hy, r, hr⟩

theorem strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y z : W}
    (hcy : K.Adj c y)
    (hcz : K.Adj c z)
    (hyz : y ≠ z)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    {uy vy uz vz : V}
    {qy : G.Walk uy vy}
    {qz : G.Walk uz vz}
    (hqy_reflect :
      forall t : V, t ∈ qy.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t)
    (hqz_reflect :
      forall t : V, t ∈ qz.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcz).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t) :
    Disjoint {t : V | t ∈ qy.support} {t : V | t ∈ qz.support} := by
  classical
  rw [Set.disjoint_left]
  intro t hty htz
  rcases hqy_reflect t hty with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
  rcases hqz_reflect t htz with ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
  have hqv_rv : qv = rv :=
    GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
      (hqv_eq.trans hrv_eq.symm)
  have hne :
      Not ((c = c ∧ y = z) ∨ (c = z ∧ y = c)) := by
    intro hsame
    rcases hsame with hsame | hsame
    · exact hyz hsame.2
    · exact hcz.ne hsame.1
  rcases
      M.edgePath_support_inter_subset_common_branch_vertices hcy hcz hne
        hqv_mem (by simpa [hqv_rv] using hrv_mem) with
    ⟨w, hwcy, hwcz, hqv_branch⟩
  rcases hwcy with rfl | rfl
  · exact hqv_ne (by simpa [hc] using hqv_branch)
  · rcases hwcz with hwc | hwz
    · exact hcy.ne hwc.symm
    · exact hyz hwz

theorem strictSubdivisionModel_collapseEdge_branch_incident_two_tail_lifts
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y z : W}
    (hcy : K.Adj c y)
    (hcz : K.Adj c z)
    (hyz : y ≠ z)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun hy :
        M.branchVertex y ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
      Exists fun hz :
        M.branchVertex z ≠
          (none : (GraphContraction.collapseEdge G hab).Target) =>
        Exists fun vy : V =>
          vy ∉ ({a, b} : Set V) ∧
            Exists fun qy : G.Walk vy
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) hy) =>
              Exists fun vz : V =>
                vz ∉ ({a, b} : Set V) ∧
                  Exists fun qz : G.Walk vz
                    (GraphContraction.collapseEdgeUncollapse G hab
                      (M.branchVertex z) hz) =>
                    (G.Adj a vy ∨ G.Adj b vy) ∧ qy.IsPath ∧
                    (forall t : V, t ∈ qy.support ->
                      t ∉ ({a, b} : Set V)) ∧
                    (forall t : V, t ∈ qy.support ->
                      Exists fun qv :
                          (GraphContraction.collapseEdge G hab).Target =>
                        qv ∈ (M.edgePath hcy).support ∧
                          Exists fun hqv_ne :
                            qv ≠
                              (none :
                                (GraphContraction.collapseEdge G hab).Target) =>
                            GraphContraction.collapseEdgeUncollapse
                              G hab qv hqv_ne = t) ∧
                    (G.Adj a vz ∨ G.Adj b vz) ∧ qz.IsPath ∧
                    (forall t : V, t ∈ qz.support ->
                      t ∉ ({a, b} : Set V)) ∧
                    (forall t : V, t ∈ qz.support ->
                      Exists fun qv :
                          (GraphContraction.collapseEdge G hab).Target =>
                        qv ∈ (M.edgePath hcz).support ∧
                          Exists fun hqv_ne :
                            qv ≠
                              (none :
                                (GraphContraction.collapseEdge G hab).Target) =>
                            GraphContraction.collapseEdgeUncollapse
                              G hab qv hqv_ne = t) ∧
                    Disjoint
                      {t : V | t ∈ qy.support}
                      {t : V | t ∈ qz.support} := by
  classical
  obtain ⟨hy, vy, hvy, qy, hsidey, hqy, hqy_out, hqy_reflect⟩ :=
    strictSubdivisionModel_collapseEdge_branch_incident_tail_lift
      hab M hcy hc
  obtain ⟨hz, vz, hvz, qz, hsidez, hqz, hqz_out, hqz_reflect⟩ :=
    strictSubdivisionModel_collapseEdge_branch_incident_tail_lift
      hab M hcz hc
  have hdisj :
      Disjoint {t : V | t ∈ qy.support} {t : V | t ∈ qz.support} :=
    strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
      hab M hcy hcz hyz hc hqy_reflect hqz_reflect
  exact ⟨hy, hz, vy, hvy, qy, vz, hvz, qz, hsidey, hqy, hqy_out,
    hqy_reflect, hsidez, hqz, hqz_out, hqz_reflect, hdisj⟩


end FourColor

end Schematic.Math.GraphTheory
