import Schematic.Math.GraphTheory.Subdivisions.DegreeBounds

/-! Source-edge combinatorics and rerouting subdivision models in the host graph. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

/-- Two distinct unordered two-ended source edges have at most one common
endpoint.

The hypotheses are deliberately graph-agnostic: adjacency is only used by
callers to supply the endpoint inequalities. This is the finite source-edge
uniqueness fact needed after the mixed `K_5`/`K_{3,3}` case split has selected
a common endpoint but the strict-subdivision support argument requires a
proof that it is the only one. -/
theorem two_pair_unique_common_endpoint_of_not_same
    {α : Type*} {a b c d v : α}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : v = a ∨ v = b)
    (hvcd : v = c ∨ v = d)
    (hne : Not ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    forall w : α,
      (w = a ∨ w = b) ->
        (w = c ∨ w = d) ->
          w = v := by
  intro w hwab hwcd
  rcases hvab with hvab | hvab <;>
    rcases hvcd with hvcd | hvcd <;>
    rcases hwab with hwab | hwab <;>
    rcases hwcd with hwcd | hwcd
  all_goals aesop (add simp [eq_comm])

/-- Two two-ended source edges with a chosen common endpoint are either the
same unordered edge, or that chosen endpoint is the unique common endpoint.

This packages the duplicate-source-edge branch separately from the genuine
single-common-endpoint branch used by strict-subdivision support
localization. -/
theorem two_pair_same_or_unique_common_endpoint
    {α : Type*} {a b c d v : α}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : v = a ∨ v = b)
    (hvcd : v = c ∨ v = d) :
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∨
      (Not ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
        forall w : α,
          (w = a ∨ w = b) ->
            (w = c ∨ w = d) ->
              w = v) := by
  by_cases hsame : (a = c ∧ b = d) ∨ (a = d ∧ b = c)
  · exact Or.inl hsame
  · exact Or.inr
      ⟨hsame,
        two_pair_unique_common_endpoint_of_not_same
          hab hcd hvab hvcd hsame⟩

/-- Distinct source edges of a strict subdivision cannot share a host edge.
The existing model axioms state vertex-disjointness only for interiors; the
stronger edge statement follows because two distinct simple source edges have
at most one common endpoint. -/
theorem StrictSubdivisionModel.edgePath_edges_disjoint_of_distinct
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y x' y' : W}
    (hxy : H.Adj x y)
    (hx'y' : H.Adj x' y')
    (hne :
      Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))) :
    forall e : Sym2 V,
      e ∈ (M.edgePath hxy).edges ->
        e ∈ (M.edgePath hx'y').edges -> False := by
  intro e
  refine Sym2.ind ?_ e
  intro a b hab hab'
  have ha_p : a ∈ (M.edgePath hxy).support :=
    (M.edgePath hxy).fst_mem_support_of_mem_edges hab
  have ha_q : a ∈ (M.edgePath hx'y').support :=
    (M.edgePath hx'y').fst_mem_support_of_mem_edges hab'
  have hb_p : b ∈ (M.edgePath hxy).support :=
    (M.edgePath hxy).snd_mem_support_of_mem_edges hab
  have hb_q : b ∈ (M.edgePath hx'y').support :=
    (M.edgePath hx'y').snd_mem_support_of_mem_edges hab'
  rcases
      M.edgePath_support_inter_subset_common_branch_vertices
        hxy hx'y' hne ha_p ha_q with
    ⟨c, hcxy, hcx'y', hac⟩
  have hunique :
      forall w : W,
        (w = x ∨ w = y) -> (w = x' ∨ w = y') -> w = c :=
    two_pair_unique_common_endpoint_of_not_same
      hxy.ne hx'y'.ne hcxy hcx'y' hne
  have hbc : b = M.branchVertex c :=
    M.edgePath_support_inter_eq_common_branchVertex
      hxy hx'y' hne hunique hb_p hb_q
  have hab_eq : a = b := hac.trans hbc.symm
  have hab_adj : G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet]
    exact (M.edgePath hxy).edges_subset_edgeSet hab
  exact hab_adj.ne hab_eq

/-- Regard a strict subdivision model as living in a larger graph on the same
vertex type, without changing any path support or edge list. -/
def StrictSubdivisionModel.targetMono
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G G' : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (hGG' : G ≤ G') :
    StrictSubdivisionModel H G' where
  toSubdivisionModel.branchVertex := M.branchVertex
  toSubdivisionModel.branchVertex_injective := M.branchVertex_injective
  toSubdivisionModel.edgePath hab :=
    (M.edgePath hab).transfer G' (fun e he => by
      exact SimpleGraph.edgeSet_mono hGG'
        ((M.edgePath hab).edges_subset_edgeSet he))
  toSubdivisionModel.edgePath_isPath hab :=
    (M.edgePath_isPath hab).transfer _
  toSubdivisionModel.no_internal_branch_vertices :=
    M.no_internal_branch_vertices
  toSubdivisionModel.internally_disjoint_edge_paths :=
    M.internally_disjoint_edge_paths
  no_internal_branch_vertices' := by
    intro a b hab z hz w hzw
    have hzold : z ∈ Walk.InternalVertices (M.edgePath hab) := by
      simpa [Walk.internalVertices_transfer] using hz
    exact M.no_internal_branch_vertices' hab hzold w hzw
  internally_disjoint_edge_paths' := by
    intro a b a' b' hab ha'b' hdistinct
    rw [Set.disjoint_left]
    intro z hz hz'
    have hzold : z ∈ Walk.InternalVertices (M.edgePath hab) := by
      simpa [Walk.internalVertices_transfer] using hz
    have hzold' : z ∈ Walk.InternalVertices (M.edgePath ha'b') := by
      simpa [Walk.internalVertices_transfer] using hz'
    exact Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hab ha'b' hdistinct)
      hzold hzold'

/-- Reroute a host edge of every model path along a clean alternate path.
All old model vertices lie in `A`, while the alternate path meets `A` only at
its endpoints.  Thus the reroute preserves the strict topological-model
axioms even when both orientations of the same source edge are represented by
different walks. -/
def StrictSubdivisionModel.rerouteHostEdgeOutside
    {W : Type u} {V : Type v}
    [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (A : Set V)
    (x y : V)
    (q : G.Walk x y)
    (hq : q.IsPath)
    (hbranch : forall w : W, M.branchVertex w ∈ A)
    (hpath :
      forall {a b : W} (hab : H.Adj a b) {z : V},
        z ∈ (M.edgePath hab).support -> z ∈ A)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ A -> z = x ∨ z = y) :
    StrictSubdivisionModel H G where
  toSubdivisionModel.branchVertex := M.branchVertex
  toSubdivisionModel.branchVertex_injective := M.branchVertex_injective
  toSubdivisionModel.edgePath hab :=
    Walk.IsPath.expandEdge (M.edgePath_isPath hab) x y q
  toSubdivisionModel.edgePath_isPath hab := by
    exact Walk.IsPath.expandEdge_isPath (M.edgePath_isPath hab) hq
      (by
        intro z hzq hzp
        exact hq_clean z hzq (hpath hab hzp))
  toSubdivisionModel.no_internal_branch_vertices :=
    M.no_internal_branch_vertices
  toSubdivisionModel.internally_disjoint_edge_paths :=
    M.internally_disjoint_edge_paths
  no_internal_branch_vertices' := by
    intro a b hab z hz w hzw
    rcases
        Walk.IsPath.expandEdge_internalVertices_subset_with_marker
          (M.edgePath_isPath hab) q z hz with hzold | hznew
    · exact M.no_internal_branch_vertices' hab hzold w hzw
    · have hzA : z ∈ A := by simpa [hzw] using hbranch w
      rcases hq_clean z hznew.2.1 hzA with hzx | hzy
      · exact hznew.2.2.1 hzx
      · exact hznew.2.2.2 hzy
  internally_disjoint_edge_paths' := by
    intro a b a' b' hab ha'b' hdistinct
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases
        Walk.IsPath.expandEdge_internalVertices_subset_with_marker
          (M.edgePath_isPath hab) q z hz with hzold | hznew
    · rcases
          Walk.IsPath.expandEdge_internalVertices_subset_with_marker
            (M.edgePath_isPath ha'b') q z hz' with hzold' | hznew'
      · exact
          Set.disjoint_left.mp
            (M.internally_disjoint_edge_paths' hab ha'b' hdistinct)
            hzold hzold'
      · have hzA : z ∈ A := hpath hab hzold.1
        rcases hq_clean z hznew'.2.1 hzA with hzx | hzy
        · exact hznew'.2.2.1 hzx
        · exact hznew'.2.2.2 hzy
    · rcases
          Walk.IsPath.expandEdge_internalVertices_subset_with_marker
            (M.edgePath_isPath ha'b') q z hz' with hzold' | hznew'
      · have hzA : z ∈ A := hpath ha'b' hzold'.1
        rcases hq_clean z hznew.2.1 hzA with hzx | hzy
        · exact hznew.2.2.1 hzx
        · exact hznew.2.2.2 hzy
      · exact M.edgePath_edges_disjoint_of_distinct hab ha'b' hdistinct
          s(x, y) hznew.1 hznew'.1

/-- If two distinct unordered two-ended source edges share endpoint `v`, then
their endpoints opposite `v` are distinct. -/
theorem two_pair_other_endpoints_ne_of_not_same
    {α : Type*} {a b c d v r s : α}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : v = a ∨ v = b)
    (hvcd : v = c ∨ v = d)
    (hrv : r ≠ v)
    (hrab : r = a ∨ r = b)
    (hsv : s ≠ v)
    (hscd : s = c ∨ s = d)
    (hne : Not ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    r ≠ s := by
  intro hrs
  apply hne
  rcases hvab with hvab | hvab <;>
    rcases hvcd with hvcd | hvcd <;>
    rcases hrab with hrab | hrab <;>
    rcases hscd with hscd | hscd
  all_goals aesop (add simp [eq_comm])

/-- If two unordered two-ended source edges are the same and share endpoint
`v`, then their endpoints opposite `v` are the same.

This is the duplicate-source-edge complement to
`two_pair_other_endpoints_ne_of_not_same`.  The mixed Kuratowski proof uses the
two lemmas together: if the recorded opposite endpoints are distinct, the two
source edges cannot be the same unordered edge. -/
theorem two_pair_other_endpoints_eq_of_same
    {α : Type*} {a b c d v r s : α}
    (hvab : v = a ∨ v = b)
    (hvcd : v = c ∨ v = d)
    (hrv : r ≠ v)
    (hrab : r = a ∨ r = b)
    (hsv : s ≠ v)
    (hscd : s = c ∨ s = d)
    (hsame : (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    r = s := by
  rcases hvab with hvab | hvab <;>
    rcases hvcd with hvcd | hvcd <;>
    rcases hrab with hrab | hrab <;>
    rcases hscd with hscd | hscd <;>
    rcases hsame with hsame | hsame
  all_goals aesop (add simp [eq_comm])

/-- Pure endpoint combinatorics for three pairwise-intersecting two-ended
source edges.

Either the three pairs have a common endpoint, or all six endpoints are
covered by three vertices.  This is the source-level alternative behind the
`K_5` mixed-edge branch: the second case is the abstract triangle pattern,
without choosing an orientation for the three edges. -/
theorem three_pair_edges_common_endpoint_or_three_cover
    {α : Type*} {a b c d e f : α}
    (h12 : a = c ∨ a = d ∨ b = c ∨ b = d)
    (h13 : a = e ∨ a = f ∨ b = e ∨ b = f)
    (h23 : c = e ∨ c = f ∨ d = e ∨ d = f) :
    (Exists fun v : α =>
      (v = a ∨ v = b) ∧ (v = c ∨ v = d) ∧ (v = e ∨ v = f)) ∨
      Exists fun x : α =>
        Exists fun y : α =>
          Exists fun z : α =>
            (a = x ∨ a = y ∨ a = z) ∧
            (b = x ∨ b = y ∨ b = z) ∧
            (c = x ∨ c = y ∨ c = z) ∧
            (d = x ∨ d = y ∨ d = z) ∧
            (e = x ∨ e = y ∨ e = z) ∧
            (f = x ∨ f = y ∨ f = z) := by
  rcases h12 with h12 | h12 | h12 | h12 <;>
    rcases h13 with h13 | h13 | h13 | h13 <;>
    rcases h23 with h23 | h23 | h23 | h23
  all_goals
    solve
    | left
      aesop (add simp [eq_comm])
    | right
      refine ⟨a, b, c, ?_⟩
      aesop (add simp [eq_comm])
    | right
      refine ⟨a, b, d, ?_⟩
      aesop (add simp [eq_comm])

/-- Three pairwise-intersecting source edges in `K_{3,3}` have a common
endpoint.

This is the finite bipartite source-graph fact used by mixed Kuratowski
localization: unlike `K_5`, the alternative "the three pairwise intersections
form a triangle" is impossible in `K_{3,3}`. -/
theorem K33Graph.common_endpoint_of_pairwise_share
    {a b c d e f : K33Vertex}
    (hab : K33Graph.Adj a b)
    (hcd : K33Graph.Adj c d)
    (hef : K33Graph.Adj e f)
    (h12 : a = c ∨ a = d ∨ b = c ∨ b = d)
    (h13 : a = e ∨ a = f ∨ b = e ∨ b = f)
    (h23 : c = e ∨ c = f ∨ d = e ∨ d = f) :
    Exists fun v : K33Vertex =>
      (v = a ∨ v = b) ∧ (v = c ∨ v = d) ∧ (v = e ∨ v = f) := by
  rcases a with a | a <;>
    rcases b with b | b <;>
    simp [K33Graph] at hab
  all_goals
    rcases c with c | c <;>
      rcases d with d | d <;>
      simp [K33Graph] at hcd
  all_goals
    rcases e with e | e <;>
      rcases f with f | f <;>
      simp [K33Graph] at hef
  all_goals
    simp at h12 h13 h23 ⊢
  all_goals aesop

/-- In `K_{3,3}`, three distinct neighbours of one vertex are all of its
neighbours.

This is the finite source-graph fact used in the GM IX `(2.4)` mixed
Kuratowski branch after the common-branch arm package has extracted three
distinct opposite source endpoints. -/
theorem K33Graph.neighbor_eq_of_three_distinct_adj
    {c a b d z : K33Vertex}
    (ha : K33Graph.Adj c a)
    (hb : K33Graph.Adj c b)
    (hd : K33Graph.Adj c d)
    (hab : a ≠ b)
    (had : a ≠ d)
    (hbd : b ≠ d)
    (hz : K33Graph.Adj c z) :
    z = a ∨ z = b ∨ z = d := by
  rcases c with c | c <;>
    rcases a with a | a <;>
    rcases b with b | b <;>
    rcases d with d | d <;>
    rcases z with z | z <;>
    simp [K33Graph] at ha hb hd hz ⊢
  all_goals
    fin_cases a <;> fin_cases b <;> fin_cases d <;>
      fin_cases z <;> simp_all

theorem fin3_exists_two_ne (i : Fin 3) :
    Exists fun j : Fin 3 =>
      Exists fun k : Fin 3 => j ≠ k ∧ j ≠ i ∧ k ≠ i := by
  fin_cases i <;> decide

/-- If three vertices are neighbors of a vertex of `K_{3,3}`, then there are
two further vertices on the same side as the center, both adjacent to all three
neighbors.  This is the finite source-graph fact behind the `K_{3,3}`
common-branch tripod construction. -/
theorem K33Graph.exists_two_same_side_common_neighbors
    {c a b d : K33Vertex}
    (ha : K33Graph.Adj c a)
    (hb : K33Graph.Adj c b)
    (hd : K33Graph.Adj c d) :
    Exists fun x : K33Vertex =>
      Exists fun y : K33Vertex =>
        x ≠ y ∧ x ≠ c ∧ y ≠ c ∧
          K33Graph.Adj x a ∧ K33Graph.Adj x b ∧ K33Graph.Adj x d ∧
            K33Graph.Adj y a ∧ K33Graph.Adj y b ∧ K33Graph.Adj y d := by
  rcases c with ci | ci
  · obtain ⟨j, k, hjk, hji, hki⟩ := fin3_exists_two_ne ci
    have hx_adj :
        forall z : K33Vertex, K33Graph.Adj (Sum.inl ci) z ->
          K33Graph.Adj (Sum.inl j) z := by
      intro z hz
      rcases z with zi | zi <;> simp [K33Graph] at hz ⊢
    have hy_adj :
        forall z : K33Vertex, K33Graph.Adj (Sum.inl ci) z ->
          K33Graph.Adj (Sum.inl k) z := by
      intro z hz
      rcases z with zi | zi <;> simp [K33Graph] at hz ⊢
    refine ⟨Sum.inl j, Sum.inl k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hjk (Sum.inl.inj h)
    · intro h
      exact hji (Sum.inl.inj h)
    · intro h
      exact hki (Sum.inl.inj h)
    · exact hx_adj a ha
    · exact hx_adj b hb
    · exact hx_adj d hd
    · exact hy_adj a ha
    · exact hy_adj b hb
    · exact hy_adj d hd
  · obtain ⟨j, k, hjk, hji, hki⟩ := fin3_exists_two_ne ci
    have hx_adj :
        forall z : K33Vertex, K33Graph.Adj (Sum.inr ci) z ->
          K33Graph.Adj (Sum.inr j) z := by
      intro z hz
      rcases z with zi | zi <;> simp [K33Graph] at hz ⊢
    have hy_adj :
        forall z : K33Vertex, K33Graph.Adj (Sum.inr ci) z ->
          K33Graph.Adj (Sum.inr k) z := by
      intro z hz
      rcases z with zi | zi <;> simp [K33Graph] at hz ⊢
    refine ⟨Sum.inr j, Sum.inr k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hjk (Sum.inr.inj h)
    · intro h
      exact hji (Sum.inr.inj h)
    · intro h
      exact hki (Sum.inr.inj h)
    · exact hx_adj a ha
    · exact hx_adj b hb
    · exact hx_adj d hd
    · exact hy_adj a ha
    · exact hy_adj b hb
    · exact hy_adj d hd

theorem StrictSubdivisionModel.K5_branchVertex_mem_support
    {V : Type v}
    {G : SimpleGraph V}
    (M : StrictSubdivisionModel K5Graph G)
    (x : Fin 5) :
    M.branchVertex x ∈ G.support := by
  have hdegree : 0 < K5Graph.degree x := by
    rw [K5Graph_degree x]
    omega
  exact M.branchVertex_mem_support_of_degree_pos hdegree

theorem StrictSubdivisionModel.K33_branchVertex_mem_support
    {V : Type v}
    {G : SimpleGraph V}
    (M : StrictSubdivisionModel K33Graph G)
    (x : K33Vertex) :
    M.branchVertex x ∈ G.support := by
  classical
  letI : DecidableRel K33Graph.Adj := Classical.decRel _
  have hdegree : 0 < K33Graph.degree x := by
    rw [K33Graph_degree x]
    omega
  exact M.branchVertex_mem_support_of_degree_pos hdegree

/-- All five branch vertices of a strict `K_5` subdivision lie in one
connected component of the host. -/
theorem StrictSubdivisionModel.K5_exists_connectedComponent_ncard_ge_five
    {V : Type v}
    [Fintype V]
    {G : SimpleGraph V}
    (M : StrictSubdivisionModel K5Graph G) :
    Exists fun C : G.ConnectedComponent => 5 <= C.supp.ncard := by
  classical
  let C : G.ConnectedComponent := G.connectedComponentMk (M.branchVertex 0)
  have hbranch_mem : forall i : Fin 5, M.branchVertex i ∈ C.supp := by
    intro i
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    by_cases hi : i = 0
    · subst i
      rfl
    · have h0i : K5Graph.Adj (0 : Fin 5) i :=
        K5Graph.adj_of_ne (fun h => hi h.symm)
      exact (SimpleGraph.ConnectedComponent.sound (M.edgePath h0i).reachable).symm
  letI : Fintype C.supp := C.supp.toFinite.fintype
  let e : Fin 5 ↪ C.supp := {
    toFun := fun i => ⟨M.branchVertex i, hbranch_mem i⟩
    inj' := by
      intro i j hij
      exact M.branchVertex_injective (Subtype.ext_iff.mp hij)
  }
  have hcard : Fintype.card (Fin 5) <= Fintype.card C.supp :=
    Fintype.card_le_of_injective e e.injective
  refine ⟨C, ?_⟩
  simpa [Fintype.card_fin, Set.fintypeCard_eq_ncard] using hcard

/-- All six branch vertices of a strict `K_{3,3}` subdivision lie in one
connected component of the host. -/
theorem StrictSubdivisionModel.K33_exists_connectedComponent_ncard_ge_six
    {V : Type v}
    [Fintype V]
    {G : SimpleGraph V}
    (M : StrictSubdivisionModel K33Graph G) :
    Exists fun C : G.ConnectedComponent => 6 <= C.supp.ncard := by
  classical
  let C : G.ConnectedComponent := G.connectedComponentMk (M.branchVertex (Sum.inl 0))
  have hbranch_mem : forall x : K33Vertex, M.branchVertex x ∈ C.supp := by
    intro x
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    cases x with
    | inl i =>
        by_cases hi : i = 0
        · subst i
          rfl
        · have h0r : K33Graph.Adj (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) := by
            simp [K33Graph]
          have hri : K33Graph.Adj (Sum.inr (0 : Fin 3)) (Sum.inl i) := by
            simp [K33Graph]
          have hreach :
              G.Reachable (M.branchVertex (Sum.inl (0 : Fin 3)))
                (M.branchVertex (Sum.inl i)) :=
            (M.edgePath h0r).reachable.trans (M.edgePath hri).reachable
          exact (SimpleGraph.ConnectedComponent.sound hreach).symm
    | inr i =>
        have h0i : K33Graph.Adj (Sum.inl (0 : Fin 3)) (Sum.inr i) := by
          simp [K33Graph]
        exact (SimpleGraph.ConnectedComponent.sound (M.edgePath h0i).reachable).symm
  letI : Fintype C.supp := C.supp.toFinite.fintype
  let e : K33Vertex ↪ C.supp := {
    toFun := fun x => ⟨M.branchVertex x, hbranch_mem x⟩
    inj' := by
      intro x y hxy
      exact M.branchVertex_injective (Subtype.ext_iff.mp hxy)
  }
  have hcard : Fintype.card K33Vertex <= Fintype.card C.supp :=
    Fintype.card_le_of_injective e e.injective
  refine ⟨C, ?_⟩
  simpa [card_K33Vertex, Set.fintypeCard_eq_ncard] using hcard

/-- A strict `K_5` subdivision forces a connected component with at least
five vertices. -/
theorem exists_connectedComponent_ncard_ge_five_of_containsStrictSubdivision_K5
    {V : Type v}
    [Fintype V]
    {G : SimpleGraph V}
    (hK5 : ContainsStrictSubdivision K5Graph G) :
    Exists fun C : G.ConnectedComponent => 5 <= C.supp.ncard := by
  rcases hK5 with ⟨M⟩
  exact M.K5_exists_connectedComponent_ncard_ge_five

/-- A strict `K_{3,3}` subdivision forces a connected component with at least
six vertices. -/
theorem exists_connectedComponent_ncard_ge_six_of_containsStrictSubdivision_K33
    {V : Type v}
    [Fintype V]
    {G : SimpleGraph V}
    (hK33 : ContainsStrictSubdivision K33Graph G) :
    Exists fun C : G.ConnectedComponent => 6 <= C.supp.ncard := by
  rcases hK33 with ⟨M⟩
  exact M.K33_exists_connectedComponent_ncard_ge_six

theorem highDegree_four_ncard_ge_five_of_containsStrictSubdivision_K5
    {V : Type v}
    {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (h : ContainsStrictSubdivision K5Graph G) :
    5 <= {v : V | 4 <= G.degree v}.ncard := by
  classical
  simpa [Fintype.card_fin] using
    highDegree_ncard_ge_of_containsStrictSubdivision
      (H := K5Graph) (G := G) (d := 4)
      (fun x => by rw [K5Graph_degree x]) h

theorem highDegree_three_ncard_ge_six_of_containsStrictSubdivision_K33
    {V : Type v}
    {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (h : ContainsStrictSubdivision K33Graph G) :
    6 <= {v : V | 3 <= G.degree v}.ncard := by
  classical
  letI : DecidableRel K33Graph.Adj := Classical.decRel _
  simpa [card_K33Vertex] using
    highDegree_ncard_ge_of_containsStrictSubdivision
      (H := K33Graph) (G := G) (d := 3)
      (fun x => by rw [K33Graph_degree x]) h


end Schematic.Math.GraphTheory
