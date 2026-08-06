import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.HangingCycleDichotomy

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- The length-three unique cut-leaf branch is planar.  This is the formal
triangular-prism endpoint of Makarychev's Lemma 3: the outside leaf `p` and the
first non-cut triangle vertex both have degree three, and one deleted endpoint
is a private neighbour of `p` relative to that triangle vertex. -/
theorem isPlanar_of_unique_cut_leaf_triangle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk v v)
    (hC : C.IsCycle)
    (hlen : C.length = 3)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hcontact :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hp_out : p ∉ C.support)
    (hunique :
      forall s : {w : V | w ∉ ({x, y} : Set V)},
        s ∉ C.support -> s = p) :
    IsPlanar G := by
  classical
  have h1C : C.getVert 1 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨1, rfl, by omega⟩
  have h1_ne_v : C.getVert 1 ≠ v := by
    intro h1v
    have hendpoint :
        1 = 0 ∨ 1 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 1) (by omega)).mp h1v
    omega
  have hcard : Fintype.card V <= 6 :=
    card_le_six_of_unique_cut_leaf_cycle_length_three
      (G := G) C hC hlen hunique
  have hp_data :
      G.degree (p : V) = 3 ∧ G.Adj (p : V) x ∧ G.Adj (p : V) y :=
    deleteEdgeEndsGraph_outside_hanging_cycle_original_degree_eq_three_and_adj_endpoints
      (G := G) hno hmin hxy C hC C.start_mem_support hattach hcontact hp_out
  have hdeg_p : G.degree (p : V) = 3 := hp_data.1
  have hdeg_one : G.degree (C.getVert 1 : V) = 3 :=
    unique_cut_leaf_triangle_getVert_one_degree_eq_three
      (G := G) hno hmin hxy C hC hlen hattach hcontact hp_out hunique
  have hp_ne_one : (p : V) ≠ (C.getVert 1 : V) := by
    intro hp1
    have hp1_sub : p = C.getVert 1 := Subtype.ext hp1
    exact hp_out (by simpa [hp1_sub] using h1C)
  have hp_not_adj_one : ¬ G.Adj (p : V) (C.getVert 1 : V) := by
    intro hp1_adj
    have hN :
        G.neighborSet (p : V) = ({x, y, (v : V)} : Set V) :=
      deleteEdgeEndsGraph_outside_hanging_cycle_original_neighborSet_eq
        (G := G) hno hmin hxy C hC C.start_mem_support hattach hcontact hp_out
    have hmem : (C.getVert 1 : V) ∈ ({x, y, (v : V)} : Set V) := by
      have hmemN : (C.getVert 1 : V) ∈ G.neighborSet (p : V) := hp1_adj
      rwa [hN] at hmemN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1x | h1y | h1v
    · exact (C.getVert 1).property (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl h1x)
    · exact (C.getVert 1).property (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr h1y)
    · exact h1_ne_v (Subtype.ext h1v)
  rcases
      unique_cut_leaf_triangle_getVert_one_adj_exactly_one_endpoint
        (G := G) hno hmin hxy C hC hlen hattach hcontact (p := p) hp_out with
    hleft | hright
  · exact
      isPlanar_of_card_le_six_degree_three_private_neighbor
        (G := G) (u := (p : V)) (v := (C.getVert 1 : V)) (a := y)
        hcard hdeg_p hdeg_one hp_ne_one hp_data.2.2 hp_not_adj_one hleft.2
  · exact
      isPlanar_of_card_le_six_degree_three_private_neighbor
        (G := G) (u := (p : V)) (v := (C.getVert 1 : V)) (a := x)
        hcard hdeg_p hdeg_one hp_ne_one hp_data.2.1 hp_not_adj_one hright.2

/-- First finite pattern in the unique cut-leaf length exclusion.  If the first
three vertices of `C - v` all attach to the same deleted endpoint `t`, then
`G - p - v` contains a direct-edge theta: the edge `t--C[2]` has the two common
neighbours `C[1]` and `C[3]`. -/
theorem containsHomeomorphicTheta_delete_cut_leaf_of_first_three_same_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y t : V}
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk v v)
    (hC : C.IsCycle)
    (hlen : 4 <= C.length)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hp_out : p ∉ C.support)
    (ht_avoid : t ∉ ({(p : V), (v : V)} : Set V))
    (h1t : G.Adj (C.getVert 1 : V) t)
    (h2t : G.Adj (C.getVert 2 : V) t)
    (h3t : G.Adj (C.getVert 3 : V) t) :
    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G (p : V) (v : V)) := by
  classical
  have h1C : C.getVert 1 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨1, rfl, by omega⟩
  have h2C : C.getVert 2 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨2, rfl, by omega⟩
  have h3C : C.getVert 3 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨3, rfl, by omega⟩
  have h1_ne_p : (C.getVert 1 : V) ≠ (p : V) := by
    intro h
    exact hp_out (by
      have hsub : C.getVert 1 = p := Subtype.ext h
      simpa [← hsub] using h1C)
  have h2_ne_p : (C.getVert 2 : V) ≠ (p : V) := by
    intro h
    exact hp_out (by
      have hsub : C.getVert 2 = p := Subtype.ext h
      simpa [← hsub] using h2C)
  have h3_ne_p : (C.getVert 3 : V) ≠ (p : V) := by
    intro h
    exact hp_out (by
      have hsub : C.getVert 3 = p := Subtype.ext h
      simpa [← hsub] using h3C)
  have h1_ne_v : C.getVert 1 ≠ v := by
    intro h1v
    have hendpoint :
        1 = 0 ∨ 1 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 1) (by omega)).mp h1v
    omega
  have h2_ne_v : C.getVert 2 ≠ v := by
    intro h2v
    have hendpoint :
        2 = 0 ∨ 2 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 2) (by omega)).mp h2v
    omega
  have h3_ne_v : C.getVert 3 ≠ v := by
    intro h3v
    have hendpoint :
        3 = 0 ∨ 3 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 3) (by omega)).mp h3v
    omega
  have ht_not : t ∉ ({(p : V), (v : V)} : Set V) := ht_avoid
  have h2_not : (C.getVert 2 : V) ∉ ({(p : V), (v : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h2_ne_p, fun h => h2_ne_v (Subtype.ext h)⟩
  have h1_not : (C.getVert 1 : V) ∉ ({(p : V), (v : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1_ne_p, fun h => h1_ne_v (Subtype.ext h)⟩
  have h3_not : (C.getVert 3 : V) ∉ ({(p : V), (v : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h3_ne_p, fun h => h3_ne_v (Subtype.ext h)⟩
  have h12D : (deleteEdgeEndsGraph G x y).Adj (C.getVert 1) (C.getVert 2) := by
    simpa using C.adj_getVert_succ (i := 1) (by omega : 1 < C.length)
  have h23D : (deleteEdgeEndsGraph G x y).Adj (C.getVert 2) (C.getVert 3) := by
    simpa using C.adj_getVert_succ (i := 2) (by omega : 2 < C.length)
  have h12G : G.Adj (C.getVert 1 : V) (C.getVert 2 : V) := by
    simpa [deleteEdgeEndsGraph] using h12D
  have h23G : G.Adj (C.getVert 2 : V) (C.getVert 3 : V) := by
    simpa [deleteEdgeEndsGraph] using h23D
  have h13_ne : (C.getVert 1 : V) ≠ (C.getVert 3 : V) := by
    intro h13
    have hidx : 1 = 3 :=
      hC.getVert_injOn
        (by exact ⟨by omega, by omega⟩)
        (by exact ⟨by omega, by omega⟩)
        (Subtype.ext h13)
    omega
  exact
    containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_and_two_common_neighbors
      (G := G)
      (x := t) (y := (C.getVert 2 : V))
      (u := (C.getVert 1 : V)) (v := (C.getVert 3 : V))
      (p := (p : V)) (q := (v : V))
      ht_not h2_not h1_not h3_not
      h2t.symm h1t.symm h12G.symm h3t.symm h23G h13_ne

/-- Full first-three attachment extraction in the unique cut-leaf branch.  If
the first three non-cut vertices of the hanging cycle each attach to one of the
two deleted endpoints, then deleting the unique leaf edge endpoints leaves a
homeomorphic theta.  The proof is the finite source case split: all three on
one endpoint use the direct-edge theta, adjacent pairs on one endpoint use the
split-tail theta, and the alternating pattern is a strict `K_{2,3}`. -/
theorem containsHomeomorphicTheta_delete_cut_leaf_of_first_three_attachments
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (hxy : G.Adj x y)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk v v)
    (hC : C.IsCycle)
    (hlen : 4 <= C.length)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hp_out : p ∉ C.support)
    (h1 : G.Adj (C.getVert 1 : V) x ∨ G.Adj (C.getVert 1 : V) y)
    (h2 : G.Adj (C.getVert 2 : V) x ∨ G.Adj (C.getVert 2 : V) y)
    (h3 : G.Adj (C.getVert 3 : V) x ∨ G.Adj (C.getVert 3 : V) y) :
    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G (p : V) (v : V)) := by
  classical
  have h1C : C.getVert 1 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨1, rfl, by omega⟩
  have h2C : C.getVert 2 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨2, rfl, by omega⟩
  have h3C : C.getVert 3 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨3, rfl, by omega⟩
  have h1_ne_p : (C.getVert 1 : V) ≠ (p : V) := by
    intro h
    exact hp_out (by
      have hsub : C.getVert 1 = p := Subtype.ext h
      simpa [← hsub] using h1C)
  have h2_ne_p : (C.getVert 2 : V) ≠ (p : V) := by
    intro h
    exact hp_out (by
      have hsub : C.getVert 2 = p := Subtype.ext h
      simpa [← hsub] using h2C)
  have h3_ne_p : (C.getVert 3 : V) ≠ (p : V) := by
    intro h
    exact hp_out (by
      have hsub : C.getVert 3 = p := Subtype.ext h
      simpa [← hsub] using h3C)
  have h1_ne_v : C.getVert 1 ≠ v := by
    intro h1v
    have hendpoint :
        1 = 0 ∨ 1 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 1) (by omega)).mp h1v
    omega
  have h2_ne_v : C.getVert 2 ≠ v := by
    intro h2v
    have hendpoint :
        2 = 0 ∨ 2 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 2) (by omega)).mp h2v
    omega
  have h3_ne_v : C.getVert 3 ≠ v := by
    intro h3v
    have hendpoint :
        3 = 0 ∨ 3 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 3) (by omega)).mp h3v
    omega
  have hx_not : x ∉ ({(p : V), (v : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by
      intro hxp
      exact p.property (by simp [hxp.symm]), by
      intro hxv
      exact v.property (by simp [hxv.symm])⟩
  have hy_not : y ∉ ({(p : V), (v : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by
      intro hyp
      exact p.property (by simp [hyp.symm]), by
      intro hyv
      exact v.property (by simp [hyv.symm])⟩
  have h1_not : (C.getVert 1 : V) ∉ ({(p : V), (v : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1_ne_p, fun h => h1_ne_v (Subtype.ext h)⟩
  have h2_not : (C.getVert 2 : V) ∉ ({(p : V), (v : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h2_ne_p, fun h => h2_ne_v (Subtype.ext h)⟩
  have h3_not : (C.getVert 3 : V) ∉ ({(p : V), (v : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h3_ne_p, fun h => h3_ne_v (Subtype.ext h)⟩
  have h12D : (deleteEdgeEndsGraph G x y).Adj (C.getVert 1) (C.getVert 2) := by
    simpa using C.adj_getVert_succ (i := 1) (by omega : 1 < C.length)
  have h23D : (deleteEdgeEndsGraph G x y).Adj (C.getVert 2) (C.getVert 3) := by
    simpa using C.adj_getVert_succ (i := 2) (by omega : 2 < C.length)
  have h12G : G.Adj (C.getVert 1 : V) (C.getVert 2 : V) := by
    simpa [deleteEdgeEndsGraph] using h12D
  have h23G : G.Adj (C.getVert 2 : V) (C.getVert 3 : V) := by
    simpa [deleteEdgeEndsGraph] using h23D
  have h12_ne : (C.getVert 1 : V) ≠ (C.getVert 2 : V) := h12G.ne
  have h23_ne : (C.getVert 2 : V) ≠ (C.getVert 3 : V) := h23G.ne
  have h13_ne : (C.getVert 1 : V) ≠ (C.getVert 3 : V) := by
    intro h13
    have hidx : 1 = 3 :=
      hC.getVert_injOn
        (by exact ⟨by omega, by omega⟩)
        (by exact ⟨by omega, by omega⟩)
        (Subtype.ext h13)
    omega
  have h1_ne_x : (C.getVert 1 : V) ≠ x := by
    intro h
    exact (C.getVert 1).property (Or.inl h)
  have h1_ne_y : (C.getVert 1 : V) ≠ y := by
    intro h
    exact (C.getVert 1).property (Or.inr h)
  have h2_ne_x : (C.getVert 2 : V) ≠ x := by
    intro h
    exact (C.getVert 2).property (Or.inl h)
  have h2_ne_y : (C.getVert 2 : V) ≠ y := by
    intro h
    exact (C.getVert 2).property (Or.inr h)
  have h3_ne_x : (C.getVert 3 : V) ≠ x := by
    intro h
    exact (C.getVert 3).property (Or.inl h)
  have h3_ne_y : (C.getVert 3 : V) ≠ y := by
    intro h
    exact (C.getVert 3).property (Or.inr h)
  rcases h1 with h1x | h1y <;> rcases h2 with h2x | h2y <;>
    rcases h3 with h3x | h3y
  · exact
      containsHomeomorphicTheta_delete_cut_leaf_of_first_three_same_endpoint
        (G := G) (x := x) (y := y) (t := x) C hC hlen hp_out
        hx_not h1x h2x h3x
  · exact
      containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_common_neighbor_two_edge_tail
        (G := G) (a := x) (b := (C.getVert 2 : V))
        (t := (C.getVert 1 : V)) (z := y) (w := (C.getVert 3 : V))
        (p := (p : V)) (q := (v : V))
        hx_not h2_not h1_not hy_not h3_not
        h2x.symm h1x.symm h12G.symm hxy h23G h3y
        h2_ne_x.symm h1_ne_x.symm hxy.ne h12_ne.symm
        h2_ne_y h1_ne_y h3_ne_x h23_ne.symm h13_ne.symm h3_ne_y
  · exact
      containsHomeomorphicTheta_deleteEdgeEndsGraph_of_three_common_neighbors
        (G := G) (a := x) (b := (C.getVert 2 : V))
        (u := y) (v := (C.getVert 1 : V)) (w := (C.getVert 3 : V))
        (p := (p : V)) (q := (v : V))
        hx_not h2_not hy_not h1_not h3_not
        hxy h2y h1x.symm h12G.symm h3x.symm h23G
        h2_ne_x.symm h1_ne_y.symm h3_ne_y.symm h13_ne
  · exact
      containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_common_neighbor_two_edge_tail
        (G := G) (a := y) (b := (C.getVert 2 : V))
        (t := (C.getVert 3 : V)) (z := x) (w := (C.getVert 1 : V))
        (p := (p : V)) (q := (v : V))
        hy_not h2_not h3_not hx_not h1_not
        h2y.symm h3y.symm h23G hxy.symm h12G.symm h1x
        h2_ne_y.symm h3_ne_y.symm hxy.ne.symm h23_ne
        h2_ne_x h3_ne_x h1_ne_y h12_ne h13_ne h1_ne_x
  · exact
      containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_common_neighbor_two_edge_tail
        (G := G) (a := x) (b := (C.getVert 2 : V))
        (t := (C.getVert 3 : V)) (z := y) (w := (C.getVert 1 : V))
        (p := (p : V)) (q := (v : V))
        hx_not h2_not h3_not hy_not h1_not
        h2x.symm h3x.symm h23G hxy h12G.symm h1y
        h2_ne_x.symm h3_ne_x.symm hxy.ne h23_ne
        h2_ne_y h3_ne_y h1_ne_x h12_ne h13_ne h1_ne_y
  · exact
      containsHomeomorphicTheta_deleteEdgeEndsGraph_of_three_common_neighbors
        (G := G) (a := y) (b := (C.getVert 2 : V))
        (u := x) (v := (C.getVert 1 : V)) (w := (C.getVert 3 : V))
        (p := (p : V)) (q := (v : V))
        hy_not h2_not hx_not h1_not h3_not
        hxy.symm h2x h1y.symm h12G.symm h3y.symm h23G
        h2_ne_y.symm h1_ne_x.symm h3_ne_x.symm h13_ne
  · exact
      containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_common_neighbor_two_edge_tail
        (G := G) (a := y) (b := (C.getVert 2 : V))
        (t := (C.getVert 1 : V)) (z := x) (w := (C.getVert 3 : V))
        (p := (p : V)) (q := (v : V))
        hy_not h2_not h1_not hx_not h3_not
        h2y.symm h1y.symm h12G.symm hxy.symm h23G h3x
        h2_ne_y.symm h1_ne_y.symm hxy.ne.symm h12_ne.symm
        h2_ne_x h1_ne_x h3_ne_y h23_ne.symm h13_ne.symm h3_ne_x
  · exact
      containsHomeomorphicTheta_delete_cut_leaf_of_first_three_same_endpoint
        (G := G) (x := x) (y := y) (t := y) C hC hlen hp_out
        hy_not h1y h2y h3y

/-- Length exclusion in the unique cut-leaf branch.  In the source proof this is
the sentence "Since there are not less than two such vertices, we have a
theta-subgraph": if the hanging cycle has at least four edges, the first three
non-cut vertices attach to the deleted endpoints and the preceding finite case
split builds a theta in `G - p - v`, contradicting the global edge-deletion
theta-free hypothesis. -/
theorem not_four_le_unique_cut_leaf_cycle_length
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk v v)
    (hC : C.IsCycle)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hcontact :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hp_out : p ∉ C.support) :
    ¬ 4 <= C.length := by
  intro hlen
  have h1C : C.getVert 1 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨1, rfl, by omega⟩
  have h2C : C.getVert 2 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨2, rfl, by omega⟩
  have h3C : C.getVert 3 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨3, rfl, by omega⟩
  have h1_ne_v : C.getVert 1 ≠ v := by
    intro h1v
    have hendpoint :
        1 = 0 ∨ 1 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 1) (by omega)).mp h1v
    omega
  have h2_ne_v : C.getVert 2 ≠ v := by
    intro h2v
    have hendpoint :
        2 = 0 ∨ 2 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 2) (by omega)).mp h2v
    omega
  have h3_ne_v : C.getVert 3 ≠ v := by
    intro h3v
    have hendpoint :
        3 = 0 ∨ 3 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 3) (by omega)).mp h3v
    omega
  have htheta :
      ContainsHomeomorphicTheta (deleteEdgeEndsGraph G (p : V) (v : V)) :=
    containsHomeomorphicTheta_delete_cut_leaf_of_first_three_attachments
      (G := G) hxy C hC hlen hp_out
      (hattach (C.getVert 1) h1C h1_ne_v)
      (hattach (C.getVert 2) h2C h2_ne_v)
      (hattach (C.getVert 3) h3C h3_ne_v)
  exact
    (no_homeomorphicTheta_delete_cut_leaf_endpoints_of_outside_hanging_cycle
      (G := G) hno hmin hxy C hC C.start_mem_support hattach hcontact
      hp_out) htheta

/-- The source unique cut-leaf endpoint is planar.  The checked length
exclusion forces the hanging cycle to have length three, and the previous
triangle lemma identifies the resulting graph as the planar 3-prism endpoint
used in Makarychev Lemma 3. -/
theorem isPlanar_of_unique_cut_leaf
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk v v)
    (hC : C.IsCycle)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hcontact :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hp_out : p ∉ C.support)
    (hunique :
      forall s : {w : V | w ∉ ({x, y} : Set V)},
        s ∉ C.support -> s = p) :
    IsPlanar G := by
  have hnot4 : ¬ 4 <= C.length :=
    not_four_le_unique_cut_leaf_cycle_length
      (G := G) hno hmin hxy C hC hattach hcontact hp_out
  have hlen3 : C.length = 3 := by
    have hge : 3 <= C.length := hC.three_le_length
    omega
  exact
    isPlanar_of_unique_cut_leaf_triangle
      (G := G) hno hmin hxy C hC hlen3 hattach hcontact hp_out hunique

/-- Base-free unique cut-leaf endpoint.  This is the form supplied by the
block/cactus dichotomy: the cut vertex `v` lies on the hanging cycle, but the
cycle walk may be based elsewhere.  We rotate the cycle to `v`, transport the
support-only hypotheses across `Walk.rotate`, and invoke the based theorem. -/
theorem isPlanar_of_unique_cut_leaf_of_mem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hcontact :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hp_out : p ∉ C.support)
    (hunique :
      forall s : {w : V | w ∉ ({x, y} : Set V)},
        s ∉ C.support -> s = p) :
    IsPlanar G := by
  let C' : (deleteEdgeEndsGraph G x y).Walk v v := C.rotate v hv
  have hC' : C'.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.rotate hv hC
  have hattach' :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C'.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y := by
    intro t ht htv
    exact hattach t
      ((SimpleGraph.Walk.mem_support_rotate_iff C v hv).mp ht) htv
  have hcontact' :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C'.support -> c ∈ C'.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v := by
    intro t c ht hc htc
    exact hcontact
      (by
        intro htC
        exact ht ((SimpleGraph.Walk.mem_support_rotate_iff C v hv).mpr htC))
      ((SimpleGraph.Walk.mem_support_rotate_iff C v hv).mp hc) htc
  have hp_out' : p ∉ C'.support := by
    intro hp
    exact hp_out ((SimpleGraph.Walk.mem_support_rotate_iff C v hv).mp hp)
  have hunique' :
      forall s : {w : V | w ∉ ({x, y} : Set V)},
        s ∉ C'.support -> s = p := by
    intro s hs
    exact hunique s (by
      intro hsC
      exact hs ((SimpleGraph.Walk.mem_support_rotate_iff C v hv).mpr hsC))
  exact
    isPlanar_of_unique_cut_leaf
      (G := G) hno hmin hxy C' hC' hattach' hcontact' hp_out' hunique'

/-- Unique-leaf endpoint rebased at the actual leaf contact.  The source
dichotomy without a global contact predicate gives a unique off-cycle leaf
`p`; once one contact `p--c` with the displayed cycle is known, theta-free
contact uniqueness makes `c` the only possible cycle contact of every
off-cycle vertex.  Thus the checked cut-leaf planar endpoint applies with the
cycle distinguished at `c`. -/
theorem isPlanar_of_unique_cut_leaf_of_contact
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {c p : {w : V | w ∉ ({x, y} : Set V)}}
    (hc : c ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ c ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hp_out : p ∉ C.support)
    (hpc : (deleteEdgeEndsGraph G x y).Adj p c)
    (hunique :
      forall s : {w : V | w ∉ ({x, y} : Set V)},
        s ∉ C.support -> s = p) :
    IsPlanar G := by
  classical
  have hcontact :
      forall {t d : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.support -> d ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj t d -> d = c := by
    intro t d ht hd htd
    have ht_eq : t = p := hunique t ht
    have hdp : (deleteEdgeEndsGraph G x y).Adj d p := by
      simpa [ht_eq] using htd.symm
    exact
      deleteEdgeEndsGraph_outside_vertex_cycle_contact_unique
        (G := G) hno hxy C hC hp_out hd hc hdp hpc.symm
  exact
    isPlanar_of_unique_cut_leaf_of_mem
      (G := G) hno hmin hxy C hC hc hattach hcontact hp_out hunique

/-- Non-planar source dichotomy with the unique-leaf residue discharged by
rebasing at the actual leaf contact.  The only remaining source-specific input
is the rebased attachment statement: whenever an off-cycle leaf contacts the
cycle at `c`, every other cycle vertex attaches to one deleted endpoint.
Under that input, the unique-leaf branch is planar by
`isPlanar_of_unique_cut_leaf_of_contact`, so a non-planar graph forces the
displayed cycle to span the deleted-end graph. -/
theorem deleteEdgeEndsGraph_cycle_spans_of_noncut_attach_not_planar_of_rebased_contact
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hrebased :
      forall {p c : {w : V | w ∉ ({x, y} : Set V)}},
        p ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj p c ->
            forall t : {w : V | w ∉ ({x, y} : Set V)},
              t ∈ C.support -> t ≠ c ->
                G.Adj (t : V) x ∨ G.Adj (t : V) y) :
    forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support := by
  classical
  rcases
    deleteEdgeEndsGraph_cycle_spans_or_unique_leaf_of_noncut_attach_not_planar
      (G := G) hnonplanar hno hmin hxy C hC hv hattach with
    hspans | hleaf
  · exact hspans
  · rcases hleaf with ⟨p, hp_out, hp_degree, hunique⟩
    have hp_pos : 0 < (deleteEdgeEndsGraph G x y).degree p := by
      rw [hp_degree]
      omega
    rcases ((deleteEdgeEndsGraph G x y).degree_pos_iff_exists_adj p).mp
        hp_pos with
      ⟨c, hpc⟩
    have hc : c ∈ C.support := by
      by_contra hc
      exact
        (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
          (G := G) hno hxy C hC hv hattach hpc hp_out hc)
    have hplanar : IsPlanar G :=
      isPlanar_of_unique_cut_leaf_of_contact
        (G := G) hno hmin hxy C hC hc (hrebased hp_out hc hpc)
        hp_out hpc hunique
    exact False.elim (hnonplanar hplanar)

/-- In a non-planar source-minimal graph, the hanging-cycle dichotomy cannot
take the unique cut-leaf branch, because the checked unique cut-leaf endpoint is
planar.  Thus the chosen hanging cycle spans `G - x - y`. -/
theorem deleteEdgeEndsGraph_hanging_cycle_spans_of_not_planar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {v : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hcontact :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v) :
    forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support := by
  rcases
      deleteEdgeEndsGraph_hanging_cycle_spans_or_unique_cut_leaf_not_planar
        (G := G) hnonplanar hno hmin hxy C hC hv hattach hcontact with
    hspans | hleaf
  · exact hspans
  · rcases hleaf with ⟨p, hp_out, _hp_neighbor, hunique⟩
    exact False.elim
      (hnonplanar
        (isPlanar_of_unique_cut_leaf_of_mem
          (G := G) hno hmin hxy C hC hv hattach hcontact hp_out hunique))


end FourColor

end Schematic.Math.GraphTheory
