import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.ShortCycleObstructions

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- In the final-cycle setting, planarity plus minimum degree three produces a
cycle vertex attached to exactly one of the two deleted endpoints.  The
all-joined case is excluded by the `K_5` extraction, and degree at most two in
`G - x - y` forces at least one endpoint attachment. -/
theorem exists_cycle_vertex_adj_exactly_one_endpoint_of_isPlanar_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hdegree :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        z ∈ C.support -> (deleteEdgeEndsGraph G x y).degree z <= 2) :
    Exists fun z : {w : V | w ∉ ({x, y} : Set V)} =>
      z ∈ C.support ∧
        ((G.Adj x (z : V) ∧ ¬ G.Adj y (z : V)) ∨
          (G.Adj y (z : V) ∧ ¬ G.Adj x (z : V))) := by
  classical
  rcases
    exists_cycle_vertex_not_adj_both_of_isPlanar_deleteEdgeEnds_cycle
      (G := G) h_planar C hC hxy with
    ⟨z, hzC, hz_not_both⟩
  have hattach :
      G.Adj (z : V) x ∨ G.Adj (z : V) y :=
    deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
      (G := G) (x := x) (y := y) hmin z (hdegree z hzC)
  rcases hattach with hzx | hzy
  · by_cases hzy' : G.Adj (z : V) y
    · exact False.elim (hz_not_both ⟨hzx.symm, hzy'.symm⟩)
    · exact ⟨z, hzC, Or.inl ⟨hzx.symm, by intro hyz; exact hzy' hyz.symm⟩⟩
  · by_cases hzx' : G.Adj (z : V) x
    · exact False.elim (hz_not_both ⟨hzx'.symm, hzy.symm⟩)
    · exact ⟨z, hzC, Or.inr ⟨hzy.symm, by intro hxz; exact hzx' hxz.symm⟩⟩

/-- Specialization of the preceding count to a hanging vertex of `G - x - y`
in the minimum-degree-three source setting. -/
theorem deleteEdgeEndsGraph_hanging_vertex_unique_neighbor_outside_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (hmin : forall w : V, 3 <= G.degree w)
    (hxy : x ≠ y)
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hz : (deleteEdgeEndsGraph G x y).degree z <= 1)
    {r s : V}
    (hrx : r ≠ x)
    (hry : r ≠ y)
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hzr : G.Adj (z : V) r)
    (hzs : G.Adj (z : V) s) :
    r = s := by
  have hdeg :
      G.degree (z : V) = 3 :=
    deleteEdgeEndsGraph_hanging_vertex_original_degree_eq_three
      (G := G) (x := x) (y := y) hmin z hz
  have hadj :
      G.Adj (z : V) x ∧ G.Adj (z : V) y :=
    (deleteEdgeEndsGraph_hanging_vertex_of_min_degree_three
      (G := G) (x := x) (y := y) hmin z hz).2
  exact neighbor_unique_outside_pair_of_degree_eq_three
    (G := G) hdeg hadj.1 hadj.2 hxy hrx hry hsx hsy hzr hzs

/-- In the two-hanging-vertices case of Makarychev Lemma 2, every vertex
outside the displayed four-vertex set is adjacent to at least one of the two
hanging vertices.  Indeed, no edge is disjoint from the four-vertex set, so
minimum degree three gives at least three neighbours among the four displayed
vertices; two of them cannot all be just `x` and `y`. -/
theorem outside_four_set_adj_hanging_of_three_neighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y u v r : V}
    (hthree :
      3 <= (G.neighborSet r ∩ ({x, y, u, v} : Set V)).ncard) :
    G.Adj r u ∨ G.Adj r v := by
  classical
  by_contra hnot
  push Not at hnot
  have hsub :
      G.neighborSet r ∩ ({x, y, u, v} : Set V) ⊆ ({x, y} : Set V) := by
    intro z hz
    rcases hz with ⟨hrz, hzS⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hzS with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hnot.1 hrz)
    · exact False.elim (hnot.2 hrz)
  have hle :
      (G.neighborSet r ∩ ({x, y, u, v} : Set V)).ncard <=
        ({x, y} : Set V).ncard :=
    Set.ncard_le_ncard hsub
  have hpair : ({x, y} : Set V).ncard <= 2 := by
    simpa using Set.ncard_insert_le x ({y} : Set V)
  omega

/-- Makarychev Lemma 2 counting reduction.  Once two distinct hanging
vertices `u,v` occur in `G - x - y`, the source hypotheses imply that there
are at most two vertices outside `{x,y,u,v}`.  This is the checked form of the
paper's sentence: every outside vertex is adjacent to at least three of
`x,y,u,v`, while each of `u,v` has original degree exactly three. -/
theorem outside_four_set_ncard_le_two_of_two_hanging_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V)) :
    ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}).ncard <= 2 := by
  classical
  let S : Set V := ({x, y, (u : V), (v : V)} : Set V)
  let Outside : Set V := {r : V | r ∉ S}
  let A : Set V := {r : V | r ∉ S ∧ G.Adj (u : V) r}
  let B : Set V := {r : V | r ∉ S ∧ G.Adj (v : V) r}
  have hno_edge :
      forall {p q : V}, G.Adj p q -> p ∉ S -> q ∉ S -> False := by
    intro p q hpq hpS hqS
    exact no_edge_outside_four_set_of_two_hanging_vertices
      (G := G) hno hmin hxy u v hu hv huv hpq
      (by simpa [S] using hpS) (by simpa [S] using hqS)
  have houtside_subset : Outside ⊆ A ∪ B := by
    intro r hrOutside
    have hthree :
        3 <= (G.neighborSet r ∩ S).ncard :=
      three_le_neighborSet_inter_of_min_degree_of_no_edge_disjoint_from_set
        (G := G) hmin hno_edge hrOutside
    have hadj :
        G.Adj r (u : V) ∨ G.Adj r (v : V) := by
      simpa [S] using
        outside_four_set_adj_hanging_of_three_neighbors
          (G := G) (x := x) (y := y) (u := (u : V)) (v := (v : V))
          (r := r) hthree
    rcases hadj with hru | hrv
    · exact Or.inl ⟨hrOutside, hru.symm⟩
    · exact Or.inr ⟨hrOutside, hrv.symm⟩
  have hA_subsingleton : A.Subsingleton := by
    intro r hr s hs
    rcases hr with ⟨hrS, hur⟩
    rcases hs with ⟨hsS, hus⟩
    have hrx : r ≠ x := by
      intro h
      exact hrS (by simp [S, h])
    have hry : r ≠ y := by
      intro h
      exact hrS (by simp [S, h])
    have hsx : s ≠ x := by
      intro h
      exact hsS (by simp [S, h])
    have hsy : s ≠ y := by
      intro h
      exact hsS (by simp [S, h])
    exact
      deleteEdgeEndsGraph_hanging_vertex_unique_neighbor_outside_pair
        (G := G) hmin hxy.ne u hu hrx hry hsx hsy hur hus
  have hB_subsingleton : B.Subsingleton := by
    intro r hr s hs
    rcases hr with ⟨hrS, hvr⟩
    rcases hs with ⟨hsS, hvs⟩
    have hrx : r ≠ x := by
      intro h
      exact hrS (by simp [S, h])
    have hry : r ≠ y := by
      intro h
      exact hrS (by simp [S, h])
    have hsx : s ≠ x := by
      intro h
      exact hsS (by simp [S, h])
    have hsy : s ≠ y := by
      intro h
      exact hsS (by simp [S, h])
    exact
      deleteEdgeEndsGraph_hanging_vertex_unique_neighbor_outside_pair
        (G := G) hmin hxy.ne v hv hrx hry hsx hsy hvr hvs
  have hA_card : A.ncard <= 1 :=
    (Set.ncard_le_one_iff_subsingleton).mpr hA_subsingleton
  have hB_card : B.ncard <= 1 :=
    (Set.ncard_le_one_iff_subsingleton).mpr hB_subsingleton
  have hOutside_card : Outside.ncard <= (A ∪ B).ncard :=
    Set.ncard_le_ncard houtside_subset
  have hAB_card : (A ∪ B).ncard <= A.ncard + B.ncard :=
    Set.ncard_union_le A B
  have htarget :
      ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}).ncard =
        Outside.ncard := by
    rfl
  rw [htarget]
  omega

/-- If the complement of a displayed four-vertex set has size at most `k`,
then the whole finite vertex type has size at most `4 + k`. -/
theorem card_le_four_add_of_four_set_compl_ncard_le
    {V : Type u} [Fintype V]
    (x y u v : V) {k : ℕ}
    (hcompl : ({r : V | r ∉ ({x, y, u, v} : Set V)}).ncard <= k) :
    Fintype.card V <= 4 + k := by
  classical
  let S : Set V := ({x, y, u, v} : Set V)
  have hS : S.ncard <= 4 := by
    have hv : ({v} : Set V).ncard <= 1 := by simp
    have huv : ({u, v} : Set V).ncard <= 2 := by
      have h := Set.ncard_insert_le u ({v} : Set V)
      omega
    have hyuv : ({y, u, v} : Set V).ncard <= 3 := by
      have h := Set.ncard_insert_le y ({u, v} : Set V)
      omega
    have hxyuv : ({x, y, u, v} : Set V).ncard <= 4 := by
      have h := Set.ncard_insert_le x ({y, u, v} : Set V)
      omega
    simpa [S] using hxyuv
  have hsum : S.ncard + Sᶜ.ncard = Nat.card V := by
    simpa [Set.ncard_univ] using Set.ncard_add_ncard_compl S
  have hcompl' : Sᶜ.ncard <= k := by
    change ({r : V | r ∉ S}).ncard <= k
    simpa [S] using hcompl
  have hnat : Nat.card V <= 4 + k := by omega
  simpa [Nat.card_eq_fintype_card] using hnat

/-- Adjacent hanging vertices are the first Figure 1 case in Makarychev
Lemma 2.  Since each of the two hanging vertices already has neighbours
`x`, `y`, and the other hanging vertex, no vertex can remain outside
`{x,y,u,v}`. -/
theorem outside_four_set_ncard_eq_zero_of_two_hanging_vertices_adj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V))
    (huv_adj : G.Adj (u : V) (v : V)) :
    ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}).ncard = 0 := by
  classical
  let S : Set V := ({x, y, (u : V), (v : V)} : Set V)
  have hno_edge :
      forall {p q : V}, G.Adj p q -> p ∉ S -> q ∉ S -> False := by
    intro p q hpq hpS hqS
    exact no_edge_outside_four_set_of_two_hanging_vertices
      (G := G) hno hmin hxy u v hu hv huv hpq
      (by simpa [S] using hpS) (by simpa [S] using hqS)
  have hempty :
      ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}) = ∅ := by
    ext r
    constructor
    · intro hr
      have hrS : r ∉ S := by simpa [S] using hr
      have hthree :
          3 <= (G.neighborSet r ∩ S).ncard :=
        three_le_neighborSet_inter_of_min_degree_of_no_edge_disjoint_from_set
          (G := G) hmin hno_edge hrS
      have hadj :
          G.Adj r (u : V) ∨ G.Adj r (v : V) := by
        simpa [S] using
          outside_four_set_adj_hanging_of_three_neighbors
            (G := G) (x := x) (y := y) (u := (u : V)) (v := (v : V))
            (r := r) hthree
      rcases hadj with hru | hrv
      · have hr_eq_v :
            r = (v : V) :=
          deleteEdgeEndsGraph_hanging_vertex_unique_neighbor_outside_pair
            (G := G) hmin hxy.ne u hu
            (by intro h; exact hrS (by simp [S, h]))
            (by intro h; exact hrS (by simp [S, h]))
            (by intro h; exact v.property (by simp [h]))
            (by intro h; exact v.property (by simp [h]))
            hru.symm huv_adj
        exact False.elim (hrS (by simp [S, hr_eq_v]))
      · have hr_eq_u :
            r = (u : V) :=
          deleteEdgeEndsGraph_hanging_vertex_unique_neighbor_outside_pair
            (G := G) hmin hxy.ne v hv
            (by intro h; exact hrS (by simp [S, h]))
            (by intro h; exact hrS (by simp [S, h]))
            (by intro h; exact u.property (by simp [h]))
            (by intro h; exact u.property (by simp [h]))
            hrv.symm huv_adj.symm
        exact False.elim (hrS (by simp [S, hr_eq_u]))
    · simp
  change ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}).ncard = 0
  rw [hempty]
  simp

/-- The adjacent Figure 1 case is planar in the repository's
Kuratowski-exclusion interface: the graph has at most four vertices. -/
theorem isPlanar_of_two_hanging_vertices_adj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V))
    (huv_adj : G.Adj (u : V) (v : V)) :
    IsPlanar G := by
  have houtside :
      ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}).ncard <= 0 := by
    rw [outside_four_set_ncard_eq_zero_of_two_hanging_vertices_adj
      (G := G) hno hmin hxy u v hu hv huv huv_adj]
  have hcard : Fintype.card V <= 4 :=
    card_le_four_add_of_four_set_compl_ncard_le
      x y (u : V) (v : V) houtside
  exact isPlanar_of_card_le_four G hcard

/-- If the two hanging vertices have a common outside neighbour, then every
outside vertex is that common neighbour.  This is the second Figure 1 case of
Makarychev Lemma 2. -/
theorem outside_four_set_ncard_le_one_of_two_hanging_vertices_common_neighbor
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y z : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V))
    (hzS : z ∉ ({x, y, (u : V), (v : V)} : Set V))
    (huz : G.Adj (u : V) z)
    (hvz : G.Adj (v : V) z) :
    ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}).ncard <= 1 := by
  classical
  let S : Set V := ({x, y, (u : V), (v : V)} : Set V)
  have hno_edge :
      forall {p q : V}, G.Adj p q -> p ∉ S -> q ∉ S -> False := by
    intro p q hpq hpS hqS
    exact no_edge_outside_four_set_of_two_hanging_vertices
      (G := G) hno hmin hxy u v hu hv huv hpq
      (by simpa [S] using hpS) (by simpa [S] using hqS)
  have hsubset :
      ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}) ⊆ ({z} : Set V) := by
    intro r hr
    have hrS : r ∉ S := by simpa [S] using hr
    have hthree :
        3 <= (G.neighborSet r ∩ S).ncard :=
      three_le_neighborSet_inter_of_min_degree_of_no_edge_disjoint_from_set
        (G := G) hmin hno_edge hrS
    have hadj :
        G.Adj r (u : V) ∨ G.Adj r (v : V) := by
      simpa [S] using
        outside_four_set_adj_hanging_of_three_neighbors
          (G := G) (x := x) (y := y) (u := (u : V)) (v := (v : V))
          (r := r) hthree
    rcases hadj with hru | hrv
    · have hr_eq_z :
          r = z :=
        deleteEdgeEndsGraph_hanging_vertex_unique_neighbor_outside_pair
          (G := G) hmin hxy.ne u hu
          (by intro h; exact hrS (by simp [S, h]))
          (by intro h; exact hrS (by simp [S, h]))
          (by intro h; exact hzS (by simp [h]))
          (by intro h; exact hzS (by simp [h]))
          hru.symm huz
      simp [hr_eq_z]
    · have hr_eq_z :
          r = z :=
        deleteEdgeEndsGraph_hanging_vertex_unique_neighbor_outside_pair
          (G := G) hmin hxy.ne v hv
          (by intro h; exact hrS (by simp [S, h]))
          (by intro h; exact hrS (by simp [S, h]))
          (by intro h; exact hzS (by simp [h]))
          (by intro h; exact hzS (by simp [h]))
          hrv.symm hvz
      simp [hr_eq_z]
  exact le_trans (Set.ncard_le_ncard hsubset) (by simp)

/-- The common-neighbour Figure 1 case is planar: the graph has at most five
vertices, and the two hanging vertices are nonadjacent, so it is not complete. -/
theorem isPlanar_of_two_hanging_vertices_common_neighbor
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y z : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V))
    (huv_not_adj : ¬ G.Adj (u : V) (v : V))
    (hzS : z ∉ ({x, y, (u : V), (v : V)} : Set V))
    (huz : G.Adj (u : V) z)
    (hvz : G.Adj (v : V) z) :
    IsPlanar G := by
  have houtside :
      ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}).ncard <= 1 :=
    outside_four_set_ncard_le_one_of_two_hanging_vertices_common_neighbor
      (G := G) hno hmin hxy u v hu hv huv hzS huz hvz
  have hcard : Fintype.card V <= 5 := by
    have h := card_le_four_add_of_four_set_compl_ncard_le
      x y (u : V) (v : V) houtside
    omega
  have hnot_complete :
      Not (forall a b : V, a ≠ b -> G.Adj a b) := by
    intro hcomplete
    exact huv_not_adj (hcomplete (u : V) (v : V) huv)
  exact isPlanar_of_card_le_five_of_not_complete hcard hnot_complete

/-- Pure local form of the distinct-neighbour Figure 1 case: if an outside
vertex already hits `u` and does not hit `v`, then three neighbours among
`{x,y,u,v}` force it to hit both deleted endpoints. -/
theorem outside_neighbor_adj_deleted_endpoints_of_three_neighbors_of_not_common
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y u v r : V}
    (hthree :
      3 <= (G.neighborSet r ∩ ({x, y, u, v} : Set V)).ncard)
    (hru : G.Adj r u)
    (hrv_not : ¬ G.Adj r v) :
    G.Adj r x ∧ G.Adj r y := by
  classical
  have hx : G.Adj r x := by
    by_contra hrx_not
    have hsub :
        G.neighborSet r ∩ ({x, y, u, v} : Set V) ⊆ ({y, u} : Set V) := by
      intro z hz
      rcases hz with ⟨hrz, hzS⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzS
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hzS with rfl | rfl | rfl | rfl
      · exact False.elim (hrx_not hrz)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (hrv_not hrz)
    have hle :
        (G.neighborSet r ∩ ({x, y, u, v} : Set V)).ncard <=
          ({y, u} : Set V).ncard :=
      Set.ncard_le_ncard hsub
    have hpair : ({y, u} : Set V).ncard <= 2 := by
      simpa using Set.ncard_insert_le y ({u} : Set V)
    omega
  have hy : G.Adj r y := by
    by_contra hry_not
    have hsub :
        G.neighborSet r ∩ ({x, y, u, v} : Set V) ⊆ ({x, u} : Set V) := by
      intro z hz
      rcases hz with ⟨hrz, hzS⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzS
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hzS with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact False.elim (hry_not hrz)
      · exact Or.inr rfl
      · exact False.elim (hrv_not hrz)
    have hle :
        (G.neighborSet r ∩ ({x, y, u, v} : Set V)).ncard <=
          ({x, u} : Set V).ncard :=
      Set.ncard_le_ncard hsub
    have hpair : ({x, u} : Set V).ncard <= 2 := by
      simpa using Set.ncard_insert_le x ({u} : Set V)
    omega
  exact ⟨hx, hy⟩

/-- Source-shaped distinct-neighbour consequence for the left hanging
vertex.  Under the two-hanging-vertices hypotheses, an outside neighbour of
`u` that is not a common neighbour of `u` and `v` is adjacent to both `x` and
`y`. -/
theorem left_outside_neighbor_adj_deleted_endpoints_of_two_hanging_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y r : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V))
    (hrS : r ∉ ({x, y, (u : V), (v : V)} : Set V))
    (hur : G.Adj (u : V) r)
    (hnot_common :
      forall z : V,
        z ∉ ({x, y, (u : V), (v : V)} : Set V) ->
          G.Adj (u : V) z -> G.Adj (v : V) z -> False) :
    G.Adj r x ∧ G.Adj r y := by
  classical
  let S : Set V := ({x, y, (u : V), (v : V)} : Set V)
  have hno_edge :
      forall {p q : V}, G.Adj p q -> p ∉ S -> q ∉ S -> False := by
    intro p q hpq hpS hqS
    exact no_edge_outside_four_set_of_two_hanging_vertices
      (G := G) hno hmin hxy u v hu hv huv hpq
      (by simpa [S] using hpS) (by simpa [S] using hqS)
  have hthree :
      3 <= (G.neighborSet r ∩ S).ncard :=
    three_le_neighborSet_inter_of_min_degree_of_no_edge_disjoint_from_set
      (G := G) hmin hno_edge (by simpa [S] using hrS)
  have hrv_not : ¬ G.Adj r (v : V) := by
    intro hrv
    exact hnot_common r hrS hur hrv.symm
  simpa [S] using
    outside_neighbor_adj_deleted_endpoints_of_three_neighbors_of_not_common
      (G := G) (x := x) (y := y) (u := (u : V)) (v := (v : V))
      (r := r) hthree hur.symm hrv_not

/-- Symmetric source-shaped distinct-neighbour consequence for the right
hanging vertex. -/
theorem right_outside_neighbor_adj_deleted_endpoints_of_two_hanging_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y r : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V))
    (hrS : r ∉ ({x, y, (u : V), (v : V)} : Set V))
    (hvr : G.Adj (v : V) r)
    (hnot_common :
      forall z : V,
        z ∉ ({x, y, (u : V), (v : V)} : Set V) ->
          G.Adj (u : V) z -> G.Adj (v : V) z -> False) :
    G.Adj r x ∧ G.Adj r y := by
  have hnot_common_swap :
      forall z : V,
        z ∉ ({x, y, (v : V), (u : V)} : Set V) ->
          G.Adj (v : V) z -> G.Adj (u : V) z -> False := by
    intro z hz hvz huz
    exact hnot_common z (by
      intro hz_orig
      apply hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz_orig ⊢
      tauto) huz hvz
  have hrS_swap :
      r ∉ ({x, y, (v : V), (u : V)} : Set V) := by
    intro hr_swap
    apply hrS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr_swap ⊢
    tauto
  have hres :=
    left_outside_neighbor_adj_deleted_endpoints_of_two_hanging_vertices
      (G := G) hno hmin hxy v u hv hu huv.symm
      hrS_swap hvr hnot_common_swap
  exact hres

/-- In the nonadjacent two-hanging-vertices case, the left hanging vertex has
some outside neighbour: its original degree is three, and `x,y` are its only
deleted-end neighbours. -/
theorem exists_left_private_neighbor_of_two_hanging_vertices_not_adj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (huv_not_adj : ¬ G.Adj (u : V) (v : V)) :
    Exists fun a : V =>
      a ∉ ({x, y, (u : V), (v : V)} : Set V) ∧ G.Adj (u : V) a := by
  classical
  have hdeg_u :
      G.degree (u : V) = 3 :=
    deleteEdgeEndsGraph_hanging_vertex_original_degree_eq_three
      (G := G) (x := x) (y := y) hmin u hu
  by_contra hnone
  push Not at hnone
  have hsub : G.neighborSet (u : V) ⊆ ({x, y} : Set V) := by
    intro z huz
    by_cases hzx : z = x
    · simp [hzx]
    by_cases hzy : z = y
    · simp [hzy]
    by_cases hzu : z = (u : V)
    · exact False.elim (huz.ne hzu.symm)
    by_cases hzv : z = (v : V)
    · exact False.elim (huv_not_adj (by simpa [hzv] using huz))
    have hzS : z ∉ ({x, y, (u : V), (v : V)} : Set V) := by
      simp [hzx, hzy, hzu, hzv]
    exact False.elim (hnone z hzS huz)
  have hcard :
      (G.neighborSet (u : V)).ncard <= ({x, y} : Set V).ncard :=
    Set.ncard_le_ncard hsub
  have hpair : ({x, y} : Set V).ncard <= 2 := by
    simpa using Set.ncard_insert_le x ({y} : Set V)
  have hdegree_card :
      (G.neighborSet (u : V)).ncard = G.degree (u : V) := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := (u : V)))
  omega

/-- Distinct-neighbour Figure 1 case, with the private left neighbour
displayed explicitly. -/
theorem isPlanar_of_two_hanging_vertices_private_left_neighbor
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y a : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V))
    (huv_not_adj : ¬ G.Adj (u : V) (v : V))
    (haS : a ∉ ({x, y, (u : V), (v : V)} : Set V))
    (hua : G.Adj (u : V) a)
    (hnot_common :
      forall z : V,
        z ∉ ({x, y, (u : V), (v : V)} : Set V) ->
          G.Adj (u : V) z -> G.Adj (v : V) z -> False) :
    IsPlanar G := by
  have houtside :
      ({r : V | r ∉ ({x, y, (u : V), (v : V)} : Set V)}).ncard <= 2 :=
    outside_four_set_ncard_le_two_of_two_hanging_vertices
      (G := G) hno hmin hxy u v hu hv huv
  have hcard : Fintype.card V <= 6 := by
    have h :=
      card_le_four_add_of_four_set_compl_ncard_le
        x y (u : V) (v : V) houtside
    omega
  have hdeg_u :
      G.degree (u : V) = 3 :=
    deleteEdgeEndsGraph_hanging_vertex_original_degree_eq_three
      (G := G) (x := x) (y := y) hmin u hu
  have hdeg_v :
      G.degree (v : V) = 3 :=
    deleteEdgeEndsGraph_hanging_vertex_original_degree_eq_three
      (G := G) (x := x) (y := y) hmin v hv
  have hva_not : ¬ G.Adj (v : V) a := by
    intro hva
    exact hnot_common a haS hua hva
  exact
    isPlanar_of_card_le_six_degree_three_private_neighbor
      (G := G) hcard hdeg_u hdeg_v huv hua huv_not_adj hva_not

/-- Distinct-neighbour Figure 1 case with no displayed private neighbour:
the private neighbour is extracted from degree three. -/
theorem isPlanar_of_two_hanging_vertices_distinct_neighbor_case
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V))
    (huv_not_adj : ¬ G.Adj (u : V) (v : V))
    (hnot_common :
      forall z : V,
        z ∉ ({x, y, (u : V), (v : V)} : Set V) ->
          G.Adj (u : V) z -> G.Adj (v : V) z -> False) :
    IsPlanar G := by
  rcases
      exists_left_private_neighbor_of_two_hanging_vertices_not_adj
        (G := G) hmin u v hu huv_not_adj with
    ⟨a, haS, hua⟩
  exact
    isPlanar_of_two_hanging_vertices_private_left_neighbor
      (G := G) hno hmin hxy u v hu hv huv huv_not_adj haS hua hnot_common

/-- Full checked Figure 1 conclusion in Makarychev Lemma 2.  Under the source
hypotheses, the existence of two distinct hanging vertices in `G - x - y`
forces `G` itself to be planar: the adjacent, common-neighbour, and
distinct-neighbour cases are all now formalized. -/
theorem isPlanar_of_two_hanging_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V)) :
    IsPlanar G := by
  classical
  by_cases huv_adj : G.Adj (u : V) (v : V)
  · exact
      isPlanar_of_two_hanging_vertices_adj
        (G := G) hno hmin hxy u v hu hv huv huv_adj
  · by_cases hcommon :
        Exists fun z : V =>
          z ∉ ({x, y, (u : V), (v : V)} : Set V) ∧
            G.Adj (u : V) z ∧ G.Adj (v : V) z
    · rcases hcommon with ⟨z, hzS, huz, hvz⟩
      exact
        isPlanar_of_two_hanging_vertices_common_neighbor
          (G := G) hno hmin hxy u v hu hv huv huv_adj hzS huz hvz
    · have hnot_common :
        forall z : V,
          z ∉ ({x, y, (u : V), (v : V)} : Set V) ->
            G.Adj (u : V) z -> G.Adj (v : V) z -> False := by
        intro z hzS huz hvz
        exact hcommon ⟨z, hzS, huz, hvz⟩
      exact
        isPlanar_of_two_hanging_vertices_distinct_neighbor_case
          (G := G) hno hmin hxy u v hu hv huv huv_adj hnot_common

/-- Makarychev Lemma 2, contradiction form.  In a non-planar graph satisfying
the source minimal-counterexample reductions, `G - x - y` cannot contain two
distinct degree-at-most-one vertices. -/
theorem not_two_hanging_vertices_of_not_planar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (u v : {w : V | w ∉ ({x, y} : Set V)})
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1)
    (huv : (u : V) ≠ (v : V)) :
    False :=
  hnonplanar
    (isPlanar_of_two_hanging_vertices
      (G := G) hno hmin hxy u v hu hv huv)

/-- Makarychev Lemma 2, uniqueness form.  The deleted-end graph has at most
one vertex of degree at most one. -/
theorem deleteEdgeEndsGraph_hanging_vertex_subsingleton_of_not_planar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    {u v : {w : V | w ∉ ({x, y} : Set V)}}
    (hu : (deleteEdgeEndsGraph G x y).degree u <= 1)
    (hv : (deleteEdgeEndsGraph G x y).degree v <= 1) :
    u = v := by
  by_contra huv_sub
  have huv : (u : V) ≠ (v : V) := by
    intro hval
    exact huv_sub (Subtype.ext hval)
  exact
      not_two_hanging_vertices_of_not_planar
        (G := G) hnonplanar hno hmin hxy u v hu hv huv

/-- Concrete Makarychev Lemma 2 corollary for the hanging-cycle block
argument: in a non-planar minimal-source configuration, the set of vertices
outside the hanging cycle is a subsingleton. -/
theorem deleteEdgeEndsGraph_outside_cycle_subsingleton_of_hanging_cycle_not_planar
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
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v)
    (hpos :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        0 < (deleteEdgeEndsGraph G x y).degree t) :
    {t : {w : V | w ∉ ({x, y} : Set V)} | t ∉ C.support}.Subsingleton :=
  deleteEdgeEndsGraph_outside_cycle_subsingleton_of_hanging_cycle_low_subsingleton
    (G := G) hno hxy C hC hv hattach hcontact hpos
    (by
      intro p q hp hq
      exact
        deleteEdgeEndsGraph_hanging_vertex_subsingleton_of_not_planar
          (G := G) hnonplanar hno hmin hxy hp hq)

/-- Source-form Makarychev Lemma 3 hanging-cycle corollary.  In the minimal
counterexample setting, no separate positivity hypothesis is needed: minimum
degree at least three in `G` already rules out isolated vertices after deleting
the ends of an edge. -/
theorem deleteEdgeEndsGraph_outside_cycle_subsingleton_of_hanging_cycle_not_planar_min_degree
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
    {t : {w : V | w ∉ ({x, y} : Set V)} | t ∉ C.support}.Subsingleton :=
  deleteEdgeEndsGraph_outside_cycle_subsingleton_of_hanging_cycle_not_planar
    (G := G) hnonplanar hno hmin hxy C hC hv hattach hcontact
    (fun t => deleteEdgeEndsGraph_degree_pos_of_min_degree_three
      (G := G) (x := x) (y := y) hmin t)


end FourColor

end Schematic.Math.GraphTheory
