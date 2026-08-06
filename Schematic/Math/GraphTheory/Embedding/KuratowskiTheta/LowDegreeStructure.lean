import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.CycleContacts
import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.SubdivisionObstructions
import Schematic.Math.GraphTheory.Connectivity.Separations

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

@[simp]
theorem deleteEdgeEndsGraph_adj_iff
    {V : Type u}
    {G : SimpleGraph V}
    {x y : V}
    {u v : {z : V | z ∉ ({x, y} : Set V)}} :
    (deleteEdgeEndsGraph G x y).Adj u v ↔ G.Adj (u : V) (v : V) :=
  Iff.rfl

/-- A nontrivial simple path of length at least two has its second vertex as
an internal vertex.  This small walk fact is used when a finite strict
subdivision has no room for subdivision vertices: any split source edge would
produce an internal branch vertex. -/
theorem Walk.snd_mem_internalVertices_of_isPath_length_gt_one
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hlen : 1 < p.length) :
    p.snd ∈ Walk.InternalVertices p := by
  classical
  refine ⟨p.getVert_mem_support 1, ?_, ?_⟩
  · have hnot_nil : ¬ p.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      omega
    have hadj : G.Adj u p.snd := SimpleGraph.Walk.adj_snd hnot_nil
    intro hsnd
    exact hadj.ne hsnd.symm
  · intro hsnd_end
    have hlt_one : 1 < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hlt_last : p.length < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hsnd_get : p.support[1]'hlt_one = p.snd := by
      simp
    have hend_get : p.support[p.length]'hlt_last = v := by
      simp
    have hidx_snd : p.support.idxOf p.snd = 1 := by
      rw [← hsnd_get]
      exact hp.support_nodup.idxOf_getElem 1 hlt_one
    have hidx_end_raw :
        p.support.idxOf (p.support[p.length]'hlt_last) = p.length :=
      hp.support_nodup.idxOf_getElem p.length hlt_last
    have hidx_end : p.support.idxOf v = p.length := by
      simpa [hend_get] using hidx_end_raw
    have hidx_snd_v : p.support.idxOf v = 1 := by
      simpa [hsnd_end] using hidx_snd
    omega

/-- If every host vertex is a branch vertex in a strict subdivision, then all
source edges are unsplit. -/
theorem StrictSubdivisionModel.edgeUnsplit_of_branchVertex_surjective
    {W : Type*} {V : Type u} [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (hsurj : Function.Surjective M.branchVertex)
    {x y : W}
    (hxy : H.Adj x y) :
    M.EdgeUnsplit hxy := by
  classical
  by_contra hnot
  let p : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath hxy
  have hpos : 0 < p.length := by
    by_contra hzero_not
    have hzero : p.length = 0 := by omega
    have hend :
        M.branchVertex x = M.branchVertex y :=
      SimpleGraph.Walk.eq_of_length_eq_zero (p := p) hzero
    exact hxy.ne (M.branchVertex_injective hend)
  have hgt : 1 < p.length := by
    have hne_one : p.length ≠ 1 := by
      intro hone
      exact hnot hone
    omega
  have hsnd_internal :
      p.snd ∈ Walk.InternalVertices p :=
    Walk.snd_mem_internalVertices_of_isPath_length_gt_one
      (G := G) (p := p) (M.edgePath_isPath hxy) hgt
  rcases hsurj p.snd with ⟨w, hw⟩
  exact M.no_internal_branch_vertices' hxy hsnd_internal w hw.symm

theorem StrictSubdivisionModel.adj_of_branchVertex_surjective
    {W : Type*} {V : Type u} [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (hsurj : Function.Surjective M.branchVertex)
    {x y : W}
    (hxy : H.Adj x y) :
    G.Adj (M.branchVertex x) (M.branchVertex y) :=
  M.adj_of_edgeUnsplit
    hxy
    (StrictSubdivisionModel.edgeUnsplit_of_branchVertex_surjective
      M hsurj hxy)

/-- In `K_{3,3}`, two distinct vertices are either adjacent or have the same
neighbour set. -/
theorem K33Graph.adj_or_neighborSet_eq_of_ne
    {x y : K33Vertex}
    (hxy : x ≠ y) :
    K33Graph.Adj x y ∨ K33Graph.neighborSet x = K33Graph.neighborSet y := by
  classical
  rcases x with x | x <;> rcases y with y | y
  · right
    ext z
    rcases z with z | z <;> simp [K33Graph]
  · left
    simp [K33Graph]
  · left
    simp [K33Graph]
  · right
    ext z
    rcases z with z | z <;> simp [K33Graph]

/-- Two neighbours of a common vertex in `K_{3,3}` lie on the same side of
the bipartition, so they are not adjacent. -/
theorem K33Graph.not_adj_of_common_neighbor
    {u x y : K33Vertex}
    (hux : K33Graph.Adj u x)
    (huy : K33Graph.Adj u y) :
    ¬ K33Graph.Adj x y := by
  rcases u with u | u <;> rcases x with x | x <;> rcases y with y | y <;>
    simp [K33Graph] at hux huy ⊢

/-- A strict `K_{3,3}` model in a six-vertex host uses all host vertices as
branch vertices. -/
theorem StrictSubdivisionModel.K33_branchVertex_surjective_of_card_le_six
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (M : StrictSubdivisionModel K33Graph G)
    (hcard : Fintype.card V <= 6) :
    Function.Surjective M.branchVertex := by
  classical
  have hnat : Nat.card V <= Nat.card K33Vertex := by
    simpa [Nat.card_eq_fintype_card, card_K33Vertex] using hcard
  exact (M.branchVertex_injective.bijective_of_nat_card_le hnat).2

/-- In a surjective strict `K_{3,3}` model, if a branch vertex has host degree
three, every ambient neighbour of that branch vertex is the image of a source
neighbour. -/
theorem StrictSubdivisionModel.K33_source_neighbor_of_host_neighbor_of_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    (hsurj : Function.Surjective M.branchVertex)
    {s : K33Vertex}
    (hdeg : G.degree (M.branchVertex s) = 3)
    {z : V}
    (hz : G.Adj (M.branchVertex s) z) :
    Exists fun t : K33Vertex => K33Graph.Adj s t ∧ M.branchVertex t = z := by
  classical
  let N : Set K33Vertex := K33Graph.neighborSet s
  let A : Set V := M.branchVertex '' N
  have hA_sub : A ⊆ G.neighborSet (M.branchVertex s) := by
    intro w hw
    rcases hw with ⟨t, htN, rfl⟩
    exact StrictSubdivisionModel.adj_of_branchVertex_surjective
      M hsurj htN
  have hN_card : N.ncard = 3 := by
    rw [← Set.fintypeCard_eq_ncard N]
    change Fintype.card (K33Graph.neighborSet s) = 3
    rw [SimpleGraph.card_neighborSet_eq_degree, K33Graph_degree s]
  have hA_card : A.ncard = 3 := by
    calc
      A.ncard = N.ncard := by
        exact Set.ncard_image_of_injective N M.branchVertex_injective
      _ = 3 := hN_card
  have hG_card : (G.neighborSet (M.branchVertex s)).ncard = 3 := by
    simpa [Set.ncard_eq_toFinset_card', hdeg] using
      (SimpleGraph.card_neighborSet_eq_degree
        (G := G) (v := M.branchVertex s))
  have hG_sub_A :
      G.neighborSet (M.branchVertex s) ⊆ A := by
    have heq :
        A = G.neighborSet (M.branchVertex s) :=
      Set.eq_of_subset_of_ncard_le hA_sub (by omega)
    intro w hw
    simpa [heq] using hw
  have hzA : z ∈ A := hG_sub_A hz
  rcases hzA with ⟨t, htN, ht⟩
  exact ⟨t, htN, ht⟩

/-- If all neighbours of a vertex lie in a displayed triple, then its degree is
at most three. -/
theorem degree_le_three_of_neighborSet_subset_triple
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u a b c : V}
    (hsub : G.neighborSet u ⊆ ({a, b, c} : Set V)) :
    G.degree u <= 3 := by
  classical
  have hle :
      (G.neighborSet u).ncard <= ({a, b, c} : Set V).ncard :=
    Set.ncard_le_ncard hsub
  have htriple : ({a, b, c} : Set V).ncard <= 3 := by
    have hbc : ({b, c} : Set V).ncard <= 2 := by
      have hbc' : ({b, c} : Set V).ncard <= ({c} : Set V).ncard + 1 :=
        Set.ncard_insert_le b ({c} : Set V)
      simp at hbc'
      exact hbc'
    have habc : ({a, b, c} : Set V).ncard <= ({b, c} : Set V).ncard + 1 :=
      Set.ncard_insert_le a ({b, c} : Set V)
    omega
  have hdegree_ncard :
      (G.neighborSet u).ncard = G.degree u := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := u))
  omega

/-- Degree-at-most-three exclusion form: once three distinct neighbours of
`u` are displayed, every other neighbour of `u` is one of them. -/
theorem neighborSet_subset_triple_of_degree_le_three
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u a b c : V}
    (hdeg : G.degree u <= 3)
    (hua : G.Adj u a)
    (hub : G.Adj u b)
    (huc : G.Adj u c)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    G.neighborSet u ⊆ ({a, b, c} : Set V) := by
  classical
  intro w huw
  by_contra hwabc
  have hwa : w ≠ a := by
    intro h
    exact hwabc (by simp [h])
  have hwb : w ≠ b := by
    intro h
    exact hwabc (by simp [h])
  have hwc : w ≠ c := by
    intro h
    exact hwabc (by simp [h])
  have hfour_sub :
      ({a, b, c, w} : Set V) ⊆ G.neighborSet u := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hua
    · exact hub
    · exact huc
    · exact huw
  have hfour_card : ({a, b, c, w} : Set V).ncard = 4 := by
    simp [hab, hac, hbc, hwa.symm, hwb.symm, hwc.symm]
  have hle :
      ({a, b, c, w} : Set V).ncard <= (G.neighborSet u).ncard :=
    Set.ncard_le_ncard hfour_sub
  have hdegree_ncard :
      (G.neighborSet u).ncard = G.degree u := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := u))
  rw [hfour_card, hdegree_ncard] at hle
  omega

/-- Six-vertex obstruction eliminator for the distinct-neighbour case: if
`u` has degree three, `u` and `v` are nonadjacent, and `u` has a neighbour
`a` that is not adjacent to `v`, then no strict `K_{3,3}` subdivision exists.
The proof is the ordinary-source version of the Figure 1 argument: in a
six-vertex model all source edges are unsplit; nonadjacent branch preimages in
`K_{3,3}` lie on the same side and hence have the same source neighbour set,
forcing `v` adjacent to `a`. -/
theorem not_containsStrictSubdivision_K33_of_card_le_six_degree_three_private_neighbor
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 6)
    {u v a : V}
    (hdeg_u : G.degree u = 3)
    (huv : u ≠ v)
    (hua : G.Adj u a)
    (huv_not_adj : ¬ G.Adj u v)
    (hva_not_adj : ¬ G.Adj v a) :
    Not (ContainsStrictSubdivision K33Graph G) := by
  classical
  rintro ⟨M⟩
  have hsurj :
      Function.Surjective M.branchVertex :=
    StrictSubdivisionModel.K33_branchVertex_surjective_of_card_le_six
      M hcard
  rcases hsurj u with ⟨su, hsu⟩
  rcases hsurj v with ⟨sv, hsv⟩
  rcases hsurj a with ⟨sa, hsa⟩
  have hsu_ne_sv : su ≠ sv := by
    intro h
    exact huv (by simpa [hsu, hsv] using congrArg M.branchVertex h)
  have hsource_not_adj : ¬ K33Graph.Adj su sv := by
    intro hsource
    have hadj :
        G.Adj (M.branchVertex su) (M.branchVertex sv) :=
      StrictSubdivisionModel.adj_of_branchVertex_surjective
        M hsurj hsource
    exact huv_not_adj (by simpa [hsu, hsv] using hadj)
  have hN_eq : K33Graph.neighborSet su = K33Graph.neighborSet sv := by
    rcases K33Graph.adj_or_neighborSet_eq_of_ne hsu_ne_sv with hadj | hN
    · exact False.elim (hsource_not_adj hadj)
    · exact hN
  have hdeg_su : G.degree (M.branchVertex su) = 3 := by
    rw [hsu]
    exact hdeg_u
  rcases
      StrictSubdivisionModel.K33_source_neighbor_of_host_neighbor_of_degree_three
        M hsurj hdeg_su (by simpa [hsu, hsa] using hua) with
    ⟨t, hsu_t, ht_a⟩
  have hsv_t : K33Graph.Adj sv t := by
    have ht_mem_su : t ∈ K33Graph.neighborSet su := hsu_t
    simpa [hN_eq] using ht_mem_su
  have h_v_a :
      G.Adj v a := by
    have hraw :
        G.Adj (M.branchVertex sv) (M.branchVertex t) :=
      StrictSubdivisionModel.adj_of_branchVertex_surjective
        M hsurj hsv_t
    simpa [hsv, ht_a] using hraw
  exact hva_not_adj h_v_a

/-- With two specified degree-three vertices, a six-vertex host has at most
four vertices of degree at least four. -/
theorem highDegree_four_ncard_le_four_of_card_le_six_two_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 6)
    {u v : V}
    (huv : u ≠ v)
    (hdeg_u : G.degree u = 3)
    (hdeg_v : G.degree v = 3) :
    {w : V | 4 <= G.degree w}.ncard <= 4 := by
  classical
  let S : Set V := ({u, v} : Set V)
  have hsub : {w : V | 4 <= G.degree w} ⊆ Sᶜ := by
    intro w hw hS
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
    rcases hS with rfl | rfl
    · have hwdeg : 4 <= G.degree w := hw
      rw [hdeg_u] at hwdeg
      omega
    · have hwdeg : 4 <= G.degree w := hw
      rw [hdeg_v] at hwdeg
      omega
  have hpair : S.ncard = 2 := by
    simpa [S] using Set.ncard_pair huv
  have hsum : S.ncard + Sᶜ.ncard = Nat.card V := by
    simpa [Set.ncard_univ] using Set.ncard_add_ncard_compl S
  have hcompl : Sᶜ.ncard <= 4 := by
    have hnat : Nat.card V <= 6 := by
      simpa [Nat.card_eq_fintype_card] using hcard
    omega
  exact (Set.ncard_le_ncard hsub).trans hcompl

/-- Planarity eliminator for the six-vertex distinct-neighbour Figure 1
case.  A private neighbour of one degree-three hanging vertex rules out
`K_{3,3}`, while the two degree-three vertices bound the possible `K_5`
branch vertices. -/
theorem isPlanar_of_card_le_six_degree_three_private_neighbor
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 6)
    {u v a : V}
    (hdeg_u : G.degree u = 3)
    (hdeg_v : G.degree v = 3)
    (huv : u ≠ v)
    (hua : G.Adj u a)
    (huv_not_adj : ¬ G.Adj u v)
    (hva_not_adj : ¬ G.Adj v a) :
    IsPlanar G := by
  constructor
  · intro hK5
    have hge :
        5 <= {w : V | 4 <= G.degree w}.ncard :=
      highDegree_four_ncard_ge_five_of_containsStrictSubdivision_K5 hK5
    have hle :
        {w : V | 4 <= G.degree w}.ncard <= 4 :=
      highDegree_four_ncard_le_four_of_card_le_six_two_degree_three
        (G := G) hcard huv hdeg_u hdeg_v
    omega
  · exact
      not_containsStrictSubdivision_K33_of_card_le_six_degree_three_private_neighbor
        (G := G) hcard hdeg_u huv hua huv_not_adj hva_not_adj

theorem deleteEdgeEndsGraph_degree_zero_forces_original_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hdegree :
      (deleteEdgeEndsGraph G x y).degree z = 0) :
    G.degree (z : V) <= 2 := by
  have hbound := degree_le_induce_compl_degree_add_ncard
    (G := G) ({x, y} : Set V) z.property
  change G.degree (z : V) <=
    (deleteEdgeEndsGraph G x y).degree z + ({x, y} : Set V).ncard at hbound
  have hpair : ({x, y} : Set V).ncard <= 2 := by
    simpa using Set.ncard_insert_le x ({y} : Set V)
  omega

theorem original_degree_le_deleteEdgeEndsGraph_degree_add_one_of_not_adj_left
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hnot : ¬ G.Adj (z : V) x) :
    G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z + 1 := by
  have hbound := degree_le_induce_compl_degree_add_neighbor_inter_ncard
    (G := G) ({x, y} : Set V) z.property
  change G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z +
    (G.neighborSet (z : V) ∩ ({x, y} : Set V)).ncard at hbound
  have hsub :
      G.neighborSet (z : V) ∩ ({x, y} : Set V) ⊆ ({y} : Set V) := by
    intro w hw
    simp only [Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    rcases hw.2 with rfl | rfl
    · exact False.elim (hnot hw.1)
    · rfl
  have hinter :
      (G.neighborSet (z : V) ∩ ({x, y} : Set V)).ncard <= 1 := by
    simpa using Set.ncard_le_ncard hsub
  omega

theorem original_degree_le_deleteEdgeEndsGraph_degree_add_one_of_not_adj_right
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hnot : ¬ G.Adj (z : V) y) :
    G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z + 1 := by
  have hbound := degree_le_induce_compl_degree_add_neighbor_inter_ncard
    (G := G) ({x, y} : Set V) z.property
  change G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z +
    (G.neighborSet (z : V) ∩ ({x, y} : Set V)).ncard at hbound
  have hsub :
      G.neighborSet (z : V) ∩ ({x, y} : Set V) ⊆ ({x} : Set V) := by
    intro w hw
    simp only [Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    rcases hw.2 with rfl | rfl
    · rfl
    · exact False.elim (hnot hw.1)
  have hinter :
      (G.neighborSet (z : V) ∩ ({x, y} : Set V)).ncard <= 1 := by
    simpa using Set.ncard_le_ncard hsub
  omega

theorem deleteEdgeEndsGraph_small_degree_original_degree_ge_three_forces_adj_endpoints
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hdelete : (deleteEdgeEndsGraph G x y).degree z <= 1)
    (horig : 3 <= G.degree (z : V)) :
    G.Adj (z : V) x ∧ G.Adj (z : V) y := by
  constructor
  · by_contra hnot
    have hbound :=
      original_degree_le_deleteEdgeEndsGraph_degree_add_one_of_not_adj_left
        (G := G) (x := x) (y := y) z hnot
    omega
  · by_contra hnot
    have hbound :=
      original_degree_le_deleteEdgeEndsGraph_degree_add_one_of_not_adj_right
        (G := G) (x := x) (y := y) z hnot
    omega

/-- Under the minimum-degree-three standing assumption used in the
Makarychev/Skopenkov proposition, deleting the two ends of an edge leaves no
isolated vertex. -/
theorem deleteEdgeEndsGraph_degree_pos_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (z : {w : V | w ∉ ({x, y} : Set V)}) :
    0 < (deleteEdgeEndsGraph G x y).degree z := by
  classical
  by_contra hnot
  have hz0 : (deleteEdgeEndsGraph G x y).degree z = 0 := by
    omega
  have hle :
      G.degree (z : V) <= 2 :=
    deleteEdgeEndsGraph_degree_zero_forces_original_degree_le_two
      (G := G) (x := x) (y := y) z hz0
  have hge : 3 <= G.degree (z : V) := hmin (z : V)
  omega

/-- Source corollary: with original minimum degree at least three, every
degree-zero-or-one vertex of `G - x - y` is adjacent in `G` to both deleted
endpoints.  This is the formal version of the line "if it has a hanging
vertex `p`, then `p` is joined both to `x` and to `y`". -/
theorem deleteEdgeEndsGraph_small_degree_adj_endpoints_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hdelete : (deleteEdgeEndsGraph G x y).degree z <= 1) :
    G.Adj (z : V) x ∧ G.Adj (z : V) y :=
  deleteEdgeEndsGraph_small_degree_original_degree_ge_three_forces_adj_endpoints
    (G := G) (x := x) (y := y) z hdelete (hmin (z : V))

/-- Source-facing hanging-vertex branch for `G - x - y`: under the original
minimum-degree-three assumption, a vertex of degree at most one in
`G - x - y` is in fact a degree-one vertex there and is adjacent in `G` to
both deleted endpoints. -/
theorem deleteEdgeEndsGraph_hanging_vertex_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hdelete : (deleteEdgeEndsGraph G x y).degree z <= 1) :
    (deleteEdgeEndsGraph G x y).degree z = 1 ∧
      G.Adj (z : V) x ∧ G.Adj (z : V) y := by
  have hpos :
      0 < (deleteEdgeEndsGraph G x y).degree z :=
    deleteEdgeEndsGraph_degree_pos_of_min_degree_three
      (G := G) (x := x) (y := y) hmin z
  have hadj :
      G.Adj (z : V) x ∧ G.Adj (z : V) y :=
    deleteEdgeEndsGraph_small_degree_adj_endpoints_of_min_degree_three
      (G := G) (x := x) (y := y) hmin z hdelete
  exact ⟨by omega, hadj⟩

/-- Minimum-degree-three form of the hanging-cycle leaf step: once the source
reduction gives minimum degree at least three in `G`, the separate
non-isolated hypothesis for `G - x - y` is automatic. -/
theorem deleteEdgeEndsGraph_degree_eq_one_of_outside_hanging_cycle_min_degree
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
    (hp_out : p ∉ C.support) :
    (deleteEdgeEndsGraph G x y).degree p = 1 :=
  deleteEdgeEndsGraph_degree_eq_one_of_outside_hanging_cycle
    (G := G) hno hxy C hC hv hattach hcontact
    (fun t => deleteEdgeEndsGraph_degree_pos_of_min_degree_three
      (G := G) (x := x) (y := y) hmin t)
    hp_out

/-- In the source hanging-cycle setup, every outside vertex is attached in
`G - x - y` to the unique cut vertex of the hanging cycle. -/
theorem deleteEdgeEndsGraph_adj_cutVertex_of_outside_hanging_cycle_min_degree
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
    (hp_out : p ∉ C.support) :
    (deleteEdgeEndsGraph G x y).Adj p v := by
  classical
  have hpos :
      0 < (deleteEdgeEndsGraph G x y).degree p :=
    deleteEdgeEndsGraph_degree_pos_of_min_degree_three
      (G := G) (x := x) (y := y) hmin p
  rcases ((deleteEdgeEndsGraph G x y).degree_pos_iff_exists_adj p).mp hpos with
    ⟨w, hpw⟩
  by_cases hwC : w ∈ C.support
  · have hwv : w = v := hcontact hp_out hwC hpw
    simpa [hwv] using hpw
  · exact False.elim
      (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
        (G := G) hno hxy C hC hv hattach hpw hp_out hwC)

/-- Strong leaf form of the hanging-cycle step: an outside vertex has exactly
the cut vertex as its neighbour in `G - x - y`. -/
theorem deleteEdgeEndsGraph_neighborSet_eq_singleton_cutVertex_of_outside_hanging_cycle_min_degree
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
    (hp_out : p ∉ C.support) :
    (deleteEdgeEndsGraph G x y).neighborSet p = {v} := by
  classical
  ext t
  constructor
  · intro hpt
    by_cases htC : t ∈ C.support
    · exact by
        have htv : t = v := hcontact hp_out htC hpt
        rw [htv]
        exact Set.mem_singleton v
    · exact False.elim
        (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
          (G := G) hno hxy C hC hv hattach hpt hp_out htC)
  · intro ht
    have htv : t = v := by simpa using ht
    rw [htv]
    exact
      deleteEdgeEndsGraph_adj_cutVertex_of_outside_hanging_cycle_min_degree
        (G := G) hno hmin hxy C hC hv hattach hcontact hp_out

theorem original_degree_le_deleteEdgeEndsGraph_degree_add_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (z : {w : V | w ∉ ({x, y} : Set V)}) :
    G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z + 2 := by
  have hbound := degree_le_induce_compl_degree_add_ncard
    (G := G) ({x, y} : Set V) z.property
  change G.degree (z : V) <=
    (deleteEdgeEndsGraph G x y).degree z + ({x, y} : Set V).ncard at hbound
  have hpair : ({x, y} : Set V).ncard <= 2 := by
    simpa using Set.ncard_insert_le x ({y} : Set V)
  omega

/-- In the source proof's minimum-degree-three setting, a hanging vertex of
`G - x - y` has original degree exactly three: its one remaining neighbour in
`G - x - y`, plus `x` and `y`. -/
theorem deleteEdgeEndsGraph_hanging_vertex_original_degree_eq_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hdelete : (deleteEdgeEndsGraph G x y).degree z <= 1) :
    G.degree (z : V) = 3 := by
  have hdel :
      (deleteEdgeEndsGraph G x y).degree z = 1 :=
    (deleteEdgeEndsGraph_hanging_vertex_of_min_degree_three
      (G := G) (x := x) (y := y) hmin z hdelete).1
  have hle :
      G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z + 2 :=
    original_degree_le_deleteEdgeEndsGraph_degree_add_two
      (G := G) (x := x) (y := y) z
  have hge : 3 <= G.degree (z : V) := hmin (z : V)
  omega

/-- Original-graph data for the unique cut-leaf branch: an outside leaf of the
hanging-cycle decomposition has original degree exactly three and is adjacent
to both deleted endpoints. -/
theorem deleteEdgeEndsGraph_outside_hanging_cycle_original_degree_eq_three_and_adj_endpoints
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
    (hp_out : p ∉ C.support) :
    G.degree (p : V) = 3 ∧ G.Adj (p : V) x ∧ G.Adj (p : V) y := by
  have hpdeg_delete :
      (deleteEdgeEndsGraph G x y).degree p = 1 :=
    deleteEdgeEndsGraph_degree_eq_one_of_outside_hanging_cycle_min_degree
      (G := G) hno hmin hxy C hC hv hattach hcontact hp_out
  have hhang :=
    deleteEdgeEndsGraph_hanging_vertex_of_min_degree_three
      (G := G) (x := x) (y := y) hmin p (by omega)
  have hdeg :
      G.degree (p : V) = 3 :=
    deleteEdgeEndsGraph_hanging_vertex_original_degree_eq_three
      (G := G) (x := x) (y := y) hmin p (by omega)
  exact ⟨hdeg, hhang.2⟩

/-- The source "delete the endpoints of this edge" input in the unique
cut-leaf branch: the cut-leaf edge `p-v` is an edge of `G`, so the global
two-end-deletion hypothesis applies to `G - p - v`. -/
theorem no_homeomorphicTheta_delete_cut_leaf_endpoints_of_outside_hanging_cycle
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
    (hp_out : p ∉ C.support) :
    Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G (p : V) (v : V))) := by
  have hpv_delete :
      (deleteEdgeEndsGraph G x y).Adj p v :=
    deleteEdgeEndsGraph_adj_cutVertex_of_outside_hanging_cycle_min_degree
      (G := G) hno hmin hxy C hC hv hattach hcontact hp_out
  have hpv : G.Adj (p : V) (v : V) := by
    simpa [deleteEdgeEndsGraph] using hpv_delete
  exact hno hpv

/-- A degree-three vertex with three displayed, distinct neighbours has
exactly those neighbours. -/
theorem neighborSet_eq_triple_of_degree_eq_three
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {z a b c : V}
    (hdeg : G.degree z = 3)
    (hza : G.Adj z a)
    (hzb : G.Adj z b)
    (hzc : G.Adj z c)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    G.neighborSet z = ({a, b, c} : Set V) := by
  classical
  apply Set.Subset.antisymm
  · intro w hzw
    by_contra hwabc
    have hwa : w ≠ a := by
      intro h
      exact hwabc (by simp [h])
    have hwb : w ≠ b := by
      intro h
      exact hwabc (by simp [h])
    have hwc : w ≠ c := by
      intro h
      exact hwabc (by simp [h])
    have hfour_sub :
        ({a, b, c, w} : Set V) ⊆ G.neighborSet z := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hza
      · exact hzb
      · exact hzc
      · exact hzw
    have hfour_card : ({a, b, c, w} : Set V).ncard = 4 := by
      simp [hab, hac, hbc, hwa.symm, hwb.symm, hwc.symm]
    have hle :
        ({a, b, c, w} : Set V).ncard <= (G.neighborSet z).ncard :=
      Set.ncard_le_ncard hfour_sub
    have hdegree_ncard :
        (G.neighborSet z).ncard = G.degree z := by
      simpa [Set.ncard_eq_toFinset_card'] using
        (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := z))
    rw [hfour_card, hdegree_ncard, hdeg] at hle
    omega
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hza
    · exact hzb
    · exact hzc

/-- The unique cut-leaf branch has a completely identified original
neighbourhood: the outside leaf is adjacent exactly to the two deleted
endpoints and to the hanging-cycle cut vertex. -/
theorem deleteEdgeEndsGraph_outside_hanging_cycle_original_neighborSet_eq
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
    (hp_out : p ∉ C.support) :
    G.neighborSet (p : V) = ({x, y, (v : V)} : Set V) := by
  have hdata :
      G.degree (p : V) = 3 ∧ G.Adj (p : V) x ∧ G.Adj (p : V) y :=
    deleteEdgeEndsGraph_outside_hanging_cycle_original_degree_eq_three_and_adj_endpoints
      (G := G) hno hmin hxy C hC hv hattach hcontact hp_out
  have hpv_delete :
      (deleteEdgeEndsGraph G x y).Adj p v :=
    deleteEdgeEndsGraph_adj_cutVertex_of_outside_hanging_cycle_min_degree
      (G := G) hno hmin hxy C hC hv hattach hcontact hp_out
  have hpv : G.Adj (p : V) (v : V) := by
    simpa [deleteEdgeEndsGraph] using hpv_delete
  have hxv : x ≠ (v : V) := by
    intro hxv
    exact v.property (by simp [hxv])
  have hyv : y ≠ (v : V) := by
    intro hyv
    exact v.property (by simp [hyv])
  exact
    neighborSet_eq_triple_of_degree_eq_three
      (G := G) hdata.1 hdata.2.1 hdata.2.2 hpv
      hxy.ne hxv hyv

/-- Makarychev Lemma 2 local exclusion.  Under the source hypotheses that all
two-end deletions are homeomorphic-theta-free and the current graph has
minimum degree at least three, two distinct hanging vertices of `G - x - y`
together with the edge `xy` forbid any edge disjoint from `{x,y,u,v}`.
Otherwise that disjoint edge's endpoint deletion would still contain the
direct-edge theta with branches through `u` and `v`. -/
theorem no_edge_disjoint_from_two_hanging_vertices_of_forall_deleteEdgeEnds_no_homeomorphicTheta
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
    {p q : V}
    (hpq : G.Adj p q)
    (hx_pq : x ∉ ({p, q} : Set V))
    (hy_pq : y ∉ ({p, q} : Set V))
    (hu_pq : (u : V) ∉ ({p, q} : Set V))
    (hv_pq : (v : V) ∉ ({p, q} : Set V)) :
    False := by
  have hu_adj :
      G.Adj (u : V) x ∧ G.Adj (u : V) y :=
    (deleteEdgeEndsGraph_hanging_vertex_of_min_degree_three
      (G := G) (x := x) (y := y) hmin u hu).2
  have hv_adj :
      G.Adj (v : V) x ∧ G.Adj (v : V) y :=
    (deleteEdgeEndsGraph_hanging_vertex_of_min_degree_three
      (G := G) (x := x) (y := y) hmin v hv).2
  exact
    no_edge_disjoint_from_edge_theta_of_forall_deleteEdgeEnds_no_homeomorphicTheta
      (G := G) hno hpq hx_pq hy_pq hu_pq hv_pq hxy
      hu_adj.1.symm hu_adj.2.symm hv_adj.1.symm hv_adj.2.symm huv

/-- Set-oriented form of the two-hanging-vertices edge exclusion.  This is
the interface used by the counting arguments: an edge cannot have both
endpoints outside the displayed four-vertex set. -/
theorem no_edge_outside_four_set_of_two_hanging_vertices
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
    {p q : V}
    (hpq : G.Adj p q)
    (hp_out : p ∉ ({x, y, (u : V), (v : V)} : Set V))
    (hq_out : q ∉ ({x, y, (u : V), (v : V)} : Set V)) :
    False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp_out hq_out
  apply
    no_edge_disjoint_from_two_hanging_vertices_of_forall_deleteEdgeEnds_no_homeomorphicTheta
      (G := G) hno hmin hxy u v hu hv huv hpq
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hp_out.1, Ne.symm hq_out.1⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hp_out.2.1, Ne.symm hq_out.2.1⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hp_out.2.2.1, Ne.symm hq_out.2.2.1⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hp_out.2.2.2, Ne.symm hq_out.2.2.2⟩

/-- Once no edge is disjoint from a displayed vertex set `S`, every vertex
outside `S` sends all of its neighbours into `S`.  Under the
minimum-degree-three counterexample reduction, it therefore has at least three
neighbours in `S`. -/
theorem three_le_neighborSet_inter_of_min_degree_of_no_edge_disjoint_from_set
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {S : Set V}
    (hno_edge :
      forall {p q : V}, G.Adj p q -> p ∉ S -> q ∉ S -> False)
    {r : V}
    (hrS : r ∉ S) :
    3 <= (G.neighborSet r ∩ S).ncard := by
  classical
  have hsub : G.neighborSet r ⊆ S := by
    intro q hrq
    by_contra hqS
    exact hno_edge hrq hrS hqS
  have hinter : G.neighborSet r ∩ S = G.neighborSet r :=
    Set.inter_eq_left.mpr hsub
  have hcard :
      (G.neighborSet r).ncard = G.degree r := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := r))
  rw [hinter, hcard]
  exact hmin r

/-- A degree-three vertex with two fixed distinct neighbours has at most one
additional neighbour outside that fixed pair. -/
theorem neighbor_unique_outside_pair_of_degree_eq_three
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a x y r s : V}
    (hdeg : G.degree a = 3)
    (hax : G.Adj a x)
    (hay : G.Adj a y)
    (hxy : x ≠ y)
    (hrx : r ≠ x)
    (hry : r ≠ y)
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (har : G.Adj a r)
    (has : G.Adj a s) :
    r = s := by
  classical
  by_contra hrs
  have hfour_sub :
      ({x, y, r, s} : Set V) ⊆ G.neighborSet a := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hax
    · exact hay
    · exact har
    · exact has
  have hfour_card : ({x, y, r, s} : Set V).ncard = 4 := by
    simp [hxy, hrx.symm, hry.symm, hsx.symm, hsy.symm, hrs]
  have hle :
      ({x, y, r, s} : Set V).ncard <= (G.neighborSet a).ncard :=
    Set.ncard_le_ncard hfour_sub
  have hdegree_ncard :
      (G.neighborSet a).ncard = G.degree a := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := a))
  rw [hfour_card, hdegree_ncard, hdeg] at hle
  omega

/-- A degree-at-most-two vertex with one fixed neighbour has at most one
additional neighbour outside that fixed neighbour. -/
theorem neighbor_unique_outside_singleton_of_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a y r s : V}
    (hdeg : G.degree a <= 2)
    (hay : G.Adj a y)
    (hry : r ≠ y)
    (hsy : s ≠ y)
    (har : G.Adj a r)
    (has : G.Adj a s) :
    r = s := by
  classical
  by_contra hrs
  have hthree_sub :
      ({y, r, s} : Set V) ⊆ G.neighborSet a := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hay
    · exact har
    · exact has
  have hthree_card : ({y, r, s} : Set V).ncard = 3 := by
    simp [hry.symm, hsy.symm, hrs]
  have hle :
      ({y, r, s} : Set V).ncard <= (G.neighborSet a).ncard :=
    Set.ncard_le_ncard hthree_sub
  have hdegree_ncard :
      (G.neighborSet a).ncard = G.degree a := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := a))
  rw [hthree_card, hdegree_ncard] at hle
  omega

/-- Deleted-end specialization of
`neighbor_unique_outside_singleton_of_degree_le_two`.  This is the exact
degree-two move used in the final-cycle proof when we inspect `G - b - c`. -/
theorem deleteEdgeEndsGraph_neighbor_unique_outside_singleton_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {p q : V}
    {a y r s : {w : V | w ∉ ({p, q} : Set V)}}
    (hdeg : (deleteEdgeEndsGraph G p q).degree a <= 2)
    (hay : G.Adj (a : V) (y : V))
    (hry : r ≠ y)
    (hsy : s ≠ y)
    (har : G.Adj (a : V) (r : V))
    (has : G.Adj (a : V) (s : V)) :
    r = s := by
  exact
    neighbor_unique_outside_singleton_of_degree_le_two
      (G := deleteEdgeEndsGraph G p q) hdeg
      (by simpa [deleteEdgeEndsGraph] using hay)
      hry hsy
      (by simpa [deleteEdgeEndsGraph] using har)
      (by simpa [deleteEdgeEndsGraph] using has)

/-- Contrapositive form used in the final-cycle proof: in `G - p - q`, a
degree-at-most-two vertex with two known distinct surviving neighbours cannot
also be adjacent to a third surviving neighbour. -/
theorem deleteEdgeEndsGraph_not_adj_third_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {p q : V}
    {a y r s : {w : V | w ∉ ({p, q} : Set V)}}
    (hdeg : (deleteEdgeEndsGraph G p q).degree a <= 2)
    (hay : G.Adj (a : V) (y : V))
    (har : G.Adj (a : V) (r : V))
    (hry : r ≠ y)
    (hsy : s ≠ y)
    (hrs : r ≠ s) :
    ¬ G.Adj (a : V) (s : V) := by
  intro has
  exact hrs
    (deleteEdgeEndsGraph_neighbor_unique_outside_singleton_of_degree_le_two
      (G := G) (p := p) (q := q) hdeg hay hry hsy har has)

/-- In a maximum-degree-two graph, two vertices joined by an edge `a--d` that
both attach to the edge `x--y` must attach to opposite ends.  Extra edges are
irrelevant; this returns one alternating pair of attachments, which is exactly
what the final `K_{3,3}` constructor needs. -/
theorem opposite_attachments_of_degree_le_two_edge_pair
    {V : Type u} [Fintype V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (hdegree : forall z : V, H.degree z <= 2)
    {x y a d : V}
    (hxy : H.Adj x y)
    (had : H.Adj a d)
    (hxa_ne : x ≠ a)
    (hxd_ne : x ≠ d)
    (hya_ne : y ≠ a)
    (hyd_ne : y ≠ d)
    (hattach_a : H.Adj a x ∨ H.Adj a y)
    (hattach_d : H.Adj d x ∨ H.Adj d y) :
    (H.Adj x a ∧ H.Adj y d) ∨ (H.Adj y a ∧ H.Adj x d) := by
  rcases hattach_a with hax | hay
  · rcases hattach_d with hdx | hdy
    · have h_eq : a = d :=
        neighbor_unique_outside_singleton_of_degree_le_two
          (G := H) (a := x) (y := y) (r := a) (s := d)
          (hdegree x) hxy hya_ne.symm hyd_ne.symm hax.symm hdx.symm
      exact False.elim (had.ne h_eq)
    · exact Or.inl ⟨hax.symm, hdy.symm⟩
  · rcases hattach_d with hdx | hdy
    · exact Or.inr ⟨hay.symm, hdx.symm⟩
    · have h_eq : a = d :=
        neighbor_unique_outside_singleton_of_degree_le_two
          (G := H) (a := y) (y := x) (r := a) (s := d)
          (hdegree y) hxy.symm hxa_ne.symm hxd_ne.symm hay.symm hdy.symm
      exact False.elim (had.ne h_eq)

/-- If a degree-two vertex has all neighbours among a two-point set and one
of those neighbours is present, then the other one is present as well. -/
theorem adj_other_of_degree_eq_two_neighborSet_subset_pair
    {V : Type u} [Fintype V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {a x y : V}
    (hdeg : H.degree a = 2)
    (hsub : H.neighborSet a ⊆ ({x, y} : Set V)) :
    H.Adj a y := by
  classical
  by_contra hay
  have hsub_single : H.neighborSet a ⊆ ({x} : Set V) := by
    intro w hw
    have hwxy := hsub hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwxy ⊢
    rcases hwxy with hwx | hwy
    · exact hwx
    · exact False.elim (hay (by simpa [hwy] using hw))
  have hcard_le :
      (H.neighborSet a).ncard <= ({x} : Set V).ncard :=
    Set.ncard_le_ncard hsub_single
  have hdegree_ncard :
      (H.neighborSet a).ncard = H.degree a := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := H) (v := a))
  rw [hdegree_ncard, hdeg] at hcard_le
  simp at hcard_le


end FourColor

end Schematic.Math.GraphTheory
