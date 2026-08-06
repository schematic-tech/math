import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.HangingVertices

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Source dichotomy after the hanging-cycle reduction in Makarychev Lemma 3:
either the chosen hanging cycle spans `G - x - y`, or there is a unique vertex
outside the cycle, and that vertex is a leaf attached to the cut vertex `v`.
This combines the no-outside-edge theta argument with Lemma 2's uniqueness of
hanging vertices. -/
theorem deleteEdgeEndsGraph_hanging_cycle_spans_or_unique_cut_leaf_not_planar
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
    (forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support) ∨
      Exists fun p : {w : V | w ∉ ({x, y} : Set V)} =>
        p ∉ C.support ∧
          (deleteEdgeEndsGraph G x y).neighborSet p = {v} ∧
            forall t : {w : V | w ∉ ({x, y} : Set V)},
              t ∉ C.support -> t = p := by
  classical
  by_cases hexists :
      Exists fun p : {w : V | w ∉ ({x, y} : Set V)} => p ∉ C.support
  · rcases hexists with ⟨p, hp⟩
    have hsub :
        {t : {w : V | w ∉ ({x, y} : Set V)} | t ∉ C.support}.Subsingleton :=
      deleteEdgeEndsGraph_outside_cycle_subsingleton_of_hanging_cycle_not_planar_min_degree
        (G := G) hnonplanar hno hmin hxy C hC hv hattach hcontact
    right
    refine ⟨p, hp, ?_, ?_⟩
    · exact
        deleteEdgeEndsGraph_neighborSet_eq_singleton_cutVertex_of_outside_hanging_cycle_min_degree
          (G := G) hno hmin hxy C hC hv hattach hcontact hp
    · intro t ht
      exact hsub ht hp
  · left
    intro t
    by_contra ht
    exact hexists ⟨t, ht⟩

/-- Source-attached-cycle dichotomy without assuming a global contact
predicate.  In the non-planar minimal-source setting, a cycle satisfying the
non-cut attachment condition either spans `G - x - y`, or there is a unique
off-cycle vertex and it is a leaf of the deleted-end graph.  The proof uses
only the no-outside-edge obstruction, pointwise contact uniqueness, and
Makarychev Lemma 2's uniqueness of deleted-end hanging vertices. -/
theorem deleteEdgeEndsGraph_cycle_spans_or_unique_leaf_of_noncut_attach_not_planar
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
          G.Adj (t : V) x ∨ G.Adj (t : V) y) :
    (forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support) ∨
      Exists fun p : {w : V | w ∉ ({x, y} : Set V)} =>
        p ∉ C.support ∧
          (deleteEdgeEndsGraph G x y).degree p = 1 ∧
            forall t : {w : V | w ∉ ({x, y} : Set V)},
              t ∉ C.support -> t = p := by
  classical
  have hleaf_of_outside :
      forall p : {w : V | w ∉ ({x, y} : Set V)},
        p ∉ C.support -> (deleteEdgeEndsGraph G x y).degree p = 1 := by
    intro p hp_outside
    have hp_pos :
        0 < (deleteEdgeEndsGraph G x y).degree p :=
      deleteEdgeEndsGraph_degree_pos_of_min_degree_three
        (G := G) (x := x) (y := y) hmin p
    rcases ((deleteEdgeEndsGraph G x y).degree_pos_iff_exists_adj p).mp
        hp_pos with
      ⟨w, hpw⟩
    by_cases hwC : w ∈ C.support
    · exact
        deleteEdgeEndsGraph_degree_eq_one_of_outside_cycle_contact
          (G := G) hno hxy C hC hv hattach hp_outside hwC hpw
    · exact False.elim
        (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
          (G := G) hno hxy C hC hv hattach hpw hp_outside hwC)
  by_cases hexists :
      Exists fun p : {w : V | w ∉ ({x, y} : Set V)} => p ∉ C.support
  · right
    rcases hexists with ⟨p, hp⟩
    have hp_degree : (deleteEdgeEndsGraph G x y).degree p = 1 :=
      hleaf_of_outside p hp
    refine ⟨p, hp, hp_degree, ?_⟩
    intro t ht
    have ht_degree : (deleteEdgeEndsGraph G x y).degree t = 1 :=
      hleaf_of_outside t ht
    exact
      deleteEdgeEndsGraph_hanging_vertex_subsingleton_of_not_planar
        (G := G) hnonplanar hno hmin hxy
        (u := t) (v := p)
        (by omega) (by omega)
  · left
    intro t
    by_contra ht
    exact hexists ⟨t, ht⟩

/-- Skopenkov condition-(1) endpoint for a hanging cycle.  Once the no-theta
argument has forced every outside edge to meet the hanging cycle only at the
displayed contact vertex, any outside vertex is a leaf.  Therefore, if the
deleted-end graph has minimum degree at least two, the hanging cycle spans.
This is the formal source line: "Since by (1) the graph `K - x - y` does not
contain hanging vertices, this graph coincides with `C`." -/
theorem deleteEdgeEndsGraph_hanging_cycle_spans_of_degree_ge_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
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
    (hdegree_ge :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree t) :
    forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support := by
  intro t
  by_contra ht
  have hpos :
      forall s : {w : V | w ∉ ({x, y} : Set V)},
        0 < (deleteEdgeEndsGraph G x y).degree s := by
    intro s
    have hs := hdegree_ge s
    omega
  have htdeg :
      (deleteEdgeEndsGraph G x y).degree t = 1 :=
    deleteEdgeEndsGraph_degree_eq_one_of_outside_hanging_cycle
      (G := G) hno hxy C hC hv hattach hcontact hpos ht
  have htge := hdegree_ge t
  omega

/-- Source-derived spanning conclusion for a hanging cycle.  If every outside
vertex is adjacent to the displayed cut vertex `v`, then the pointwise leaf
theorem makes any outside vertex degree one; a minimum deleted degree of two
therefore forces the cycle to span. -/
theorem deleteEdgeEndsGraph_hanging_cycle_spans_of_degree_ge_two_adj_contact
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
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
    (hadj_contact :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∉ C.support -> (deleteEdgeEndsGraph G x y).Adj t v)
    (hdegree_ge :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree t) :
    forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support := by
  intro t
  by_contra ht
  have htdeg :
      (deleteEdgeEndsGraph G x y).degree t = 1 :=
    deleteEdgeEndsGraph_degree_eq_one_of_outside_cycle_adj_contact
      (G := G) hno hxy C hC hv hattach ht (hadj_contact t ht)
  have htge := hdegree_ge t
  omega

/-- Vertex bookkeeping for the unique cut-leaf branch: every original vertex
is one of the deleted endpoints, the unique outside leaf, or the image of a
vertex on the hanging cycle. -/
theorem vertex_eq_deleted_endpoint_or_leaf_or_cycle_support_of_unique_cut_leaf
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hunique :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∉ C.support -> t = p)
    (z : V) :
    z = x ∨ z = y ∨ z = (p : V) ∨
      Exists fun t : {w : V | w ∉ ({x, y} : Set V)} =>
        t ∈ C.support ∧ (t : V) = z := by
  classical
  by_cases hzxy : z ∈ ({x, y} : Set V)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzxy
    rcases hzxy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · let zD : {w : V | w ∉ ({x, y} : Set V)} := ⟨z, hzxy⟩
    by_cases hzC : zD ∈ C.support
    · exact Or.inr (Or.inr (Or.inr ⟨zD, hzC, rfl⟩))
    · have hzD_eq : zD = p := hunique zD hzC
      exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val hzD_eq)))

/-- Cardinal bookkeeping for the unique cut-leaf branch.  The whole original
graph is covered by the two deleted endpoints, the outside leaf, and the
distinct support vertices of the hanging cycle. -/
theorem card_le_three_add_cycle_support_card_of_unique_cut_leaf
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hunique :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∉ C.support -> t = p) :
    Fintype.card V <= 3 + C.support.toFinset.card := by
  classical
  let D : Set {w : V | w ∉ ({x, y} : Set V)} := {t | t ∈ C.support}
  let A : Set V := ({x, y, (p : V)} : Set V)
  let B : Set V := Subtype.val '' D
  let S : Set V := A ∪ B
  have hsub : (Set.univ : Set V) ⊆ S := by
    intro z _hz
    rcases
      vertex_eq_deleted_endpoint_or_leaf_or_cycle_support_of_unique_cut_leaf
        (G := G) (x := x) (y := y) C hunique z with
      hzx | hzy | hzp | hCz
    · exact Or.inl (by simp [A, hzx])
    · exact Or.inl (by simp [A, hzy])
    · exact Or.inl (by simp [A, hzp])
    · rcases hCz with ⟨t, htC, htz⟩
      exact Or.inr ⟨t, htC, htz⟩
  have huniv_le : (Set.univ : Set V).ncard <= S.ncard :=
    Set.ncard_le_ncard hsub
  have hS_le : S.ncard <= A.ncard + B.ncard := by
    simpa [S] using Set.ncard_union_le A B
  have hA_le : A.ncard <= 3 := by
    have hpair : ({y, (p : V)} : Set V).ncard <= 2 := by
      have hsingle : ({(p : V)} : Set V).ncard = 1 := by
        simp
      have h := Set.ncard_insert_le y ({(p : V)} : Set V)
      omega
    have htriple : ({x, y, (p : V)} : Set V).ncard <= 3 := by
      have h := Set.ncard_insert_le x ({y, (p : V)} : Set V)
      omega
    simpa [A] using htriple
  have hD_card : D.ncard = C.support.toFinset.card := by
    have hD_eq : D = (C.support.toFinset : Set {w : V | w ∉ ({x, y} : Set V)}) := by
      ext t
      change (t ∈ C.support) ↔ t ∈ C.support.toFinset
      rw [List.mem_toFinset]
    rw [hD_eq, Set.ncard_coe_finset]
  have hB_card : B.ncard = D.ncard := by
    exact Set.ncard_image_of_injective D Subtype.val_injective
  have huniv_card : (Set.univ : Set V).ncard = Fintype.card V := by
    simp [Set.ncard_univ, Nat.card_eq_fintype_card]
  omega

/-- Length version of the unique cut-leaf cardinal bound.  Since a simple
cycle is a nontrivial closed walk, its distinct support vertices are bounded
by its length. -/
theorem card_le_three_add_cycle_length_of_unique_cut_leaf
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hunique :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∉ C.support -> t = p) :
    Fintype.card V <= 3 + C.length := by
  have hcard :=
    card_le_three_add_cycle_support_card_of_unique_cut_leaf
      (G := G) (x := x) (y := y) C hunique
  have hsupport :
      C.support.toFinset.card <= C.length :=
    Walk.support_toFinset_card_le_length_of_closed C hC.not_nil
  omega

/-- If the hanging cycle in the unique cut-leaf branch is a triangle, then
the original graph has at most six vertices, exactly the finite size of the
source triangular-prism endpoint. -/
theorem card_le_six_of_unique_cut_leaf_cycle_length_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hlen : C.length = 3)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hunique :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∉ C.support -> t = p) :
    Fintype.card V <= 6 := by
  have hcard :=
    card_le_three_add_cycle_length_of_unique_cut_leaf
      (G := G) (x := x) (y := y) C hC hunique
  omega

/-- In the unique cut-leaf branch, a non-cut vertex of the hanging cycle has
no original neighbours except the two deleted endpoints and vertices of the
hanging cycle itself.  The only possible outside vertex is the leaf `p`, but
`p` is adjacent only to `x`, `y`, and the cut vertex `v`. -/
theorem neighbor_eq_deleted_endpoint_or_cycle_support_of_noncut_cycle_vertex_unique_cut_leaf
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
        s ∉ C.support -> s = p)
    {t : {w : V | w ∉ ({x, y} : Set V)}}
    (htv : t ≠ v)
    {z : V}
    (htz : G.Adj (t : V) z) :
    z = x ∨ z = y ∨
      Exists fun c : {w : V | w ∉ ({x, y} : Set V)} =>
        c ∈ C.support ∧ (c : V) = z := by
  classical
  rcases
    vertex_eq_deleted_endpoint_or_leaf_or_cycle_support_of_unique_cut_leaf
      (G := G) (x := x) (y := y) C hunique z with
    hzx | hzy | hzp | hzC
  · exact Or.inl hzx
  · exact Or.inr (Or.inl hzy)
  · have hN :
        G.neighborSet (p : V) = ({x, y, (v : V)} : Set V) :=
      deleteEdgeEndsGraph_outside_hanging_cycle_original_neighborSet_eq
        (G := G) hno hmin hxy C hC hv hattach hcontact hp_out
    have hpt : G.Adj (p : V) (t : V) := by
      simpa [hzp] using htz.symm
    have ht_neighbor : (t : V) ∈ G.neighborSet (p : V) := hpt
    have ht_mem : (t : V) ∈ ({x, y, (v : V)} : Set V) := by
      rwa [hN] at ht_neighbor
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht_mem
    rcases ht_mem with htx | hty | htv_val
    · exact False.elim (t.property (by simp [htx]))
    · exact False.elim (t.property (by simp [hty]))
    · exact False.elim (htv (Subtype.ext htv_val))
  · exact Or.inr (Or.inr hzC)

/-- Triangle endpoint constraint in the unique cut-leaf branch.  If the
hanging cycle is already rotated so that the cut vertex is its base point,
then the first non-cut triangle vertex cannot be adjacent to both deleted
endpoints.  Otherwise the second non-cut triangle vertex attaches to one
endpoint, and `G - p - v` contains a direct-edge theta. -/
theorem unique_cut_leaf_triangle_getVert_one_not_adj_both_endpoints
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
    (hp_out : p ∉ C.support) :
    ¬ (G.Adj (C.getVert 1 : V) x ∧ G.Adj (C.getVert 1 : V) y) := by
  classical
  intro ha_both
  let a : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 1
  let b : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 2
  have haC : a ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨1, rfl, by omega⟩
  have hbC : b ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨2, rfl, by omega⟩
  have ha_ne_v : a ≠ v := by
    intro hav
    have hendpoint :
        1 = 0 ∨ 1 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 1) (by omega)).mp (by
        simpa [a] using hav)
    omega
  have hb_ne_v : b ≠ v := by
    intro hbv
    have hendpoint :
        2 = 0 ∨ 2 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 2) (by omega)).mp (by
        simpa [b] using hbv)
    omega
  have hab_ne : a ≠ b := by
    intro hab
    have hidx :
        1 = 2 :=
      hC.getVert_injOn
        (by
          simp only [Set.mem_setOf_eq]
          omega)
        (by
          simp only [Set.mem_setOf_eq]
          omega)
        (by simpa [a, b] using hab)
    omega
  have habD : (deleteEdgeEndsGraph G x y).Adj a b := by
    simpa [a, b] using C.adj_getVert_succ (i := 1) (by omega)
  have habG : G.Adj (a : V) (b : V) := by
    simpa [deleteEdgeEndsGraph] using habD
  have hb_attach : G.Adj (b : V) x ∨ G.Adj (b : V) y :=
    hattach b hbC hb_ne_v
  have hpv_delete :
      (deleteEdgeEndsGraph G x y).Adj p v :=
    deleteEdgeEndsGraph_adj_cutVertex_of_outside_hanging_cycle_min_degree
      (G := G) hno hmin hxy C hC C.start_mem_support hattach hcontact hp_out
  have hpv : G.Adj (p : V) (v : V) := by
    simpa [deleteEdgeEndsGraph] using hpv_delete
  have hx_avoid : x ∉ ({(p : V), (v : V)} : Set V) := by
    intro hxmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem
    rcases hxmem with hxp | hxv
    · exact p.property (by simp [hxp])
    · exact v.property (by simp [hxv])
  have hy_avoid : y ∉ ({(p : V), (v : V)} : Set V) := by
    intro hymem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hymem
    rcases hymem with hyp | hyv
    · exact p.property (by simp [hyp])
    · exact v.property (by simp [hyv])
  have ha_avoid : (a : V) ∉ ({(p : V), (v : V)} : Set V) := by
    intro hamem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hamem
    rcases hamem with hap | hav
    · have hap_sub : a = p := Subtype.ext hap
      exact hp_out (by simpa [hap_sub] using haC)
    · exact ha_ne_v (Subtype.ext hav)
  have hb_avoid : (b : V) ∉ ({(p : V), (v : V)} : Set V) := by
    intro hbmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbmem
    rcases hbmem with hbp | hbv
    · have hbp_sub : b = p := Subtype.ext hbp
      exact hp_out (by simpa [hbp_sub] using hbC)
    · exact hb_ne_v (Subtype.ext hbv)
  have hy_ne_b : y ≠ (b : V) := by
    intro hyb
    exact b.property (by simp [hyb])
  have hx_ne_b : x ≠ (b : V) := by
    intro hxb
    exact b.property (by simp [hxb])
  rcases hb_attach with hbx | hby
  · exact
      hno hpv
        (containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_and_two_common_neighbors
          (G := G)
          (x := x) (y := (a : V)) (u := y) (v := (b : V))
          (p := (p : V)) (q := (v : V))
          hx_avoid ha_avoid hy_avoid hb_avoid
          ha_both.1.symm hxy ha_both.2 hbx.symm habG hy_ne_b)
  · exact
      hno hpv
        (containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_and_two_common_neighbors
          (G := G)
          (x := y) (y := (a : V)) (u := x) (v := (b : V))
          (p := (p : V)) (q := (v : V))
          hy_avoid ha_avoid hx_avoid hb_avoid
          ha_both.2.symm hxy.symm ha_both.1 hby.symm habG hx_ne_b)

/-- Symmetric form of
`unique_cut_leaf_triangle_getVert_one_not_adj_both_endpoints` for the second
non-cut triangle vertex, obtained by reversing the cycle. -/
theorem unique_cut_leaf_triangle_getVert_two_not_adj_both_endpoints
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
    (hp_out : p ∉ C.support) :
    ¬ (G.Adj (C.getVert 2 : V) x ∧ G.Adj (C.getVert 2 : V) y) := by
  classical
  have hattach_rev :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.reverse.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y := by
    intro t ht htne
    have htC : t ∈ C.support := by
      rw [SimpleGraph.Walk.support_reverse] at ht
      exact List.mem_reverse.mp ht
    exact hattach t htC htne
  have hcontact_rev :
      forall {t c : {w : V | w ∉ ({x, y} : Set V)}},
        t ∉ C.reverse.support -> c ∈ C.reverse.support ->
          (deleteEdgeEndsGraph G x y).Adj t c -> c = v := by
    intro t c ht_out hc_rev htc
    have ht_out_C : t ∉ C.support := by
      intro htC
      apply ht_out
      rw [SimpleGraph.Walk.support_reverse]
      exact List.mem_reverse.mpr htC
    have hcC : c ∈ C.support := by
      rw [SimpleGraph.Walk.support_reverse] at hc_rev
      exact List.mem_reverse.mp hc_rev
    exact hcontact ht_out_C hcC htc
  have hp_out_rev : p ∉ C.reverse.support := by
    intro hp_rev
    apply hp_out
    rw [SimpleGraph.Walk.support_reverse] at hp_rev
    exact List.mem_reverse.mp hp_rev
  have hrev_not :
      ¬ (G.Adj (C.reverse.getVert 1 : V) x ∧
          G.Adj (C.reverse.getVert 1 : V) y) :=
    unique_cut_leaf_triangle_getVert_one_not_adj_both_endpoints
      (G := G) hno hmin hxy C.reverse hC.reverse
      (by simpa [SimpleGraph.Walk.length_reverse] using hlen)
      hattach_rev hcontact_rev (p := p) hp_out_rev
  have hpen :
      (C.penultimate : V) = (C.getVert 2 : V) := by
    change (C.getVert (C.length - 1) : V) = (C.getVert 2 : V)
    have hidx : C.length - 1 = 2 := by omega
    rw [hidx]
  intro hboth
  have hboth_pen :
      G.Adj (C.penultimate : V) x ∧ G.Adj (C.penultimate : V) y := by
    rw [hpen]
    exact hboth
  exact hrev_not (by simpa using hboth_pen)

/-- In the unique cut-leaf triangle branch, the first non-cut triangle vertex
attaches to exactly one deleted endpoint. -/
theorem unique_cut_leaf_triangle_getVert_one_adj_exactly_one_endpoint
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
    (hp_out : p ∉ C.support) :
    (G.Adj (C.getVert 1 : V) x ∧ ¬ G.Adj (C.getVert 1 : V) y) ∨
      (G.Adj (C.getVert 1 : V) y ∧ ¬ G.Adj (C.getVert 1 : V) x) := by
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
  have hattach1 :
      G.Adj (C.getVert 1 : V) x ∨ G.Adj (C.getVert 1 : V) y :=
    hattach (C.getVert 1) h1C h1_ne_v
  have hnot_both :
      ¬ (G.Adj (C.getVert 1 : V) x ∧ G.Adj (C.getVert 1 : V) y) :=
    unique_cut_leaf_triangle_getVert_one_not_adj_both_endpoints
      (G := G) hno hmin hxy C hC hlen hattach hcontact (p := p) hp_out
  rcases hattach1 with h1x | h1y
  · by_cases h1y' : G.Adj (C.getVert 1 : V) y
    · exact False.elim (hnot_both ⟨h1x, h1y'⟩)
    · exact Or.inl ⟨h1x, h1y'⟩
  · by_cases h1x' : G.Adj (C.getVert 1 : V) x
    · exact False.elim (hnot_both ⟨h1x', h1y⟩)
    · exact Or.inr ⟨h1y, h1x'⟩

/-- In the unique cut-leaf triangle branch, the second non-cut triangle vertex
attaches to exactly one deleted endpoint. -/
theorem unique_cut_leaf_triangle_getVert_two_adj_exactly_one_endpoint
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
    (hp_out : p ∉ C.support) :
    (G.Adj (C.getVert 2 : V) x ∧ ¬ G.Adj (C.getVert 2 : V) y) ∨
      (G.Adj (C.getVert 2 : V) y ∧ ¬ G.Adj (C.getVert 2 : V) x) := by
  classical
  have h2C : C.getVert 2 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨2, rfl, by omega⟩
  have h2_ne_v : C.getVert 2 ≠ v := by
    intro h2v
    have hendpoint :
        2 = 0 ∨ 2 = C.length := by
      exact (hC.getVert_endpoint_iff (i := 2) (by omega)).mp h2v
    omega
  have hattach2 :
      G.Adj (C.getVert 2 : V) x ∨ G.Adj (C.getVert 2 : V) y :=
    hattach (C.getVert 2) h2C h2_ne_v
  have hnot_both :
      ¬ (G.Adj (C.getVert 2 : V) x ∧ G.Adj (C.getVert 2 : V) y) :=
    unique_cut_leaf_triangle_getVert_two_not_adj_both_endpoints
      (G := G) hno hmin hxy C hC hlen hattach hcontact (p := p) hp_out
  rcases hattach2 with h2x | h2y
  · by_cases h2y' : G.Adj (C.getVert 2 : V) y
    · exact False.elim (hnot_both ⟨h2x, h2y'⟩)
    · exact Or.inl ⟨h2x, h2y'⟩
  · by_cases h2x' : G.Adj (C.getVert 2 : V) x
    · exact False.elim (hnot_both ⟨h2x', h2y⟩)
    · exact Or.inr ⟨h2y, h2x'⟩

/-- In the unique cut-leaf triangle branch, the first non-cut triangle vertex
has original degree exactly three.  Its neighbours are its two cycle neighbours
and the unique deleted endpoint to which it attaches. -/
theorem unique_cut_leaf_triangle_getVert_one_degree_eq_three
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
    G.degree (C.getVert 1 : V) = 3 := by
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
  have hdegree_upper_x
      (h1noty : ¬ G.Adj (C.getVert 1 : V) y) :
      G.degree (C.getVert 1 : V) <= 3 := by
    refine degree_le_three_of_neighborSet_subset_triple (G := G)
      (u := (C.getVert 1 : V)) (a := x) (b := (v : V))
      (c := (C.getVert 2 : V)) ?_
    intro z hz
    rcases
        neighbor_eq_deleted_endpoint_or_cycle_support_of_noncut_cycle_vertex_unique_cut_leaf
          (G := G) hno hmin hxy C hC C.start_mem_support hattach hcontact
          hp_out hunique h1_ne_v hz with
      hzx | hzy | hzC
    · simp [hzx]
    · exact False.elim (h1noty (by simpa [hzy] using hz))
    · rcases hzC with ⟨c, hcC, hcz⟩
      rcases Walk.support_subset_getVert012_of_length_eq_three C hlen hcC with
        hc0 | hc1 | hc2
      · have hzv : z = (v : V) := by
          rw [← hcz]
          have hc0_val : (c : V) = (C.getVert 0 : V) :=
            congrArg Subtype.val hc0
          simpa [SimpleGraph.Walk.getVert_zero] using hc0_val
        simp [hzv]
      · have hza : z = (C.getVert 1 : V) := by
          rw [← hcz]
          exact congrArg Subtype.val hc1
        exact False.elim (hz.ne hza.symm)
      · have hzb : z = (C.getVert 2 : V) := by
          rw [← hcz]
          exact congrArg Subtype.val hc2
        simp [hzb]
  have hdegree_upper_y
      (h1notx : ¬ G.Adj (C.getVert 1 : V) x) :
      G.degree (C.getVert 1 : V) <= 3 := by
    refine degree_le_three_of_neighborSet_subset_triple (G := G)
      (u := (C.getVert 1 : V)) (a := y) (b := (v : V))
      (c := (C.getVert 2 : V)) ?_
    intro z hz
    rcases
        neighbor_eq_deleted_endpoint_or_cycle_support_of_noncut_cycle_vertex_unique_cut_leaf
          (G := G) hno hmin hxy C hC C.start_mem_support hattach hcontact
          hp_out hunique h1_ne_v hz with
      hzx | hzy | hzC
    · exact False.elim (h1notx (by simpa [hzx] using hz))
    · simp [hzy]
    · rcases hzC with ⟨c, hcC, hcz⟩
      rcases Walk.support_subset_getVert012_of_length_eq_three C hlen hcC with
        hc0 | hc1 | hc2
      · have hzv : z = (v : V) := by
          rw [← hcz]
          have hc0_val : (c : V) = (C.getVert 0 : V) :=
            congrArg Subtype.val hc0
          simpa [SimpleGraph.Walk.getVert_zero] using hc0_val
        simp [hzv]
      · have hza : z = (C.getVert 1 : V) := by
          rw [← hcz]
          exact congrArg Subtype.val hc1
        exact False.elim (hz.ne hza.symm)
      · have hzb : z = (C.getVert 2 : V) := by
          rw [← hcz]
          exact congrArg Subtype.val hc2
        simp [hzb]
  have hge : 3 <= G.degree (C.getVert 1 : V) := hmin (C.getVert 1 : V)
  rcases
      unique_cut_leaf_triangle_getVert_one_adj_exactly_one_endpoint
        (G := G) hno hmin hxy C hC hlen hattach hcontact (p := p) hp_out with
    hleft | hright
  · have hle := hdegree_upper_x hleft.2
    omega
  · have hle := hdegree_upper_y hright.2
    omega


end FourColor

end Schematic.Math.GraphTheory
