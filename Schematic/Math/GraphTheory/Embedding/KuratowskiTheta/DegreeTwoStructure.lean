import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.HangingCycleObstructions
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- A finite graph of maximum degree two, with no isolated vertices and at most
one vertex of degree at most one, is everywhere degree two.  The proof is the
handshaking parity argument: a single degree-one vertex would force another
odd-degree vertex, and under the degree bounds that vertex is also degree one. -/
theorem degree_eq_two_of_degree_le_two_degree_pos_low_subsingleton
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmax : forall v : V, G.degree v <= 2)
    (hpos : forall v : V, 0 < G.degree v)
    (hlow :
      forall {u v : V}, G.degree u <= 1 -> G.degree v <= 1 -> u = v) :
    forall v : V, G.degree v = 2 := by
  classical
  intro v
  have hvpos : 0 < G.degree v := hpos v
  have hvmax : G.degree v <= 2 := hmax v
  by_contra hvne
  have hvdeg : G.degree v = 1 := by omega
  have hvodd : Odd (G.degree v) := by
    rw [hvdeg]
    exact odd_one
  rcases G.exists_ne_odd_degree_of_exists_odd_degree v hvodd with
    ⟨w, hwne, hwodd⟩
  have hwdeg : G.degree w = 1 := by
    rcases hwodd with ⟨k, hk⟩
    have hwpos : 0 < G.degree w := hpos w
    have hwmax : G.degree w <= 2 := hmax w
    omega
  have hvw : v = w := hlow (by omega) (by omega)
  exact hwne hvw.symm

/-- A graph whose every vertex has degree two is an `IsCycles` graph in
mathlib's componentwise-cycle sense. -/
theorem isCycles_of_degree_eq_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall v : V, G.degree v = 2) :
    G.IsCycles := by
  classical
  intro v _hv_nonempty
  have hcard :
      (G.neighborSet v).ncard = G.degree v := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v))
  rw [hcard, hdegree v]

/-- A spanning chordless cycle is exactly two-regular.  This is the local
degree-count endpoint needed after the source block/cactus proof has shown
that the deleted graph coincides with a hanging cycle and the no-theta
hypothesis has ruled out chords. -/
theorem degree_eq_two_of_spanning_chordless_cycle
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hchordless :
      forall {a b : V}, a ∈ C.support -> b ∈ C.support ->
        G.Adj a b -> C.toSubgraph.Adj a b) :
    forall v : V, G.degree v = 2 := by
  classical
  intro v
  have hvC : v ∈ C.support := by
    exact C.mem_verts_toSubgraph.mp (by
      rw [hspanning]
      exact Set.mem_univ v)
  have hneighbor :
      G.neighborSet v = C.toSubgraph.neighborSet v := by
    ext w
    constructor
    · intro hvw
      have hwC : w ∈ C.support := by
        exact C.mem_verts_toSubgraph.mp (by
          rw [hspanning]
          exact Set.mem_univ w)
      exact hchordless hvC hwC hvw
    · intro hvw
      exact C.toSubgraph.adj_sub hvw
  have hG_card :
      (G.neighborSet v).ncard = G.degree v := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v))
  have hcycle_card :
      (C.toSubgraph.neighborSet v).ncard = 2 :=
    hC.ncard_neighborSet_toSubgraph_eq_two hvC
  rw [← hG_card, hneighbor]
  exact hcycle_card

/-- Variant of `degree_eq_two_of_spanning_chordless_cycle` using mathlib's
`Walk.IsChordless` predicate directly. -/
theorem degree_eq_two_of_spanning_isChordless_cycle
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hchordless : C.IsChordless) :
    forall v : V, G.degree v = 2 :=
  degree_eq_two_of_spanning_chordless_cycle C hC hspanning
    (by
      intro a b ha hb hab
      exact Walk.IsChordless.toSubgraph_adj_of_adj hchordless ha hb hab)

/-- Under the source no-theta hypothesis, a simple cycle is chordless.  A chord
would be the suppressed direct branch of an `EdgeThetaGraph` subdivision, with
the two cycle arcs as the other two branches. -/
theorem isChordless_of_isCycle_no_homeomorphicTheta
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hno : Not (ContainsHomeomorphicTheta G)) :
    C.IsChordless := by
  classical
  by_contra hnot
  rcases
      (Walk.not_isChordless_iff_exists_adj_not_toSubgraph_adj
        (G := G) C).mp hnot with
    ⟨a, ha, b, hb, hab, hnot_adj⟩
  exact hno
    (ContainsHomeomorphicTheta.of_edgeSubdivision
      (ContainsEdgeThetaSubdivision.of_cycle_chord
        C hC ha hb hab hnot_adj))

/-- Degree bound on an end-cycle from the block/cactus picture.  If every
neighbour of a cycle vertex `t ≠ v` stays on the displayed cycle, then
theta-free chordlessness makes the full neighbour set of `t` equal to a
sub-neighbour-set of the cycle, hence has size at most two. -/
theorem degree_le_two_of_cycle_no_external_contact_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hno : Not (ContainsHomeomorphicTheta G))
    {v t : V}
    (ht : t ∈ C.support)
    (htv : t ≠ v)
    (hcontact :
      forall {a b : V}, a ∈ C.support -> a ≠ v ->
        G.Adj a b -> b ∈ C.support) :
    G.degree t <= 2 := by
  classical
  have hchordless : C.IsChordless :=
    isChordless_of_isCycle_no_homeomorphicTheta C hC hno
  have hneighbor_sub :
      G.neighborSet t ⊆ C.toSubgraph.neighborSet t := by
    intro w htw
    have hwC : w ∈ C.support := hcontact ht htv htw
    exact Walk.IsChordless.toSubgraph_adj_of_adj hchordless ht hwC htw
  have hle :
      (G.neighborSet t).ncard <= (C.toSubgraph.neighborSet t).ncard :=
    Set.ncard_le_ncard hneighbor_sub
  have hG_card :
      (G.neighborSet t).ncard = G.degree t := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  have hC_card :
      (C.toSubgraph.neighborSet t).ncard = 2 :=
    hC.ncard_neighborSet_toSubgraph_eq_two ht
  omega

/-- General outside-component contact uniqueness for a theta-free cycle.  If
two outside neighbours of cycle vertices lie in the same component of the
graph induced outside the cycle, then those cycle vertices are equal; otherwise
the outside path and the two cycle arcs give a homeomorphic theta. -/
theorem cycle_contacts_eq_of_external_reachable_no_homeomorphicTheta
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b u v : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hno : Not (ContainsHomeomorphicTheta G))
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hu_outside : u ∉ C.support)
    (hv_outside : v ∉ C.support)
    (hreach :
      (G.induce {z : V | z ∉ C.support}).Reachable
        (⟨u, hu_outside⟩ : {z : V | z ∉ C.support})
        (⟨v, hv_outside⟩ : {z : V | z ∉ C.support}))
    (hau : G.Adj a u)
    (hbv : G.Adj b v) :
    a = b := by
  classical
  by_contra hab_ne
  rcases Walk.IsCycle.exists_two_support_ne (G := G) C hC ha with
    ⟨z₁, z₂, hz₁, hz₂, hz₁_ne_a, hz₂_ne_a, hz₁z₂⟩
  have htheta : ContainsEdgeThetaSubdivision G := by
    rcases
        reachable_induce_exists_chordless_path_support_subset
          (G := G) (A := {z : V | z ∉ C.support})
          hu_outside hv_outside hreach with
      ⟨q, hq_path, _hq_chordless, hq_support⟩
    by_cases hz₁b : z₁ = b
    · have hz₂_ne_b : b ≠ z₂ := by
        intro hbz₂
        exact hz₁z₂ (by rw [hz₁b, hbz₂])
      exact
        ContainsEdgeThetaSubdivision.of_cycle_external_connector
          (G := G) C hC ha hb hz₂ hab_ne hz₂_ne_a.symm hz₂_ne_b
          hau q hq_path
          (by
            intro t ht
            exact hq_support t ht)
          hbv
    · have hz₁_ne_b : b ≠ z₁ := by
        intro hbz₁
        exact hz₁b hbz₁.symm
      exact
        ContainsEdgeThetaSubdivision.of_cycle_external_connector
          (G := G) C hC ha hb hz₁ hab_ne hz₁_ne_a.symm hz₁_ne_b
          hau q hq_path
          (by
            intro t ht
            exact hq_support t ht)
          hbv
  exact hno (ContainsHomeomorphicTheta.of_edgeSubdivision htheta)

/-- Boundary bound for one outside component of a theta-free cycle.  A
connected component of the graph induced outside `C` can contact `C` in at
most one vertex. -/
theorem cycle_external_component_boundary_ncard_le_one_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hno : Not (ContainsHomeomorphicTheta G))
    (K : (G.induce {z : V | z ∉ C.support}).ConnectedComponent) :
    ({v : V | v ∈ C.support ∧
      Exists fun u : V =>
        u ∈ induceComponentSupport
          (G := G) (A := {z : V | z ∉ C.support}) K ∧ G.Adj u v}).ncard <= 1 := by
  classical
  rw [Set.ncard_le_one_iff]
  intro a b ha hb
  rcases ha with ⟨haC, u, huK, hua⟩
  rcases hb with ⟨hbC, w, hwK, hwb⟩
  rcases huK with ⟨hu_outside, huKsupp⟩
  rcases hwK with ⟨hw_outside, hwKsupp⟩
  let H : SimpleGraph {z : V | z ∉ C.support} :=
    G.induce {z : V | z ∉ C.support}
  let uH : {z : V | z ∉ C.support} := ⟨u, hu_outside⟩
  let wH : {z : V | z ∉ C.support} := ⟨w, hw_outside⟩
  have hu_eq : H.connectedComponentMk uH = K := by
    simpa [H, uH] using (SimpleGraph.ConnectedComponent.mem_supp_iff K uH).mp huKsupp
  have hw_eq : H.connectedComponentMk wH = K := by
    simpa [H, wH] using (SimpleGraph.ConnectedComponent.mem_supp_iff K wH).mp hwKsupp
  have hreach : H.Reachable uH wH :=
    SimpleGraph.ConnectedComponent.exact (hu_eq.trans hw_eq.symm)
  exact
    cycle_contacts_eq_of_external_reachable_no_homeomorphicTheta
      (G := G) C hC hno haC hbC hu_outside hw_outside
      (by simpa [H, uH, wH] using hreach) hua.symm hwb.symm

/-- Two-connected theta-free graphs have no vertices outside a displayed
cycle.  This is the formal block theorem needed by the cactus step: in a
2-connected block, the no-theta hypothesis forces the block to be exactly its
cycle. -/
theorem cycle_support_univ_of_twoConnected_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsTwoConnected G)
    {r : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hno : Not (ContainsHomeomorphicTheta G)) :
    forall v : V, v ∈ C.support := by
  classical
  intro x
  by_contra hx
  let outside : Set V := {z : V | z ∉ C.support}
  let K : (G.induce outside).ConnectedComponent :=
    (G.induce outside).connectedComponentMk ⟨x, hx⟩
  have hA_nonempty :
      (induceComponentSupport (G := G) (A := outside) K).Nonempty :=
    induceComponentSupport_nonempty (G := G) K
  have hA_disjoint :
      Disjoint (induceComponentSupport (G := G) (A := outside) K)
        {z : V | z ∈ C.support} := by
    rw [Set.disjoint_left]
    intro y hyK hyC
    exact hyK.choose hyC
  have hS_large : 1 < ({z : V | z ∈ C.support} : Set V).ncard := by
    rcases Walk.IsCycle.exists_two_support_ne
        (G := G) C hC C.start_mem_support with
      ⟨a, b, ha, hb, _ha_ne, _hb_ne, hab⟩
    exact (Set.one_lt_ncard_iff (s := {z : V | z ∈ C.support})).mpr
      ⟨a, b, ha, hb, hab⟩
  have hclosed :
      forall a : V,
        a ∈ induceComponentSupport (G := G) (A := outside) K ->
          forall b : V, G.Adj a b ->
            b ∈ induceComponentSupport (G := G) (A := outside) K ∨
              b ∈ C.support := by
    intro a ha b hab
    by_cases hbC : b ∈ C.support
    · exact Or.inr hbC
    · exact Or.inl
        (induceComponentSupport_mem_of_adj
          (G := G) (A := outside) K ha hbC hab)
  have hlower :
      2 <= ({v : V | v ∈ C.support ∧
        Exists fun a : V =>
          a ∈ induceComponentSupport (G := G) (A := outside) K ∧
            G.Adj a v}).ncard :=
    IsTwoConnected.boundary_ncard_ge_two
      (G := G) hG hA_nonempty hA_disjoint hS_large hclosed
  have hupper :
      ({v : V | v ∈ C.support ∧
        Exists fun a : V =>
          a ∈ induceComponentSupport (G := G) (A := outside) K ∧
            G.Adj a v}).ncard <= 1 :=
    cycle_external_component_boundary_ncard_le_one_no_homeomorphicTheta
      (G := G) C hC hno K
  omega

/-- Two-connected theta-free graph, spanning-cycle form. -/
theorem cycle_toSubgraph_verts_eq_univ_of_twoConnected_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsTwoConnected G)
    {r : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hno : Not (ContainsHomeomorphicTheta G)) :
    C.toSubgraph.verts = Set.univ := by
  ext v
  constructor
  · intro _hv
    exact Set.mem_univ v
  · intro _hv
    exact C.mem_verts_toSubgraph.mpr
      (cycle_support_univ_of_twoConnected_no_homeomorphicTheta
        (G := G) hG C hC hno v)

/-- If the only off-cycle vertex is a leaf `p` contacting the cycle at `c`,
then every neighbour of any other cycle vertex `v ≠ c` lies on the cycle.
Theta-free chordlessness then bounds the deleted-end degree of `v` by two.
This is the degree-count core of the source rebasing step. -/
theorem deleteEdgeEndsGraph_degree_le_two_of_unique_outside_noncontact
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
    {p c v : {w : V | w ∉ ({x, y} : Set V)}}
    (hp_out : p ∉ C.support)
    (hc : c ∈ C.support)
    (hpc : (deleteEdgeEndsGraph G x y).Adj p c)
    (hv : v ∈ C.support)
    (hvc : v ≠ c)
    (hunique :
      forall s : {w : V | w ∉ ({x, y} : Set V)},
        s ∉ C.support -> s = p) :
    (deleteEdgeEndsGraph G x y).degree v <= 2 := by
  classical
  have hchordless :
      C.IsChordless :=
    isChordless_of_isCycle_no_homeomorphicTheta
      C hC (hno hxy)
  have hneighbor_sub :
      (deleteEdgeEndsGraph G x y).neighborSet v ⊆
        C.toSubgraph.neighborSet v := by
    intro w hvw
    have hwC : w ∈ C.support := by
      by_contra hw_out
      have hw_eq : w = p := hunique w hw_out
      have hvp : (deleteEdgeEndsGraph G x y).Adj v p := by
        simpa [hw_eq] using hvw
      have hv_eq_c : v = c :=
        deleteEdgeEndsGraph_outside_vertex_cycle_contact_unique
          (G := G) hno hxy C hC hp_out hv hc hvp hpc.symm
      exact hvc hv_eq_c
    exact Walk.IsChordless.toSubgraph_adj_of_adj hchordless hv hwC hvw
  have hle :
      ((deleteEdgeEndsGraph G x y).neighborSet v).ncard <=
        (C.toSubgraph.neighborSet v).ncard :=
    Set.ncard_le_ncard hneighbor_sub
  have hD_card :
      ((deleteEdgeEndsGraph G x y).neighborSet v).ncard =
        (deleteEdgeEndsGraph G x y).degree v := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  have hC_card :
      (C.toSubgraph.neighborSet v).ncard = 2 :=
    hC.ncard_neighborSet_toSubgraph_eq_two hv
  omega

/-- Rebase the source non-cut attachment condition at the actual leaf contact.
All vertices except the old distinguished vertex are handled by the original
source hypothesis.  For the old distinguished vertex, the previous degree
lemma and the ambient minimum-degree-three condition force an edge to one of
the deleted endpoints. -/
theorem deleteEdgeEndsGraph_rebased_attach_of_unique_outside_contact
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
    {v p c : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hp_out : p ∉ C.support)
    (hc : c ∈ C.support)
    (hpc : (deleteEdgeEndsGraph G x y).Adj p c)
    (hunique :
      forall s : {w : V | w ∉ ({x, y} : Set V)},
        s ∉ C.support -> s = p) :
    forall t : {w : V | w ∉ ({x, y} : Set V)},
      t ∈ C.support -> t ≠ c ->
        G.Adj (t : V) x ∨ G.Adj (t : V) y := by
  intro t ht htc
  by_cases htv : t = v
  · subst t
    have hdeg_le :
        (deleteEdgeEndsGraph G x y).degree v <= 2 :=
      deleteEdgeEndsGraph_degree_le_two_of_unique_outside_noncontact
        (G := G) hno hxy C hC hp_out hc hpc hv htc hunique
    exact
      deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
        (G := G) (x := x) (y := y) hmin v hdeg_le
  · exact hattach t ht htv

/-- Source-attached-cycle spanning theorem in its no-extra-contact form.  In a
non-planar minimum-degree-three source graph, a cycle satisfying the
Makarychev/Skopenkov non-cut attachment condition must span `G - x - y`.
The proof first applies the checked source dichotomy; the unique off-cycle
leaf branch supplies an actual contact `p--c`, the previous rebasing lemma
moves the attachment condition to `c`, and the rebased unique-leaf endpoint
makes that branch planar, contradicting `hnonplanar`. -/
theorem deleteEdgeEndsGraph_cycle_spans_of_noncut_attach_not_planar
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
    have hattach_c :
        forall t : {w : V | w ∉ ({x, y} : Set V)},
          t ∈ C.support -> t ≠ c ->
            G.Adj (t : V) x ∨ G.Adj (t : V) y :=
      deleteEdgeEndsGraph_rebased_attach_of_unique_outside_contact
        (G := G) hno hmin hxy C hC hv hattach hp_out hc hpc hunique
    have hplanar : IsPlanar G :=
      isPlanar_of_unique_cut_leaf_of_contact
        (G := G) hno hmin hxy C hC hc hattach_c hp_out hpc hunique
    exact False.elim (hnonplanar hplanar)

/-- Final Kuratowski extraction from a source-attached cycle, without the old
global contact predicate.  The previous theorem proves the cycle spans in the
non-planar source-minimal setting; the existing final-cycle extractor then
produces the strict `K5` or `K3,3` subdivision. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_cycle_noncut_attach_not_planar
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
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  have hspans :
      forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support :=
    deleteEdgeEndsGraph_cycle_spans_of_noncut_attach_not_planar
      (G := G) hnonplanar hno hmin hxy C hC hv hattach
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_hanging_cycle_spans
      (G := G) hmin hxy C hC hspans hdegree_delete

/-- A spanning cycle in a theta-free graph is exactly two-regular.  This is the
Skopenkov/Makarychev use of the chorded-cycle theta obstruction: once the
block/cactus argument says the deleted graph is a cycle on all remaining
vertices, no extra chords can remain. -/
theorem degree_eq_two_of_spanning_cycle_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hno : Not (ContainsHomeomorphicTheta G)) :
    forall v : V, G.degree v = 2 :=
  degree_eq_two_of_spanning_isChordless_cycle C hC hspanning
    (isChordless_of_isCycle_no_homeomorphicTheta C hC hno)

/-- Connected finite degree-two graphs admit a simple cycle whose subgraph uses
all vertices.  This is the formal "is a cycle" endpoint used in the
Makarychev/Skopenkov deletion argument. -/
theorem exists_cycle_toSubgraph_verts_eq_univ_of_preconnected_degree_eq_two
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Preconnected)
    (hdegree : forall v : V, G.degree v = 2) :
    Exists fun u : V =>
      Exists fun c : G.Walk u u =>
        c.IsCycle ∧ c.toSubgraph.verts = Set.univ := by
  classical
  let x : V := Classical.choice (inferInstance : Nonempty V)
  have hcycles : G.IsCycles := isCycles_of_degree_eq_two (G := G) hdegree
  have hx_neighbor : (G.neighborSet x).Nonempty := by
    have hxpos : 0 < G.degree x := by
      rw [hdegree x]
      omega
    exact (G.degree_pos_iff_exists_adj x).mp hxpos
  let C : G.ConnectedComponent := G.connectedComponentMk x
  have hxC : x ∈ C.supp := by
    simp [C]
  rcases SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (G := G) (v := x) (c := C) hcycles hxC hx_neighbor with
    ⟨p, hpcycle, hpverts⟩
  have hC_univ : C.supp = Set.univ := by
    ext v
    constructor
    · intro _hv
      exact Set.mem_univ v
    · intro _hv
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact SimpleGraph.ConnectedComponent.sound (hconn v x)
  exact ⟨x, p, hpcycle, by simpa [hC_univ] using hpverts⟩

/-- Skopenkov/Makarychev connectedness reduction in the exact two-regular
case.  If `G - x - y` had two components, the component of `u` is a cycle; a
degree-two edge in another component is disjoint from that cycle.  Minimum
degree in `G` gives endpoint attachments for two non-cut vertices of the
cycle, and the earlier theta constructor contradicts the global hypothesis
that every edge-end deletion is theta-free. -/
theorem deleteEdgeEndsGraph_preconnected_of_degree_eq_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hdegree :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        (deleteEdgeEndsGraph G x y).degree z = 2) :
    (deleteEdgeEndsGraph G x y).Preconnected := by
  classical
  let D : SimpleGraph {w : V | w ∉ ({x, y} : Set V)} :=
    deleteEdgeEndsGraph G x y
  intro u v
  by_contra hnot
  have hcycles : D.IsCycles := by
    exact isCycles_of_degree_eq_two (G := D) (by
      intro z
      simpa [D] using hdegree z)
  have hu_neighbor : (D.neighborSet u).Nonempty := by
    have hudeg : D.degree u = 2 := by
      simpa [D] using hdegree u
    have hupos : 0 < D.degree u := by
      rw [hudeg]
      omega
    exact (D.degree_pos_iff_exists_adj u).mp hupos
  let Cu : D.ConnectedComponent := D.connectedComponentMk u
  have huCu : u ∈ Cu.supp := by
    simpa [Cu] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        (G := D) (v := u))
  rcases SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (G := D) (v := u) (c := Cu) hcycles huCu hu_neighbor with
    ⟨C, hC, hCverts⟩
  have hv_out : v ∉ C.support := by
    intro hvC
    have hvCu : v ∈ Cu.supp := by
      rw [← hCverts]
      exact C.mem_verts_toSubgraph.mpr hvC
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hvCu
    exact hnot ((SimpleGraph.ConnectedComponent.exact hvCu).symm)
  have hv_neighbor : (D.neighborSet v).Nonempty := by
    have hvdeg : D.degree v = 2 := by
      simpa [D] using hdegree v
    have hvpos : 0 < D.degree v := by
      rw [hvdeg]
      omega
    exact (D.degree_pos_iff_exists_adj v).mp hvpos
  rcases hv_neighbor with ⟨q, hvq⟩
  have hvqD : D.Adj v q := by
    simpa [D] using hvq
  have hq_out : q ∉ C.support := by
    intro hqC
    have hqCu : q ∈ Cu.supp := by
      rw [← hCverts]
      exact C.mem_verts_toSubgraph.mpr hqC
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hqCu
    have hqu : D.Reachable q u :=
      SimpleGraph.ConnectedComponent.exact hqCu
    have hvu : D.Reachable v u := hvqD.reachable.trans hqu
    exact hnot hvu.symm
  exact
    False.elim <|
      no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
        (G := G) hno hxy C hC C.start_mem_support
        (fun t _ht _ht_ne =>
          deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
            (G := G) hmin t (by
              have htdeg :
                  (deleteEdgeEndsGraph G x y).degree t = 2 := hdegree t
              omega))
        (by simpa [D] using hvqD)
        (by simpa [D] using hv_out)
        (by simpa [D] using hq_out)

/-- Lemma 3 degree-two endpoint for deleted-end graphs.  Once the remaining
source argument has shown `G - x - y` has maximum degree at most two, Lemma 2
and the minimum-degree-three reduction force every surviving vertex to have
degree exactly two. -/
theorem deleteEdgeEndsGraph_degree_eq_two_of_degree_le_two_not_planar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hmax :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        (deleteEdgeEndsGraph G x y).degree z <= 2) :
    forall z : {w : V | w ∉ ({x, y} : Set V)},
      (deleteEdgeEndsGraph G x y).degree z = 2 := by
  classical
  exact
    degree_eq_two_of_degree_le_two_degree_pos_low_subsingleton
      (G := deleteEdgeEndsGraph G x y)
      hmax
      (fun z => deleteEdgeEndsGraph_degree_pos_of_min_degree_three
        (G := G) hmin z)
      (by
        intro u v hu hv
        exact
          deleteEdgeEndsGraph_hanging_vertex_subsingleton_of_not_planar
            (G := G) hnonplanar hno hmin hxy hu hv)

/-- Under the minimum-degree-three source reduction, deleting two named
vertices always leaves at least one vertex. -/
theorem deleteEdgeEndsGraph_nonempty_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    (x y : V) :
    Nonempty {w : V | w ∉ ({x, y} : Set V)} := by
  classical
  by_contra hnone
  have hneighbor_sub : G.neighborSet x ⊆ ({y} : Set V) := by
    intro w hxw
    by_cases hwy : w = y
    · simp [hwy]
    · have hwx : w ≠ x := hxw.ne.symm
      have hwoutside : w ∉ ({x, y} : Set V) := by
        simp [hwx, hwy]
      exact False.elim (hnone ⟨⟨w, hwoutside⟩⟩)
  have hcard_le :
      (G.neighborSet x).ncard <= ({y} : Set V).ncard :=
    Set.ncard_le_ncard hneighbor_sub
  have hdegree_ncard :
      (G.neighborSet x).ncard = G.degree x := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := x))
  have hdeg_le : G.degree x <= 1 := by
    simpa [hdegree_ncard] using hcard_le
  have hdeg_min : 3 <= G.degree x := hmin x
  omega

/-- Connected deleted-end graphs of minimum deleted degree at least two contain
a cycle.  This is the formal base of the source block/cactus step before one
chooses an end block/hanging cycle. -/
theorem deleteEdgeEndsGraph_exists_cycle_of_degree_ge_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hconn : (deleteEdgeEndsGraph G x y).Preconnected)
    (hdegree_ge :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree z) :
    Exists fun r : {w : V | w ∉ ({x, y} : Set V)} =>
      Exists fun C : (deleteEdgeEndsGraph G x y).Walk r r => C.IsCycle := by
  classical
  letI : Nonempty {w : V | w ∉ ({x, y} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin x y
  haveI : Nontrivial {w : V | w ∉ ({x, y} : Set V)} := by
    let z : {w : V | w ∉ ({x, y} : Set V)} :=
      Classical.choice inferInstance
    have hzpos : 0 < (deleteEdgeEndsGraph G x y).degree z := by
      have hz := hdegree_ge z
      omega
    rcases
        ((deleteEdgeEndsGraph G x y).degree_pos_iff_exists_adj z).mp hzpos with
      ⟨w, hzw⟩
    exact ⟨⟨z, w, hzw.ne⟩⟩
  exact
    exists_isCycle_of_preconnected_min_degree_two
      (G := deleteEdgeEndsGraph G x y) hconn hdegree_ge

/-- Disconnected form of the deleted-end cycle existence step.  Under the
source minimum-degree-three hypothesis the two-end deletion is nonempty; if
every surviving vertex has deleted degree at least two, some component already
contains a simple cycle. -/
theorem deleteEdgeEndsGraph_exists_cycle_of_degree_ge_two_any_component
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hdegree_ge :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree z) :
    Exists fun r : {w : V | w ∉ ({x, y} : Set V)} =>
      Exists fun C : (deleteEdgeEndsGraph G x y).Walk r r => C.IsCycle := by
  classical
  letI : Nonempty {w : V | w ∉ ({x, y} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin x y
  exact
    exists_isCycle_of_nonempty_min_degree_two
      (G := deleteEdgeEndsGraph G x y) hdegree_ge

/-- Deleted-end Lemma 3 endpoint from a maximum-degree-two deletion.  The
minimum-degree-three and low-degree uniqueness reductions first upgrade the
deleted graph to exact degree two; the Skopenkov/Makarychev connectedness
lemma above then supplies the spanning cycle. -/
theorem deleteEdgeEndsGraph_exists_spanning_cycle_of_degree_le_two_not_planar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnonplanar : ¬ IsPlanar G)
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hmax :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        (deleteEdgeEndsGraph G x y).degree z <= 2) :
    Exists fun u : {w : V | w ∉ ({x, y} : Set V)} =>
      Exists fun c : (deleteEdgeEndsGraph G x y).Walk u u =>
        c.IsCycle ∧ c.toSubgraph.verts = Set.univ := by
  classical
  have hdeg :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        (deleteEdgeEndsGraph G x y).degree z = 2 :=
    deleteEdgeEndsGraph_degree_eq_two_of_degree_le_two_not_planar
      (G := G) hnonplanar hno hmin hxy hmax
  have hconn : (deleteEdgeEndsGraph G x y).Preconnected :=
    deleteEdgeEndsGraph_preconnected_of_degree_eq_two
      (G := G) hno hmin hxy hdeg
  letI : Nonempty {w : V | w ∉ ({x, y} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin x y
  exact
    exists_cycle_toSubgraph_verts_eq_univ_of_preconnected_degree_eq_two
      (G := deleteEdgeEndsGraph G x y) hconn hdeg

/-- Source-aligned final obstruction theorem for the Makarychev/Skopenkov
lemma.  Once the block/cactus part has shown that `G - x - y` is connected and
two-regular, the checked final-cycle argument extracts a genuine strict
Kuratowski subdivision in the original graph.  This theorem deliberately avoids
the overloaded `¬ IsPlanar` hypothesis: the remaining bridge work only has to
prove the connected two-regular deletion from the source hypotheses. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hconn : (deleteEdgeEndsGraph G x y).Preconnected)
    (hdegree :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  letI : Nonempty {w : V | w ∉ ({x, y} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin x y
  rcases
      exists_cycle_toSubgraph_verts_eq_univ_of_preconnected_degree_eq_two
        (G := deleteEdgeEndsGraph G x y) hconn (hdegree hxy) with
    ⟨u, C, hC, hCverts⟩
  exact
    containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_spanning_cycle_final
      (G := G) hmin C hC hxy hCverts hdegree

/-- Source-aligned final obstruction theorem for the exact degree-two
deletion case, with connectedness proved internally from the theta-free
two-end deletion hypothesis. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_degree_eq_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    (hxy : G.Adj x y)
    (hdegree :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G :=
  containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_preconnected_degree_eq_two
    (G := G) hmin hxy
    (deleteEdgeEndsGraph_preconnected_of_degree_eq_two
      (G := G) hno hmin hxy (hdegree hxy))
    hdegree


end FourColor

end Schematic.Math.GraphTheory
