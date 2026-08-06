import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.DeletionTransport

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Source-shaped corollary of the end-cycle theta: an edge whose endpoints
are outside the cycle and outside the two external endpoints is disjoint from
the displayed theta, hence impossible under the two-end-deletion no-theta
hypothesis. -/
theorem no_edge_outside_cycle_of_cycle_two_endpoint_attachments
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {p q r a b z x y : V}
    (hpq : G.Adj p q)
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hxy : G.Adj x y)
    (ha_attach : G.Adj a x ∨ G.Adj a y)
    (hb_attach : G.Adj b x ∨ G.Adj b y)
    (hx_cycle : x ∉ c.support)
    (hy_cycle : y ∉ c.support)
    (hp_cycle : p ∉ c.support)
    (hq_cycle : q ∉ c.support)
    (hxp : x ≠ p)
    (hxq : x ≠ q)
    (hyp : y ≠ p)
    (hyq : y ≠ q) :
    False := by
  refine
    no_edge_disjoint_from_cycle_two_endpoint_attachments_of_forall_deleteEdgeEnds_no_homeomorphicTheta
      (G := G) hno hpq c hc ?_ ha hb hz hab haz hbz hxy
      ha_attach hb_attach hx_cycle hy_cycle ?_ ?_
  · intro w hw
    simp
    constructor
    · intro hwp
      exact hp_cycle (by simpa [hwp] using hw)
    · intro hwq
      exact hq_cycle (by simpa [hwq] using hw)
  · simp [hxp, hxq]
  · simp [hyp, hyq]

/-- Deleted-end version of `no_edge_outside_cycle_of_cycle_two_endpoint_attachments`.
If a cycle in `G - x - y` has two distinct vertices attached to the deleted
edge endpoints so that it displays the source theta, then no edge of
`G - x - y` can be disjoint from that cycle.  This is the exact formal form of
the Skopenkov/Makarychev sentence used in the hanging-cycle block argument. -/
theorem no_deleteEdgeEnds_edge_outside_cycle_of_cycle_two_endpoint_attachments
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {x y : V}
    (hxy : G.Adj x y)
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    {a b z : {w : V | w ∉ ({x, y} : Set V)}}
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hz : z ∈ C.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (ha_attach : G.Adj (a : V) x ∨ G.Adj (a : V) y)
    (hb_attach : G.Adj (b : V) x ∨ G.Adj (b : V) y)
    {p q : {w : V | w ∉ ({x, y} : Set V)}}
    (hpq : (deleteEdgeEndsGraph G x y).Adj p q)
    (hp_cycle : p ∉ C.support)
    (hq_cycle : q ∉ C.support) :
    False := by
  classical
  let A : Set V := ({x, y} : Set V)ᶜ
  let φ := (SimpleGraph.Embedding.induce (G := G) A).toHom
  let CG : G.Walk (r : V) (r : V) := C.map φ
  have hCG : CG.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.map
      (p := C) (f := φ) (by
        intro u v huv
        exact Subtype.ext huv) hC
  have hmem_map {t : {w : V | w ∉ ({x, y} : Set V)}} :
      t ∈ C.support -> (t : V) ∈ CG.support := by
    intro ht
    change (t : V) ∈ (C.map φ).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨t, ht, by simp [φ, A]⟩
  have hnot_mem_map {t : {w : V | w ∉ ({x, y} : Set V)}} :
      t ∉ C.support -> (t : V) ∉ CG.support := by
    intro ht htg
    change (t : V) ∈ (C.map φ).support at htg
    rw [SimpleGraph.Walk.support_map] at htg
    rcases List.mem_map.mp htg with ⟨s, hs, hst⟩
    exact ht (by
      have hs_eq : s = t := Subtype.ext hst
      simpa [hs_eq] using hs)
  exact
    no_edge_outside_cycle_of_cycle_two_endpoint_attachments
      (G := G) hno (by simpa [deleteEdgeEndsGraph] using hpq)
      CG hCG
      (hmem_map ha) (hmem_map hb) (hmem_map hz)
      (by intro h; exact hab (Subtype.ext h))
      (by intro h; exact haz (Subtype.ext h))
      (by intro h; exact hbz (Subtype.ext h))
      hxy ha_attach hb_attach
      (by
        intro hxC
        change x ∈ (C.map φ).support at hxC
        rw [SimpleGraph.Walk.support_map] at hxC
        rcases List.mem_map.mp hxC with ⟨s, _hs, hsx⟩
        have hsx' : (s : V) = x := by
          simpa [φ, A] using hsx
        exact s.property (by simp [hsx']))
      (by
        intro hyC
        change y ∈ (C.map φ).support at hyC
        rw [SimpleGraph.Walk.support_map] at hyC
        rcases List.mem_map.mp hyC with ⟨s, _hs, hsy⟩
        have hsy' : (s : V) = y := by
          simpa [φ, A] using hsy
        exact s.property (by simp [hsy']))
      (hnot_mem_map hp_cycle)
      (hnot_mem_map hq_cycle)
      (by
        intro h
        exact p.property (by simp [h.symm]))
      (by
        intro h
        exact q.property (by simp [h.symm]))
      (by
        intro h
        exact p.property (by simp [h.symm]))
      (by
        intro h
        exact q.property (by simp [h.symm]))

/-- Hanging-cycle source step.  If every vertex of a deleted-end cycle except
the displayed cut vertex attaches to one of the deleted endpoints, then every
edge of the deleted-end graph has an endpoint on that cycle.  This is the
formal version of Skopenkov's "hence by (1) each edge of `K - x - y` has an
end on `C`" for the cycle chosen as a hanging block. -/
theorem no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
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
    {p q : {w : V | w ∉ ({x, y} : Set V)}}
    (hpq : (deleteEdgeEndsGraph G x y).Adj p q)
    (hp_cycle : p ∉ C.support)
    (hq_cycle : q ∉ C.support) :
    False := by
  rcases
      Walk.IsCycle.exists_two_support_ne
        (G := deleteEdgeEndsGraph G x y) C hC hv with
    ⟨a, b, ha, hb, ha_ne_v, hb_ne_v, hab⟩
  exact
    no_deleteEdgeEnds_edge_outside_cycle_of_cycle_two_endpoint_attachments
      (G := G) hno hxy C hC
      ha hb hv hab ha_ne_v hb_ne_v
      (hattach a ha ha_ne_v)
      (hattach b hb hb_ne_v)
      hpq hp_cycle hq_cycle

/-- Component-contact form of the no-theta cycle obstruction in `G - x - y`.
If two outside neighbours of cycle vertices lie in the same component of the
graph induced outside the cycle, then those cycle vertices must be consecutive
on the cycle.  Otherwise the outside path between the neighbours and the two
contact edges form a suppressed-edge theta subdivision in the deleted-end
graph, contradicting the standing Makarychev/Skopenkov condition. -/
theorem deleteEdgeEndsGraph_cycle_contacts_adjacent_of_external_reachable
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {x y : V}
    (hxy : G.Adj x y)
    {r a b u v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hab_ne : a ≠ b)
    (hu_outside : u ∉ C.support)
    (hv_outside : v ∉ C.support)
    (hreach :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).Reachable
        (⟨u, hu_outside⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support})
        (⟨v, hv_outside⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}))
    (hau : (deleteEdgeEndsGraph G x y).Adj a u)
    (hbv : (deleteEdgeEndsGraph G x y).Adj b v) :
    C.toSubgraph.Adj a b := by
  classical
  by_contra hnot_adj
  exact
    (hno hxy)
      (ContainsHomeomorphicTheta.of_edgeSubdivision
        (ContainsEdgeThetaSubdivision.of_cycle_external_reachable_nonadjacent
          (G := deleteEdgeEndsGraph G x y)
          C hC ha hb hab_ne hnot_adj
          hu_outside hv_outside hreach hau hbv))

/-- Connected-component form of
`deleteEdgeEndsGraph_cycle_contacts_adjacent_of_external_reachable`.  This is
the form used by the block/cactus reduction: all contacts from one outside
component to a theta-free deleted-end cycle are pairwise consecutive on the
cycle. -/
theorem deleteEdgeEndsGraph_cycle_contacts_adjacent_of_same_external_component
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {x y : V}
    (hxy : G.Adj x y)
    {r a b u v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hab_ne : a ≠ b)
    (hu_outside : u ∉ C.support)
    (hv_outside : v ∉ C.support)
    (K :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).ConnectedComponent)
    (huK :
      (⟨u, hu_outside⟩ :
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hvK :
      (⟨v, hv_outside⟩ :
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hau : (deleteEdgeEndsGraph G x y).Adj a u)
    (hbv : (deleteEdgeEndsGraph G x y).Adj b v) :
    C.toSubgraph.Adj a b := by
  classical
  let H : SimpleGraph
      {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support} :=
    (deleteEdgeEndsGraph G x y).induce
      {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}
  let uH : {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support} :=
    ⟨u, hu_outside⟩
  let vH : {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support} :=
    ⟨v, hv_outside⟩
  have hu_eq : H.connectedComponentMk uH = K := by
    simpa [H, uH] using (SimpleGraph.ConnectedComponent.mem_supp_iff K uH).mp huK
  have hv_eq : H.connectedComponentMk vH = K := by
    simpa [H, vH] using (SimpleGraph.ConnectedComponent.mem_supp_iff K vH).mp hvK
  have hreach : H.Reachable uH vH :=
    SimpleGraph.ConnectedComponent.exact (hu_eq.trans hv_eq.symm)
  exact
    deleteEdgeEndsGraph_cycle_contacts_adjacent_of_external_reachable
      (G := G) hno hxy C hC ha hb hab_ne
      hu_outside hv_outside
      (by simpa [H, uH, vH] using hreach)
      hau hbv

/-- Strong outside-component contact obstruction.  In a theta-free deleted-end
graph, one connected component outside a displayed cycle cannot attach to two
distinct cycle vertices.  The outside component supplies an external path with
a genuine outside internal vertex, and the cycle supplies the other two
branches of a theta. -/
theorem deleteEdgeEndsGraph_cycle_contacts_eq_of_external_reachable
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {x y : V}
    (hxy : G.Adj x y)
    {r a b u v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hu_outside : u ∉ C.support)
    (hv_outside : v ∉ C.support)
    (hreach :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).Reachable
        (⟨u, hu_outside⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support})
        (⟨v, hv_outside⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}))
    (hau : (deleteEdgeEndsGraph G x y).Adj a u)
    (hbv : (deleteEdgeEndsGraph G x y).Adj b v) :
    a = b := by
  classical
  by_contra hab_ne
  rcases
      Walk.IsCycle.exists_two_support_ne
        (G := deleteEdgeEndsGraph G x y) C hC ha with
    ⟨z₁, z₂, hz₁, hz₂, hz₁_ne_a, hz₂_ne_a, hz₁z₂⟩
  have htheta : ContainsEdgeThetaSubdivision (deleteEdgeEndsGraph G x y) := by
    rcases
        reachable_induce_exists_chordless_path_support_subset
          (G := deleteEdgeEndsGraph G x y)
          (A := {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support})
          hu_outside hv_outside hreach with
      ⟨q, hq_path, _hq_chordless, hq_support⟩
    by_cases hz₁b : z₁ = b
    · have hz₂_ne_b : b ≠ z₂ := by
        intro hbz₂
        exact hz₁z₂ (by rw [hz₁b, hbz₂])
      exact
        ContainsEdgeThetaSubdivision.of_cycle_external_connector
          (G := deleteEdgeEndsGraph G x y)
          C hC ha hb hz₂ hab_ne hz₂_ne_a.symm hz₂_ne_b
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
          (G := deleteEdgeEndsGraph G x y)
          C hC ha hb hz₁ hab_ne hz₁_ne_a.symm hz₁_ne_b
          hau q hq_path
          (by
            intro t ht
            exact hq_support t ht)
          hbv
  exact (hno hxy) (ContainsHomeomorphicTheta.of_edgeSubdivision htheta)

/-- Connected-component form of
`deleteEdgeEndsGraph_cycle_contacts_eq_of_external_reachable`. -/
theorem deleteEdgeEndsGraph_cycle_contacts_eq_of_same_external_component
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {x y : V}
    (hxy : G.Adj x y)
    {r a b u v : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hu_outside : u ∉ C.support)
    (hv_outside : v ∉ C.support)
    (K :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).ConnectedComponent)
    (huK :
      (⟨u, hu_outside⟩ :
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hvK :
      (⟨v, hv_outside⟩ :
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hau : (deleteEdgeEndsGraph G x y).Adj a u)
    (hbv : (deleteEdgeEndsGraph G x y).Adj b v) :
    a = b := by
  classical
  let H : SimpleGraph
      {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support} :=
    (deleteEdgeEndsGraph G x y).induce
      {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}
  let uH : {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support} :=
    ⟨u, hu_outside⟩
  let vH : {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support} :=
    ⟨v, hv_outside⟩
  have hu_eq : H.connectedComponentMk uH = K := by
    simpa [H, uH] using (SimpleGraph.ConnectedComponent.mem_supp_iff K uH).mp huK
  have hv_eq : H.connectedComponentMk vH = K := by
    simpa [H, vH] using (SimpleGraph.ConnectedComponent.mem_supp_iff K vH).mp hvK
  have hreach : H.Reachable uH vH :=
    SimpleGraph.ConnectedComponent.exact (hu_eq.trans hv_eq.symm)
  exact
    deleteEdgeEndsGraph_cycle_contacts_eq_of_external_reachable
      (G := G) hno hxy C hC ha hb hu_outside hv_outside
      (by simpa [H, uH, vH] using hreach)
      hau hbv

/-- A single outside vertex has at most one neighbour on a theta-free
deleted-end cycle.  This is the pointwise contact form consumed by the
hanging-cycle leaf lemmas. -/
theorem deleteEdgeEndsGraph_outside_vertex_cycle_contact_unique
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {x y : V}
    (hxy : G.Adj x y)
    {r p c d : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hp_outside : p ∉ C.support)
    (hc : c ∈ C.support)
    (hd : d ∈ C.support)
    (hpc : (deleteEdgeEndsGraph G x y).Adj c p)
    (hpd : (deleteEdgeEndsGraph G x y).Adj d p) :
    c = d := by
  classical
  exact
    deleteEdgeEndsGraph_cycle_contacts_eq_of_external_reachable
      (G := G) hno hxy C hC hc hd hp_outside hp_outside
      (by
        exact SimpleGraph.Reachable.refl
          (⟨p, hp_outside⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}))
      hpc hpd

/-- If one outside component has a displayed contact `v` with the cycle, then
every other contact from that outside component is the same vertex `v`. -/
theorem deleteEdgeEndsGraph_same_external_component_contact_eq
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {x y : V}
    (hxy : G.Adj x y)
    {r c v p t : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hc : c ∈ C.support)
    (hv : v ∈ C.support)
    (hp_outside : p ∉ C.support)
    (ht_outside : t ∉ C.support)
    (K :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).ConnectedComponent)
    (hpK :
      (⟨p, hp_outside⟩ :
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (htK :
      (⟨t, ht_outside⟩ :
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hcv : (deleteEdgeEndsGraph G x y).Adj c t)
    (hvp : (deleteEdgeEndsGraph G x y).Adj v p) :
    c = v := by
  exact
    deleteEdgeEndsGraph_cycle_contacts_eq_of_same_external_component
      (G := G) hno hxy C hC hc hv ht_outside hp_outside K htK hpK hcv hvp

/-- Connected outside-component form of the source "common end" step.  Suppose
`C` is a displayed cycle in `G - x - y`, every non-cut vertex of `C` attaches
to one of the deleted endpoints, and the graph induced outside `C` is
connected.  If that outside component has one displayed contact with `v`, then
every vertex outside `C` is adjacent to `v` in `G - x - y`.

This is the formal version of the Makarychev/Skopenkov sentence that the
outside paths and the cycle paths would otherwise have a common end: any
neighbour of an outside vertex is either on `C`, where the contact-uniqueness
theta obstruction forces it to be `v`, or outside `C`, where the no-outside-edge
theta obstruction contradicts the source attachment hypothesis. -/
theorem deleteEdgeEndsGraph_outside_vertices_adj_contact_of_connected_outside
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
    {v p : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hp_outside : p ∉ C.support)
    (hpv : (deleteEdgeEndsGraph G x y).Adj p v)
    (houtside_preconnected :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).Preconnected)
    (hpos :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        0 < (deleteEdgeEndsGraph G x y).degree t) :
    forall t : {w : V | w ∉ ({x, y} : Set V)},
      t ∉ C.support -> (deleteEdgeEndsGraph G x y).Adj t v := by
  classical
  intro t ht_outside
  rcases ((deleteEdgeEndsGraph G x y).degree_pos_iff_exists_adj t).mp
      (hpos t) with
    ⟨w, htw⟩
  by_cases hwC : w ∈ C.support
  · have hreach :
        ((deleteEdgeEndsGraph G x y).induce
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).Reachable
          (⟨t, ht_outside⟩ :
            {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support})
          (⟨p, hp_outside⟩ :
            {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) :=
      houtside_preconnected
        (⟨t, ht_outside⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support})
        (⟨p, hp_outside⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support})
    have hwv : w = v :=
      deleteEdgeEndsGraph_cycle_contacts_eq_of_external_reachable
        (G := G) hno hxy C hC hwC hv ht_outside hp_outside
        hreach htw.symm hpv.symm
    simpa [hwv] using htw
  · exact False.elim
      (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
        (G := G) hno hxy C hC hv hattach htw ht_outside hwC)

/-- Component-cover version of
`deleteEdgeEndsGraph_outside_vertices_adj_contact_of_connected_outside`.  This
is the exact form used by an end-block proof: all vertices outside the
displayed cycle lie in one named component of the outside induced graph, and
that component has one contact to the cut vertex `v`. -/
theorem deleteEdgeEndsGraph_outside_vertices_adj_contact_of_common_external_component
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
    {v p : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hp_outside : p ∉ C.support)
    (hpv : (deleteEdgeEndsGraph G x y).Adj p v)
    (K :
      ((deleteEdgeEndsGraph G x y).induce
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}).ConnectedComponent)
    (hpK :
      (⟨p, hp_outside⟩ :
        {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hallK :
      forall (t : {w : V | w ∉ ({x, y} : Set V)}) (ht : t ∉ C.support),
        (⟨t, ht⟩ :
          {z : {w : V | w ∉ ({x, y} : Set V)} | z ∉ C.support}) ∈ K.supp)
    (hpos :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        0 < (deleteEdgeEndsGraph G x y).degree t) :
    forall t : {w : V | w ∉ ({x, y} : Set V)},
      t ∉ C.support -> (deleteEdgeEndsGraph G x y).Adj t v := by
  classical
  intro t ht_outside
  rcases ((deleteEdgeEndsGraph G x y).degree_pos_iff_exists_adj t).mp
      (hpos t) with
    ⟨w, htw⟩
  by_cases hwC : w ∈ C.support
  · have hwv : w = v :=
      deleteEdgeEndsGraph_same_external_component_contact_eq
        (G := G) hno hxy C hC hwC hv hp_outside ht_outside
        K hpK (hallK t ht_outside) htw.symm hpv.symm
    simpa [hwv] using htw
  · exact False.elim
      (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
        (G := G) hno hxy C hC hv hattach htw ht_outside hwC)

/-- Leaf form needing only one displayed cycle contact.  Under the source
non-cut attachment condition, no edge can stay completely outside the cycle;
under the theta-free deletion hypothesis, one outside vertex cannot have two
distinct cycle contacts.  Therefore any outside vertex with one cycle contact
is a leaf of `G - x - y`. -/
theorem deleteEdgeEndsGraph_degree_eq_one_of_outside_cycle_contact
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
    {v p c : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hp_outside : p ∉ C.support)
    (hc : c ∈ C.support)
    (hpc : (deleteEdgeEndsGraph G x y).Adj p c) :
    (deleteEdgeEndsGraph G x y).degree p = 1 := by
  classical
  exact (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr
    ⟨c, hpc, by
      intro t hpt
      by_cases htC : t ∈ C.support
      · exact
          deleteEdgeEndsGraph_outside_vertex_cycle_contact_unique
            (G := G) hno hxy C hC hp_outside htC hc hpt.symm hpc.symm
      · exact False.elim
          (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
            (G := G) hno hxy C hC hv hattach hpt hp_outside htC)⟩

/-- Strong source spanning lemma.  If a deleted-end cycle satisfies the
Makarychev/Skopenkov non-cut attachment condition, then a minimum deleted
degree of two already forces the cycle to span.  Indeed, any outside vertex has
positive degree; its first neighbour is either outside the cycle, contradicting
the no-outside-edge obstruction, or on the cycle, in which case the previous
contact leaf lemma gives deleted degree one. -/
theorem deleteEdgeEndsGraph_cycle_spans_of_degree_ge_two_of_noncut_vertices_attach
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
    (hdegree_ge :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        2 <= (deleteEdgeEndsGraph G x y).degree t) :
    forall t : {w : V | w ∉ ({x, y} : Set V)}, t ∈ C.support := by
  classical
  intro p
  by_contra hp_outside
  have hp_pos : 0 < (deleteEdgeEndsGraph G x y).degree p := by
    have hp_ge := hdegree_ge p
    omega
  rcases ((deleteEdgeEndsGraph G x y).degree_pos_iff_exists_adj p).mp hp_pos with
    ⟨w, hpw⟩
  by_cases hwC : w ∈ C.support
  · have hp_degree :
        (deleteEdgeEndsGraph G x y).degree p = 1 :=
      deleteEdgeEndsGraph_degree_eq_one_of_outside_cycle_contact
        (G := G) hno hxy C hC hv hattach hp_outside hwC hpw
    have hp_ge := hdegree_ge p
    omega
  · exact
      (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
        (G := G) hno hxy C hC hv hattach hpw hp_outside hwC)

/-- Pointwise leaf form for a displayed outside contact.  If every edge
outside the cycle is ruled out by the source attachment hypothesis and an
outside vertex `p` is adjacent to the displayed contact `v`, then theta-free
contact uniqueness forces `v` to be the only neighbour of `p`. -/
theorem deleteEdgeEndsGraph_degree_eq_one_of_outside_cycle_adj_contact
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
    {v p : {w : V | w ∉ ({x, y} : Set V)}}
    (hv : v ∈ C.support)
    (hattach :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        t ∈ C.support -> t ≠ v ->
          G.Adj (t : V) x ∨ G.Adj (t : V) y)
    (hp_outside : p ∉ C.support)
    (hpv : (deleteEdgeEndsGraph G x y).Adj p v) :
    (deleteEdgeEndsGraph G x y).degree p = 1 := by
  classical
  exact (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr
    ⟨v, hpv, by
      intro t hpt
      by_cases htC : t ∈ C.support
      · exact
          deleteEdgeEndsGraph_outside_vertex_cycle_contact_unique
            (G := G) hno hxy C hC hp_outside htC hv hpt.symm hpv.symm
      · exact False.elim
          (no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
            (G := G) hno hxy C hC hv hattach hpt hp_outside htC)⟩

/-- In the hanging-cycle situation, every vertex outside the cycle is a
degree-one vertex of the deleted-end graph.  The hypotheses express the two
source inputs separately: vertices of `C - v` attach to the deleted endpoints,
and outside vertices can meet `C` only at the cut vertex `v`. -/
theorem deleteEdgeEndsGraph_degree_eq_one_of_outside_hanging_cycle
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
    (hpos :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        0 < (deleteEdgeEndsGraph G x y).degree t)
    {p : {w : V | w ∉ ({x, y} : Set V)}}
    (hp_out : p ∉ C.support) :
    (deleteEdgeEndsGraph G x y).degree p = 1 := by
  exact
    Walk.degree_eq_one_of_outside_cycle_no_edges_of_only_contact
      (G := deleteEdgeEndsGraph G x y)
      C hp_out
      (by
        intro a b hab ha hb
        exact
          no_deleteEdgeEnds_edge_outside_cycle_of_noncut_vertices_attach
            (G := G) hno hxy C hC hv hattach hab ha hb)
      (by
        intro a b hab ha hb
        exact hcontact ha hb hab)
      (hpos p)

/-- Low-degree uniqueness applied to the hanging-cycle setup: once every
outside vertex is a leaf of `G - x - y`, there is at most one such outside
vertex.  The later Makarychev Lemma 2 theorem supplies `hlow`; this statement
is placed earlier so the block/cactus proof can be assembled without a forward
dependency. -/
theorem deleteEdgeEndsGraph_outside_cycle_subsingleton_of_hanging_cycle_low_subsingleton
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
    (hpos :
      forall t : {w : V | w ∉ ({x, y} : Set V)},
        0 < (deleteEdgeEndsGraph G x y).degree t)
    (hlow :
      forall {p q : {w : V | w ∉ ({x, y} : Set V)}},
        (deleteEdgeEndsGraph G x y).degree p <= 1 ->
          (deleteEdgeEndsGraph G x y).degree q <= 1 -> p = q) :
    {t : {w : V | w ∉ ({x, y} : Set V)} | t ∉ C.support}.Subsingleton := by
  intro p hp q hq
  have hpdeg :
      (deleteEdgeEndsGraph G x y).degree p <= 1 := by
    have h :=
      deleteEdgeEndsGraph_degree_eq_one_of_outside_hanging_cycle
        (G := G) hno hxy C hC hv hattach hcontact hpos hp
    omega
  have hqdeg :
      (deleteEdgeEndsGraph G x y).degree q <= 1 := by
    have h :=
      deleteEdgeEndsGraph_degree_eq_one_of_outside_hanging_cycle
        (G := G) hno hxy C hC hv hattach hcontact hpos hq
    omega
  exact hlow hpdeg hqdeg


end FourColor

end Schematic.Math.GraphTheory
