import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- A homeomorphic theta in `G - a - b` transports to the outside part of the
edge contraction `G / ab`. -/
theorem ContainsHomeomorphicTheta.to_collapseEdgeOutside
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (h : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    ContainsHomeomorphicTheta
      ((GraphContraction.collapseEdge G hab).graph.induce
        {y : (GraphContraction.collapseEdge G hab).Target |
          y ≠ (none : (GraphContraction.collapseEdge G hab).Target)}) := by
  classical
  let φ := deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab
  exact ContainsHomeomorphicTheta.map
    φ.toRelEmbedding.toRelHom φ.toEquiv.injective h

/-- A theta in the non-collapsed part of `G / ab` is also a theta in the
edge-deleted graph `G - ab`, by transporting it back across
`G - a - b = (G / ab) - [ab]` and then using the endpoint-deletion inclusion. -/
theorem ContainsHomeomorphicTheta.of_collapseEdgeOutside_to_deletedGraph
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (h : ContainsHomeomorphicTheta
      ((GraphContraction.collapseEdge G hab).graph.induce
        {y : (GraphContraction.collapseEdge G hab).Target |
          y ≠ (none : (GraphContraction.collapseEdge G hab).Target)})) :
    ContainsHomeomorphicTheta (EdgeDeletion.deletedGraph G a b) := by
  classical
  let φ := (deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab).symm
  have hdelEnds :
      ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b) :=
    ContainsHomeomorphicTheta.map
      φ.toRelEmbedding.toRelHom φ.toEquiv.injective h
  exact ContainsHomeomorphicTheta.to_deletedGraph hdelEnds

/-- Contrapositive of
`ContainsHomeomorphicTheta.of_collapseEdgeOutside_to_deletedGraph`. -/
theorem not_containsHomeomorphicTheta_collapseEdgeOutside_of_deletedGraph
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (hno : Not (ContainsHomeomorphicTheta (EdgeDeletion.deletedGraph G a b))) :
    Not (ContainsHomeomorphicTheta
      ((GraphContraction.collapseEdge G hab).graph.induce
        {y : (GraphContraction.collapseEdge G hab).Target |
          y ≠ (none : (GraphContraction.collapseEdge G hab).Target)})) := by
  intro htheta
  exact hno
    (ContainsHomeomorphicTheta.of_collapseEdgeOutside_to_deletedGraph hab htheta)

theorem ContainsStrictSubdivision.of_deleteEdgeEndsGraph
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {x y : V}
    (h : ContainsStrictSubdivision K (deleteEdgeEndsGraph G x y)) :
    ContainsStrictSubdivision K G := by
  let f : deleteEdgeEndsGraph G x y ↪g G :=
    SimpleGraph.Embedding.induce ({x, y} : Set V)ᶜ
  exact ContainsStrictSubdivision.map f f.injective h

theorem ContainsThetaSubdivision.of_deleteEdgeEndsGraph
    {V : Type u} {G : SimpleGraph V}
    {x y : V}
    (h : ContainsThetaSubdivision (deleteEdgeEndsGraph G x y)) :
    ContainsThetaSubdivision G :=
  ContainsStrictSubdivision.of_deleteEdgeEndsGraph h

/-- Restrict a strict theta subdivision to a two-end deletion when all branch
vertices and all source-edge path vertices avoid the two deleted endpoints. -/
theorem ContainsThetaSubdivision.to_deleteEdgeEndsGraph_of_support_avoids
    {V : Type u}
    {G : SimpleGraph V}
    {p q : V}
    (h : ContainsThetaSubdivision G)
    (hbranch :
      forall a : K23Vertex,
        (Classical.choice h).branchVertex a ∉ ({p, q} : Set V))
    (hedge :
      forall {a b : K23Vertex} (hab : K23Graph.Adj a b) {z : V},
        z ∈ ((Classical.choice h).edgePath hab).support ->
          z ∉ ({p, q} : Set V)) :
    ContainsThetaSubdivision (deleteEdgeEndsGraph G p q) := by
  classical
  exact
    ContainsStrictSubdivision.targetRestrict
      (H := K23Graph) (G := G) (S := ({p, q} : Set V)ᶜ)
      h
      (by
        intro a
        exact hbranch a)
      (by
        intro a b hab z hz
        exact hedge hab hz)

/-- Source Lemma 1 mechanism for strict theta subdivisions: under the standing
hypothesis that every edge-end deletion is theta-free, no edge can be disjoint
from all vertices used by a strict theta model. -/
theorem no_edge_disjoint_from_strictTheta_of_forall_deleteEdgeEnds_no_homeomorphicTheta
    {V : Type u}
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {p q : V}
    (hpq : G.Adj p q)
    (hθ : ContainsThetaSubdivision G)
    (hbranch :
      forall a : K23Vertex,
        (Classical.choice hθ).branchVertex a ∉ ({p, q} : Set V))
    (hedge :
      forall {a b : K23Vertex} (hab : K23Graph.Adj a b) {z : V},
        z ∈ ((Classical.choice hθ).edgePath hab).support ->
          z ∉ ({p, q} : Set V)) :
    False :=
  hno hpq
    (ContainsHomeomorphicTheta.of_strict
      (ContainsThetaSubdivision.to_deleteEdgeEndsGraph_of_support_avoids
        hθ hbranch hedge))

/-- Restrict a suppressed-edge theta subdivision to a two-end deletion when
all branch vertices and all source-edge path vertices avoid the two deleted
endpoints. -/
theorem ContainsEdgeThetaSubdivision.to_deleteEdgeEndsGraph_of_support_avoids
    {V : Type u}
    {G : SimpleGraph V}
    {p q : V}
    (h : ContainsEdgeThetaSubdivision G)
    (hbranch :
      forall a : EdgeThetaVertex,
        (Classical.choice h).branchVertex a ∉ ({p, q} : Set V))
    (hedge :
      forall {a b : EdgeThetaVertex} (hab : EdgeThetaGraph.Adj a b) {z : V},
        z ∈ ((Classical.choice h).edgePath hab).support ->
          z ∉ ({p, q} : Set V)) :
    ContainsEdgeThetaSubdivision (deleteEdgeEndsGraph G p q) := by
  classical
  exact
    ContainsStrictSubdivision.targetRestrict
      (H := EdgeThetaGraph) (G := G) (S := ({p, q} : Set V)ᶜ)
      h
      (by
        intro a
        exact hbranch a)
      (by
        intro a b hab z hz
        exact hedge hab hz)

/-- Source Lemma 1 mechanism for suppressed-edge theta subdivisions. -/
theorem no_edge_disjoint_from_edgeThetaSubdivision_of_forall_deleteEdgeEnds_no_homeomorphicTheta
    {V : Type u}
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {p q : V}
    (hpq : G.Adj p q)
    (hθ : ContainsEdgeThetaSubdivision G)
    (hbranch :
      forall a : EdgeThetaVertex,
        (Classical.choice hθ).branchVertex a ∉ ({p, q} : Set V))
    (hedge :
      forall {a b : EdgeThetaVertex} (hab : EdgeThetaGraph.Adj a b) {z : V},
        z ∈ ((Classical.choice hθ).edgePath hab).support ->
          z ∉ ({p, q} : Set V)) :
    False :=
  hno hpq
    (ContainsHomeomorphicTheta.of_edgeSubdivision
      (ContainsEdgeThetaSubdivision.to_deleteEdgeEndsGraph_of_support_avoids
        hθ hbranch hedge))

/-- Deleted-end form of the cycle/common-neighbour theta extraction.  If a
cycle and an external common neighbour avoid the two endpoints of an edge
`pq`, then deleting `p,q` still leaves a homeomorphic theta. -/
theorem containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_common_neighbor
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {p q r a b z t : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hcycle_avoids :
      forall w : V, w ∈ c.support -> w ∉ ({p, q} : Set V))
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hat : G.Adj a t)
    (hbt : G.Adj b t)
    (ht_cycle : t ∉ c.support)
    (ht_avoids : t ∉ ({p, q} : Set V)) :
    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q) := by
  classical
  let A : Set V := ({p, q} : Set V)ᶜ
  let cA :
      (G.induce A).Walk
        ⟨r, hcycle_avoids r c.start_mem_support⟩
        ⟨r, hcycle_avoids r c.end_mem_support⟩ :=
    c.induce A hcycle_avoids
  have hcA : cA.IsCycle := by
    have hmap :
        (cA.map (SimpleGraph.Embedding.induce (G := G) A).toHom).IsCycle := by
      simpa [cA, A] using hc
    exact
      (SimpleGraph.Walk.map_isCycle_iff_of_injective
        (p := cA)
        (f := (SimpleGraph.Embedding.induce (G := G) A).toHom)
        (SimpleGraph.Embedding.induce (G := G) A).injective).mp hmap
  let aA : A := ⟨a, hcycle_avoids a ha⟩
  let bA : A := ⟨b, hcycle_avoids b hb⟩
  let zA : A := ⟨z, hcycle_avoids z hz⟩
  let tA : A := ⟨t, ht_avoids⟩
  have haA : aA ∈ cA.support := by
    simpa [aA, cA, A] using
      (Walk.mem_induce_support_of_mem_support
        (G := G) (S := A) c hcycle_avoids ha)
  have hbA : bA ∈ cA.support := by
    simpa [bA, cA, A] using
      (Walk.mem_induce_support_of_mem_support
        (G := G) (S := A) c hcycle_avoids hb)
  have hzA : zA ∈ cA.support := by
    simpa [zA, cA, A] using
      (Walk.mem_induce_support_of_mem_support
        (G := G) (S := A) c hcycle_avoids hz)
  have habA : aA ≠ bA := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hazA : aA ≠ zA := by
    intro h
    exact haz (congrArg Subtype.val h)
  have hbzA : bA ≠ zA := by
    intro h
    exact hbz (congrArg Subtype.val h)
  have hatA : (deleteEdgeEndsGraph G p q).Adj aA tA := by
    simpa [deleteEdgeEndsGraph, A, aA, tA] using hat
  have hbtA : (deleteEdgeEndsGraph G p q).Adj bA tA := by
    simpa [deleteEdgeEndsGraph, A, bA, tA] using hbt
  have ht_cycleA : tA ∉ cA.support := by
    intro htA
    exact ht_cycle
      (Walk.mem_support_of_mem_induce_support
        (G := G) (S := A) c hcycle_avoids
        (x := tA) (by simpa [cA, A, tA] using htA))
  exact
    ContainsHomeomorphicTheta.of_edgeSubdivision
      (ContainsEdgeThetaSubdivision.of_cycle_common_neighbor
        (G := deleteEdgeEndsGraph G p q)
        cA hcA haA hbA hzA habA hazA hbzA hatA hbtA ht_cycleA)

/-- Source Lemma 1 mechanism specialized to the end-cycle theta: under the
standing hypothesis that every edge-end deletion is homeomorphic-theta-free,
no edge can be disjoint from a cycle plus an external common neighbour of two
cycle vertices. -/
theorem no_edge_disjoint_from_cycle_common_neighbor_of_forall_deleteEdgeEnds_no_homeomorphicTheta
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {p q r a b z t : V}
    (hpq : G.Adj p q)
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hcycle_avoids :
      forall w : V, w ∈ c.support -> w ∉ ({p, q} : Set V))
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hat : G.Adj a t)
    (hbt : G.Adj b t)
    (ht_cycle : t ∉ c.support)
    (ht_avoids : t ∉ ({p, q} : Set V)) :
    False :=
  hno hpq
    (containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_common_neighbor
      (G := G) c hc hcycle_avoids ha hb hz hab haz hbz
      hat hbt ht_cycle ht_avoids)

/-- Deleted-end form of the mixed end-cycle theta extraction.  If two cycle
vertices attach to opposite ends of an external edge `xy`, and the whole
configuration avoids the endpoints of `pq`, then deleting `p,q` still leaves a
homeomorphic theta. -/
theorem containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_adjacent_endpoint_path
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {p q r a b z x y : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hcycle_avoids :
      forall w : V, w ∈ c.support -> w ∉ ({p, q} : Set V))
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hax : G.Adj a x)
    (hxy : G.Adj x y)
    (hby : G.Adj b y)
    (hx_cycle : x ∉ c.support)
    (hy_cycle : y ∉ c.support)
    (hx_avoids : x ∉ ({p, q} : Set V))
    (hy_avoids : y ∉ ({p, q} : Set V)) :
    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q) := by
  classical
  let A : Set V := ({p, q} : Set V)ᶜ
  let cA :
      (G.induce A).Walk
        ⟨r, hcycle_avoids r c.start_mem_support⟩
        ⟨r, hcycle_avoids r c.end_mem_support⟩ :=
    c.induce A hcycle_avoids
  have hcA : cA.IsCycle := by
    have hmap :
        (cA.map (SimpleGraph.Embedding.induce (G := G) A).toHom).IsCycle := by
      simpa [cA, A] using hc
    exact
      (SimpleGraph.Walk.map_isCycle_iff_of_injective
        (p := cA)
        (f := (SimpleGraph.Embedding.induce (G := G) A).toHom)
        (SimpleGraph.Embedding.induce (G := G) A).injective).mp hmap
  let aA : A := ⟨a, hcycle_avoids a ha⟩
  let bA : A := ⟨b, hcycle_avoids b hb⟩
  let zA : A := ⟨z, hcycle_avoids z hz⟩
  let xA : A := ⟨x, hx_avoids⟩
  let yA : A := ⟨y, hy_avoids⟩
  have haA : aA ∈ cA.support := by
    simpa [aA, cA, A] using
      (Walk.mem_induce_support_of_mem_support
        (G := G) (S := A) c hcycle_avoids ha)
  have hbA : bA ∈ cA.support := by
    simpa [bA, cA, A] using
      (Walk.mem_induce_support_of_mem_support
        (G := G) (S := A) c hcycle_avoids hb)
  have hzA : zA ∈ cA.support := by
    simpa [zA, cA, A] using
      (Walk.mem_induce_support_of_mem_support
        (G := G) (S := A) c hcycle_avoids hz)
  have habA : aA ≠ bA := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hazA : aA ≠ zA := by
    intro h
    exact haz (congrArg Subtype.val h)
  have hbzA : bA ≠ zA := by
    intro h
    exact hbz (congrArg Subtype.val h)
  have haxA : (deleteEdgeEndsGraph G p q).Adj aA xA := by
    simpa [deleteEdgeEndsGraph, A, aA, xA] using hax
  have hxyA : (deleteEdgeEndsGraph G p q).Adj xA yA := by
    simpa [deleteEdgeEndsGraph, A, xA, yA] using hxy
  have hbyA : (deleteEdgeEndsGraph G p q).Adj bA yA := by
    simpa [deleteEdgeEndsGraph, A, bA, yA] using hby
  have hx_cycleA : xA ∉ cA.support := by
    intro hxA
    exact hx_cycle
      (Walk.mem_support_of_mem_induce_support
        (G := G) (S := A) c hcycle_avoids
        (x := xA) (by simpa [cA, A, xA] using hxA))
  have hy_cycleA : yA ∉ cA.support := by
    intro hyA
    exact hy_cycle
      (Walk.mem_support_of_mem_induce_support
        (G := G) (S := A) c hcycle_avoids
        (x := yA) (by simpa [cA, A, yA] using hyA))
  exact
    ContainsHomeomorphicTheta.of_edgeSubdivision
      (ContainsEdgeThetaSubdivision.of_cycle_adjacent_endpoint_path
        (G := deleteEdgeEndsGraph G p q)
        cA hcA haA hbA hzA habA hazA hbzA
        haxA hxyA hbyA hx_cycleA hy_cycleA)

/-- Source Lemma 1 mechanism for the mixed end-cycle theta. -/
theorem no_edge_disjoint_from_cycle_adjacent_endpoint_path_of_forall_deleteEdgeEnds_no_homeomorphicTheta
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {p q r a b z x y : V}
    (hpq : G.Adj p q)
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hcycle_avoids :
      forall w : V, w ∈ c.support -> w ∉ ({p, q} : Set V))
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hax : G.Adj a x)
    (hxy : G.Adj x y)
    (hby : G.Adj b y)
    (hx_cycle : x ∉ c.support)
    (hy_cycle : y ∉ c.support)
    (hx_avoids : x ∉ ({p, q} : Set V))
    (hy_avoids : y ∉ ({p, q} : Set V)) :
    False :=
  hno hpq
    (containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_adjacent_endpoint_path
      (G := G) c hc hcycle_avoids ha hb hz hab haz hbz
      hax hxy hby hx_cycle hy_cycle hx_avoids hy_avoids)

/-- Deleted-end form of the full two-endpoint attachment split: two distinct
vertices on the cycle, each attached to one endpoint of an external edge,
always leave a homeomorphic theta after deleting any disjoint edge endpoints. -/
theorem containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_two_endpoint_attachments
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {p q r a b z x y : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hcycle_avoids :
      forall w : V, w ∈ c.support -> w ∉ ({p, q} : Set V))
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
    (hx_avoids : x ∉ ({p, q} : Set V))
    (hy_avoids : y ∉ ({p, q} : Set V)) :
    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q) := by
  rcases ha_attach with hax | hay
  · rcases hb_attach with hbx | hby
    · exact
        containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_common_neighbor
          (G := G) c hc hcycle_avoids ha hb hz hab haz hbz
          hax hbx hx_cycle hx_avoids
    · exact
        containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_adjacent_endpoint_path
          (G := G) c hc hcycle_avoids ha hb hz hab haz hbz
          hax hxy hby hx_cycle hy_cycle hx_avoids hy_avoids
  · rcases hb_attach with hbx | hby
    · exact
        containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_adjacent_endpoint_path
          (G := G) c hc hcycle_avoids ha hb hz hab haz hbz
          hay hxy.symm hbx hy_cycle hx_cycle hy_avoids hx_avoids
    · exact
        containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_common_neighbor
          (G := G) c hc hcycle_avoids ha hb hz hab haz hbz
          hay hby hy_cycle hy_avoids

/-- Source Lemma 1 mechanism in the exact endpoint-assignment form used by the
Makarychev/Skopenkov hanging-cycle argument. -/
theorem no_edge_disjoint_from_cycle_two_endpoint_attachments_of_forall_deleteEdgeEnds_no_homeomorphicTheta
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {p q r a b z x y : V}
    (hpq : G.Adj p q)
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hcycle_avoids :
      forall w : V, w ∈ c.support -> w ∉ ({p, q} : Set V))
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
    (hx_avoids : x ∉ ({p, q} : Set V))
    (hy_avoids : y ∉ ({p, q} : Set V)) :
    False :=
  hno hpq
    (containsHomeomorphicTheta_deleteEdgeEndsGraph_of_cycle_two_endpoint_attachments
      (G := G) c hc hcycle_avoids ha hb hz hab haz hbz hxy
      ha_attach hb_attach hx_cycle hy_cycle hx_avoids hy_avoids)


end FourColor

end Schematic.Math.GraphTheory
