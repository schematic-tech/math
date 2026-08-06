import Schematic.Math.GraphTheory.Embedding.Wagner
import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion
import Schematic.Math.GraphTheory.Embedding.RotationSystemFan

/-!
The three-connected reconstruction step of Coq `planar/wagner.v`.

This module sits above both the strict-subdivision cycle obstruction and the
rotation-system vertex-deletion construction.  Keeping the reconstruction in
this separate layer prevents either lower module from importing the other.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

open RotationSystemVertexDeletion

namespace WagnerThree

/-- A specified neighbor can be removed from a degree-at-least-three
neighborhood while retaining two distinct neighbors. -/
theorem exists_two_neighbors_other_than
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (hxy : G.Adj x y)
    (hdegree : 3 <= G.degree x) :
    Exists fun x1 : V =>
      Exists fun x2 : V =>
        G.Adj x x1 ∧ G.Adj x x2 ∧
          x1 ≠ x2 ∧ x1 ≠ y ∧ x2 ≠ y := by
  classical
  let N := G.neighborFinset x
  have hyN : y ∈ N := by
    simpa [N] using hxy
  have hNcard : N.card = G.degree x := by
    exact SimpleGraph.card_neighborFinset_eq_degree G x
  have hcard : 1 < (N.erase y).card := by
    rw [Finset.card_erase_of_mem hyN, hNcard]
    omega
  rcases Finset.one_lt_card.mp hcard with
    ⟨x1, hx1, x2, hx2, hx1_ne_x2⟩
  have hx1' := Finset.mem_erase.mp hx1
  have hx2' := Finset.mem_erase.mp hx2
  refine ⟨x1, x2, ?_, ?_, hx1_ne_x2, hx1'.1, hx2'.1⟩
  · simpa [N] using hx1'.2
  · simpa [N] using hx2'.2

/-- The deleted-contraction embedding pulled back to the graph outside the
two endpoints of the contracted edge.  This retains the facial cycle instead
of forgetting it after mapping the cycle into the original graph. -/
structure EmbeddedMergedFaceCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (left right : V) where
  rotation : RotationSystem (G.induce (({left, right} : Set V)ᶜ))
  dualEulerPlanar : rotation.toHypermap.dual.EulerPlanar
  root : {z : V // z ∈ (({left, right} : Set V)ᶜ)}
  cycle : (G.induce (({left, right} : Set V)ᶜ)).Walk root root
  cycle_isCycle : cycle.IsCycle
  facial : RotationSystemGluing.IsFacialCycle rotation cycle cycle_isCycle
  left_neighbors :
    forall (z : V) (hzout : z ∉ ({left, right} : Set V)),
      G.Adj left z ->
        (⟨z, hzout⟩ : {w : V // w ∈ (({left, right} : Set V)ᶜ)}) ∈
          cycle.support
  right_neighbors :
    forall (z : V) (hzout : z ∉ ({left, right} : Set V)),
      G.Adj right z ->
        (⟨z, hzout⟩ : {w : V // w ∈ (({left, right} : Set V)ᶜ)}) ∈
          cycle.support

/-- Strengthened lift of the merged face from the contraction.  This is the
embedding-preserving form needed by the two `plane_add_node` calls in Coq
`wagner3`. -/
theorem mergedFaceCycle_lift_embedded
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hR : R.toHypermap.dual.EulerPlanar)
    (hnode : forall d : OrientedEdge
      (GraphContraction.collapseEdge G hab).graph, R.node d ≠ d)
    (u : {z : (GraphContraction.collapseEdge G hab).Target |
      z ≠ (none : (GraphContraction.collapseEdge G hab).Target)})
    (c : ((GraphContraction.collapseEdge G hab).graph.induce
      {z : (GraphContraction.collapseEdge G hab).Target |
        z ≠ (none : (GraphContraction.collapseEdge G hab).Target)}).Walk u u)
    (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle
      (vertexDeletedRotationSystem R
        (none : (GraphContraction.collapseEdge G hab).Target)) c hc)
    (hports :
      forall (x : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
        (hx : x.tail =
          (none : (GraphContraction.collapseEdge G hab).Target)),
        orientedEdgeDartEquiv
            (vertexDeletedFacePort R
              (none : (GraphContraction.collapseEdge G hab).Target)
              hnode x hx) ∈
          c.darts) :
    Nonempty (EmbeddedMergedFaceCycle G a b) := by
  classical
  let Q := GraphContraction.collapseEdge G hab
  let phi := GraphContraction.collapseEdgeOutsideIso G hab
  let D : RotationSystem
      (Q.graph.induce {z : Q.Target | z ≠ (none : Q.Target)}) :=
    vertexDeletedRotationSystem R (none : Q.Target)
  let Rout : RotationSystem (G.induce (({a, b} : Set V)ᶜ)) :=
    RotationSystem.ofIso phi D
  let cOutside := c.map phi.symm.toHom
  have hcOutside : cOutside.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.map
      (p := c) (f := phi.symm.toHom) phi.symm.toEquiv.injective hc
  have hfacialOutside :
      RotationSystemGluing.IsFacialCycle Rout cOutside hcOutside := by
    exact RotationSystemFan.isFacialCycle_ofIso phi D c hc hfacial
  have hDdual : D.toHypermap.dual.EulerPlanar := by
    exact vertexDeletedRotationSystem_dual_eulerPlanar
      R (none : Q.Target) hR
  have hRoutDual : Rout.toHypermap.dual.EulerPlanar := by
    let psi : Hypermap.Iso Rout.toHypermap D.toHypermap :=
      RotationSystem.ofIso_toHypermapIso phi D
    have hDprimal : D.toHypermap.EulerPlanar :=
      (D.toHypermap.dual_eulerPlanar_iff).mp hDdual
    have hRoutPrimal : Rout.toHypermap.EulerPlanar :=
      (psi.eulerPlanar_iff).mpr hDprimal
    exact (Rout.toHypermap.dual_eulerPlanar_iff).mpr hRoutPrimal
  have neighbor_mem
      (z : V) (hzout : z ∉ ({a, b} : Set V))
      (haz_or_hbz : G.Adj a z ∨ G.Adj b z) :
      (⟨z, hzout⟩ : {w : V // w ∈ (({a, b} : Set V)ᶜ)}) ∈
        cOutside.support := by
    let zOutside : {w : V // w ∈ (({a, b} : Set V)ᶜ)} := ⟨z, hzout⟩
    let qz : {q : Q.Target // q ≠ (none : Q.Target)} := phi zOutside
    have hqAdj : Q.graph.Adj (none : Q.Target) qz := by
      change
        (GraphContraction.collapseEdge G hab).graph.Adj none
          (GraphContraction.collapseEdgeOutside G hab z hzout)
      exact
        (GraphContraction.collapseEdge_adj_none_outside_iff G hab hzout).mpr
          haz_or_hbz
    let x : OrientedEdge Q.graph := ⟨((none : Q.Target), qz), hqAdj⟩
    have hx : x.tail = (none : Q.Target) := rfl
    let port := vertexDeletedFacePort R (none : Q.Target) hnode x hx
    have hportDart : orientedEdgeDartEquiv port ∈ c.darts := hports x hx
    have hportSupport : port.tail ∈ c.support := by
      change (orientedEdgeDartEquiv port).fst ∈ c.support
      exact c.dart_fst_mem_support_of_mem_darts hportDart
    have hportEq : port.tail = qz := by
      apply Subtype.ext
      exact vertexDeletedFacePort_tail_val R (none : Q.Target) hnode x hx
    change zOutside ∈ (c.map phi.symm.toHom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    refine ⟨port.tail, hportSupport, ?_⟩
    change phi.symm port.tail = zOutside
    rw [hportEq]
    exact phi.symm_apply_apply zOutside
  exact ⟨{
    rotation := Rout
    dualEulerPlanar := hRoutDual
    root := phi.symm u
    cycle := cOutside
    cycle_isCycle := hcOutside
    facial := hfacialOutside
    left_neighbors := fun z hzout haz => neighbor_mem z hzout (Or.inl haz)
    right_neighbors := fun z hzout hbz => neighbor_mem z hzout (Or.inr hbz)
  }⟩

/-- Lift the merged facial cycle of an edge contraction back through
`G - a - b = (G / ab) - [ab]`.  Every surviving neighbor of either endpoint
lies on the lifted cycle, while the two endpoints themselves do not. -/
theorem mergedFaceCycle_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hnode : forall d : OrientedEdge
      (GraphContraction.collapseEdge G hab).graph, R.node d ≠ d)
    (u : {z : (GraphContraction.collapseEdge G hab).Target |
      z ≠ (none : (GraphContraction.collapseEdge G hab).Target)})
    (c : ((GraphContraction.collapseEdge G hab).graph.induce
      {z : (GraphContraction.collapseEdge G hab).Target |
        z ≠ (none : (GraphContraction.collapseEdge G hab).Target)}).Walk u u)
    (hc : c.IsCycle)
    (hports :
      forall (x : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
        (hx : x.tail =
          (none : (GraphContraction.collapseEdge G hab).Target)),
        orientedEdgeDartEquiv
            (vertexDeletedFacePort R
              (none : (GraphContraction.collapseEdge G hab).Target)
              hnode x hx) ∈
          c.darts) :
    Exists fun r : V =>
      Exists fun C : G.Walk r r =>
        C.IsCycle ∧
          a ∉ C.support ∧
            b ∉ C.support ∧
              (forall z : V, G.Adj a z -> z ≠ b -> z ∈ C.support) ∧
                (forall z : V, G.Adj b z -> z ≠ a -> z ∈ C.support) := by
  classical
  let Q := GraphContraction.collapseEdge G hab
  let phi := GraphContraction.collapseEdgeOutsideIso G hab
  let includeOutside :=
    (SimpleGraph.Embedding.induce (G := G) (({a, b} : Set V)ᶜ)).toHom
  let cOutside := c.map phi.symm.toHom
  let C := cOutside.map includeOutside
  have hcOutside : cOutside.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.map
      (p := c) (f := phi.symm.toHom) phi.symm.toEquiv.injective hc
  have hC : C.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.map
      (p := cOutside) (f := includeOutside)
        (SimpleGraph.Embedding.induce
          (G := G) (({a, b} : Set V)ᶜ)).injective hcOutside
  have support_outside :
      forall z : V, z ∈ C.support -> z ∉ ({a, b} : Set V) := by
    intro z hz
    change z ∈ (cOutside.map includeOutside).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨zOutside, _hzOutside, rfl⟩
    exact zOutside.2
  have neighbor_mem
      (z : V) (hzout : z ∉ ({a, b} : Set V))
      (haz_or_hbz : G.Adj a z ∨ G.Adj b z) :
      z ∈ C.support := by
    let zOutside : {z : V // z ∈ (({a, b} : Set V)ᶜ)} := ⟨z, hzout⟩
    let qz : {q : Q.Target // q ≠ (none : Q.Target)} := phi zOutside
    have hqAdj : Q.graph.Adj (none : Q.Target) qz := by
      change
        (GraphContraction.collapseEdge G hab).graph.Adj none
          (GraphContraction.collapseEdgeOutside G hab z hzout)
      exact
        (GraphContraction.collapseEdge_adj_none_outside_iff G hab hzout).mpr
          haz_or_hbz
    let x : OrientedEdge Q.graph := ⟨((none : Q.Target), qz), hqAdj⟩
    have hx : x.tail = (none : Q.Target) := rfl
    let port := vertexDeletedFacePort R (none : Q.Target) hnode x hx
    have hportDart : orientedEdgeDartEquiv port ∈ c.darts := by
      exact hports x hx
    have hportSupport : port.tail ∈ c.support := by
      change (orientedEdgeDartEquiv port).fst ∈ c.support
      exact c.dart_fst_mem_support_of_mem_darts hportDart
    have hportEq : port.tail = qz := by
      apply Subtype.ext
      exact vertexDeletedFacePort_tail_val R (none : Q.Target) hnode x hx
    have hzOutside : zOutside ∈ cOutside.support := by
      change zOutside ∈ (c.map phi.symm.toHom).support
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      refine ⟨port.tail, hportSupport, ?_⟩
      change phi.symm port.tail = zOutside
      rw [hportEq]
      exact phi.symm_apply_apply zOutside
    change z ∈ (cOutside.map includeOutside).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨zOutside, hzOutside, rfl⟩
  refine ⟨(phi.symm u : V), C, hC, ?_, ?_, ?_, ?_⟩
  · intro ha
    exact support_outside a ha (by simp)
  · intro hb
    exact support_outside b hb (by simp)
  · intro z haz hzb
    have hzout : z ∉ ({a, b} : Set V) := by
      simpa [Set.mem_insert_iff] using And.intro haz.ne' hzb
    exact neighbor_mem z hzout (Or.inl haz)
  · intro z hbz hza
    have hzout : z ∉ ({a, b} : Set V) := by
      simpa [Set.mem_insert_iff] using And.intro hza hbz.ne'
    exact neighbor_mem z hzout (Or.inr hbz)

/-- The contractible-edge recursion supplies a boundary cycle in the original
graph carrying every surviving neighbor of both split endpoints.  This is the
graph-level output immediately before Coq `wagner3` invokes
`wagner_no_cross`. -/
theorem IsThreeConnected.exists_contractibleEdge_boundaryCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsThreeConnected G)
    (hcard : 4 < Nat.card V)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel
            (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        Exists fun R :
            RotationSystem (GraphContraction.collapseEdge G hab).graph =>
          (R.toHypermap).dual.EulerPlanar) :
    Exists fun a : V =>
      Exists fun b : V =>
        Exists fun hab : G.Adj a b =>
          letI : DecidableRel
              (GraphContraction.collapseEdge G hab).graph.Adj :=
            Classical.decRel _
          Exists fun _hthree :
              IsThreeConnected
                (GraphContraction.collapseEdge G hab).graph =>
            Exists fun R :
                RotationSystem
                  (GraphContraction.collapseEdge G hab).graph =>
              (R.toHypermap).dual.EulerPlanar ∧
                Exists fun r : V =>
                  Exists fun C : G.Walk r r =>
                    C.IsCycle ∧
                      a ∉ C.support ∧
                        b ∉ C.support ∧
                          (forall z : V,
                            G.Adj a z -> z ≠ b -> z ∈ C.support) ∧
                            (forall z : V,
                              G.Adj b z -> z ≠ a -> z ∈ C.support) := by
  classical
  rcases
      _root_.Schematic.Math.GraphTheory.FourColor.RotationSystemVertexDeletion.IsThreeConnected.exists_contractibleEdge_mergedFaceCycle
        hG hcard hcontract with
    ⟨a, b, hab, hthree, R, hR, u, c, hc, _hfacial, hports⟩
  refine ⟨a, b, hab, hthree, R, hR, ?_⟩
  exact mergedFaceCycle_lift hab R
    (node_ne_self_of_isTwoConnected R
      (IsKConnected.mono (by omega) hthree)) u c hc hports

/-- The boundary segment selected in Coq `wagner3`: all neighbors of the
right split endpoint occur on `arcs.first`, while no internal vertex of that
arc is adjacent to the left split endpoint. -/
structure BoundarySegment
    {V : Type u} (G : SimpleGraph V) (left right : V) where
  root : V
  cycle : G.Walk root root
  cycle_isCycle : cycle.IsCycle
  left_not_mem : left ∉ cycle.support
  right_not_mem : right ∉ cycle.support
  firstContact : V
  secondContact : V
  arcs : Wagner.CycleTwoArcs cycle
    (x1 := firstContact) (x2 := secondContact)
  left_adj_first : G.Adj left firstContact
  left_adj_second : G.Adj left secondContact
  right_neighbors_first :
    forall z : V, z ∈ cycle.support -> G.Adj right z ->
      z ∈ arcs.first.support
  no_left_neighbor_interior :
    forall z : V, z ∈ Walk.InternalVertices arcs.first ->
      ¬ G.Adj left z

/-- The boundary segment together with the actual recursive embedding on
`G - left - right`.  Its cycle in the original graph is definitionally the
image of the facial cycle stored by `merged`. -/
structure EmbeddedBoundarySegment
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (left right : V) where
  merged : EmbeddedMergedFaceCycle G left right
  firstContact : V
  secondContact : V
  arcs : Wagner.CycleTwoArcs
    (merged.cycle.map
      (SimpleGraph.Embedding.induce
        (G := G) (({left, right} : Set V)ᶜ)).toHom)
    (x1 := firstContact) (x2 := secondContact)
  left_adj_first : G.Adj left firstContact
  left_adj_second : G.Adj left secondContact
  right_neighbors_first :
    forall z : V,
      z ∈ (merged.cycle.map
        (SimpleGraph.Embedding.induce
          (G := G) (({left, right} : Set V)ᶜ)).toHom).support ->
      G.Adj right z -> z ∈ arcs.first.support
  no_left_neighbor_interior :
    forall z : V, z ∈ Walk.InternalVertices arcs.first ->
      ¬ G.Adj left z

/-- Pull an arc pair on the image of an induced cycle back to the induced
graph, retaining exact equations for both mapped paths. -/
theorem exists_inducedCycleTwoArcs
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {S : Set V}
    {r : S} (c : (G.induce S).Walk r r)
    {x1 x2 : V}
    (A : Wagner.CycleTwoArcs
      (c.map (SimpleGraph.Embedding.induce (G := G) S).toHom)
      (x1 := x1) (x2 := x2)) :
    Exists fun x1S : S =>
      Exists fun x2S : S =>
        Exists fun hx1 : (x1S : V) = x1 =>
          Exists fun hx2 : (x2S : V) = x2 =>
            Exists fun B : Wagner.CycleTwoArcs c (x1 := x1S) (x2 := x2S) =>
              (B.first.map
                  (SimpleGraph.Embedding.induce (G := G) S).toHom).copy
                    hx1 hx2 = A.first ∧
                (B.second.map
                  (SimpleGraph.Embedding.induce (G := G) S).toHom).copy
                    hx1 hx2 = A.second := by
  classical
  let inc := (SimpleGraph.Embedding.induce (G := G) S).toHom
  have hfirstS : forall z : V, z ∈ A.first.support -> z ∈ S := by
    intro z hz
    have hzC := A.first_support z hz
    change z ∈ (c.map inc).support at hzC
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzC
    rcases hzC with ⟨w, _hw, rfl⟩
    exact w.2
  have hsecondS : forall z : V, z ∈ A.second.support -> z ∈ S := by
    intro z hz
    have hzC := A.second_support z hz
    change z ∈ (c.map inc).support at hzC
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzC
    rcases hzC with ⟨w, _hw, rfl⟩
    exact w.2
  let x1S : S := ⟨x1, hfirstS x1 A.first.start_mem_support⟩
  let x2S : S := ⟨x2, hfirstS x2 A.first.end_mem_support⟩
  let p0 := A.first.induce S hfirstS
  let q0 := A.second.induce S hsecondS
  let p : (G.induce S).Walk x1S x2S :=
    p0.copy (Subtype.ext rfl) (Subtype.ext rfl)
  let q : (G.induce S).Walk x1S x2S :=
    q0.copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hpMap : p.map inc = A.first := by
    simp [p, p0, inc]
  have hqMap : q.map inc = A.second := by
    simp [q, q0, inc]
  have support_of_map_support
      (w : (G.induce S).Walk x1S x2S)
      (W : G.Walk x1 x2) (hwMap : w.map inc = W)
      {z : S} (hz : z ∈ w.support) : (z : V) ∈ W.support := by
    rw [← hwMap]
    have hlist : (z : V) ∈ w.support.map inc :=
      List.mem_map.mpr ⟨z, hz, rfl⟩
    exact (SimpleGraph.Walk.support_map (p := w) (f := inc)).symm ▸ hlist
  have cycle_support_of_mapped {z : S}
      (hz : (z : V) ∈ (c.map inc).support) : z ∈ c.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨w, hw, hwz⟩
    have hwEq : w = z := by
      apply Subtype.ext
      exact hwz
    simpa [hwEq] using hw
  have edge_of_mapped
      (w : (G.induce S).Walk x1S x2S)
      (W : G.Walk x1 x2) (hwMap : w.map inc = W)
      {e : Sym2 S} (he : Sym2.map inc e ∈ W.edges) :
      e ∈ w.edges := by
    rw [← hwMap] at he
    have heList : Sym2.map inc e ∈ w.edges.map (Sym2.map inc) := by
      exact SimpleGraph.Walk.edges_map (p := w) (f := inc) ▸ he
    rcases List.mem_map.mp heList with ⟨f, hf, hfe⟩
    have hEq : f = e :=
      (Sym2.map.injective
        (SimpleGraph.Embedding.induce (G := G) S).injective) hfe
    simpa [hEq] using hf
  have cycle_edge_of_mapped {e : Sym2 S}
      (he : Sym2.map inc e ∈ (c.map inc).edges) : e ∈ c.edges := by
    have heList : Sym2.map inc e ∈ c.edges.map (Sym2.map inc) := by
      exact SimpleGraph.Walk.edges_map (p := c) (f := inc) ▸ he
    rcases List.mem_map.mp heList with ⟨f, hf, hfe⟩
    have hEq : f = e :=
      (Sym2.map.injective
        (SimpleGraph.Embedding.induce (G := G) S).injective) hfe
    simpa [hEq] using hf
  let B : Wagner.CycleTwoArcs c (x1 := x1S) (x2 := x2S) := {
    first := p
    second := q
    endpoints_ne := by
      intro h
      exact A.endpoints_ne (congrArg Subtype.val h)
    first_isPath := by
      apply SimpleGraph.Walk.IsPath.of_map (f := inc)
      rw [hpMap]
      exact A.first_isPath
    second_isPath := by
      apply SimpleGraph.Walk.IsPath.of_map (f := inc)
      rw [hqMap]
      exact A.second_isPath
    first_support := by
      intro z hz
      apply cycle_support_of_mapped
      exact A.first_support (z : V)
        (support_of_map_support p A.first hpMap hz)
    second_support := by
      intro z hz
      apply cycle_support_of_mapped
      exact A.second_support (z : V)
        (support_of_map_support q A.second hqMap hz)
    first_edges := by
      intro e he
      apply cycle_edge_of_mapped
      exact A.first_edges (Sym2.map inc e) (by
        rw [← hpMap]
        have heList : Sym2.map inc e ∈ p.edges.map (Sym2.map inc) :=
          List.mem_map.mpr ⟨e, he, rfl⟩
        exact (SimpleGraph.Walk.edges_map (p := p) (f := inc)).symm ▸ heList)
    second_edges := by
      intro e he
      apply cycle_edge_of_mapped
      exact A.second_edges (Sym2.map inc e) (by
        rw [← hqMap]
        have heList : Sym2.map inc e ∈ q.edges.map (Sym2.map inc) :=
          List.mem_map.mpr ⟨e, he, rfl⟩
        exact (SimpleGraph.Walk.edges_map (p := q) (f := inc)).symm ▸ heList)
    internally_disjoint := by
      rw [Set.disjoint_left]
      intro z hzp hzq
      have hzpMap : (z : V) ∈ Walk.InternalVertices A.first := by
        rw [← hpMap]
        exact (Walk.mem_internalVertices_map_iff_of_injective
          inc
          (SimpleGraph.Embedding.induce (G := G) S).injective p).mpr
          ⟨z, hzp, rfl⟩
      have hzqMap : (z : V) ∈ Walk.InternalVertices A.second := by
        rw [← hqMap]
        exact (Walk.mem_internalVertices_map_iff_of_injective
          inc
          (SimpleGraph.Embedding.induce (G := G) S).injective q).mpr
          ⟨z, hzq, rfl⟩
      exact Set.disjoint_left.mp A.internally_disjoint hzpMap hzqMap
    cover := by
      intro z hzC
      have hzMap : (z : V) ∈ (c.map inc).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨z, hzC, rfl⟩
      rcases A.cover (z : V) hzMap with hzFirst | hzSecond
      · left
        rw [← hpMap] at hzFirst
        have hzList : (z : V) ∈ p.support.map inc := by
          exact SimpleGraph.Walk.support_map (p := p) (f := inc) ▸ hzFirst
        rcases List.mem_map.mp hzList with ⟨w, hw, hwz⟩
        have hwEq : w = z := by
          apply Subtype.ext
          exact hwz
        simpa [hwEq] using hw
      · right
        rw [← hqMap] at hzSecond
        have hzList : (z : V) ∈ q.support.map inc := by
          exact SimpleGraph.Walk.support_map (p := q) (f := inc) ▸ hzSecond
        rcases List.mem_map.mp hzList with ⟨w, hw, hwz⟩
        have hwEq : w = z := by
          apply Subtype.ext
          exact hwz
        simpa [hwEq] using hw
  }
  exact ⟨x1S, x2S, rfl, rfl, B, hpMap, hqMap⟩

/-- The selected segment entirely on the embedded outside graph. -/
structure OutsideBoundarySegment
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (left right : V) where
  merged : EmbeddedMergedFaceCycle G left right
  firstContact : {z : V // z ∈ (({left, right} : Set V)ᶜ)}
  secondContact : {z : V // z ∈ (({left, right} : Set V)ᶜ)}
  arcs : Wagner.CycleTwoArcs merged.cycle
    (x1 := firstContact) (x2 := secondContact)
  left_adj_first : G.Adj left firstContact
  left_adj_second : G.Adj left secondContact
  right_neighbors_first :
    forall z : {w : V // w ∈ (({left, right} : Set V)ᶜ)},
      G.Adj right z -> z ∈ arcs.first.support
  no_left_neighbor_interior :
    forall z : {w : V // w ∈ (({left, right} : Set V)ᶜ)},
      z ∈ Walk.InternalVertices arcs.first -> ¬ G.Adj left z

/-- Pull the mapped `wagner_no_cross` segment back to the same outside graph
that carries the recursive rotation system. -/
theorem EmbeddedBoundarySegment.exists_outsideBoundarySegment
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {left right : V}
    (E : EmbeddedBoundarySegment G left right) :
    Nonempty (OutsideBoundarySegment G left right) := by
  classical
  let S : Set V := (({left, right} : Set V)ᶜ)
  let inc := (SimpleGraph.Embedding.induce (G := G) S).toHom
  rcases exists_inducedCycleTwoArcs E.merged.cycle E.arcs with
    ⟨x1, x2, hx1, hx2, A, hfirstMap, _hsecondMap⟩
  have cycle_map_mem {z : S} (hz : z ∈ E.merged.cycle.support) :
      (z : V) ∈ (E.merged.cycle.map inc).support := by
    have hzList : (z : V) ∈ E.merged.cycle.support.map inc :=
      List.mem_map.mpr ⟨z, hz, rfl⟩
    exact (SimpleGraph.Walk.support_map
      (p := E.merged.cycle) (f := inc)).symm ▸ hzList
  have first_support_of_mapped {z : S}
      (hz : (z : V) ∈
        ((A.first.map inc).copy hx1 hx2).support) :
      z ∈ A.first.support := by
    have hzMap : (z : V) ∈ (A.first.map inc).support := by
      simpa using hz
    have hzList : (z : V) ∈ A.first.support.map inc :=
      SimpleGraph.Walk.support_map (p := A.first) (f := inc) ▸ hzMap
    rcases List.mem_map.mp hzList with ⟨w, hw, hwz⟩
    have hwEq : w = z := by
      apply Subtype.ext
      exact hwz
    simpa [hwEq] using hw
  refine ⟨{
    merged := E.merged
    firstContact := x1
    secondContact := x2
    arcs := A
    left_adj_first := by simpa [hx1] using E.left_adj_first
    left_adj_second := by simpa [hx2] using E.left_adj_second
    right_neighbors_first := ?_
    no_left_neighbor_interior := ?_
  }⟩
  · intro z hrz
    have hzCycleMap := cycle_map_mem
      (E.merged.right_neighbors z z.2 hrz)
    have hzOriginal : (z : V) ∈ E.arcs.first.support :=
      E.right_neighbors_first (z : V) hzCycleMap hrz
    rw [← hfirstMap] at hzOriginal
    exact first_support_of_mapped hzOriginal
  · intro z hz
    have hzMap : (z : V) ∈ Walk.InternalVertices (A.first.map inc) :=
      (Walk.mem_internalVertices_map_iff_of_injective
        inc (SimpleGraph.Embedding.induce (G := G) S).injective A.first).mpr
        ⟨z, hz, rfl⟩
    have hzCopy : (z : V) ∈
        Walk.InternalVertices ((A.first.map inc).copy hx1 hx2) :=
      (Walk.mem_internalVertices_copy_iff (A.first.map inc) hx1 hx2).mpr
        hzMap
    rw [hfirstMap] at hzCopy
    exact E.no_left_neighbor_interior (z : V) hzCopy

/-- Neighbors of the left split endpoint among the vertices outside both
endpoints. -/
def leftNeighborSet
    {V : Type u} (G : SimpleGraph V) (left right : V) :
    Set {z : V // z ∈ (({left, right} : Set V)ᶜ)} :=
  {z | G.Adj left z}

/-- Neighbors of the right split endpoint after the left endpoint has been
reinserted as `none`.  The inner `none` is always selected because the two
split endpoints are adjacent. -/
def rightNeighborSetAfterLeft
    {V : Type u} (G : SimpleGraph V) (right : V) {S : Set V} :
    Set (Option S) :=
  {z | match z with
    | none => True
    | some w => G.Adj right w}

/-- Coq `wagner3`'s final `fwd`/`bwd` isomorphism: adding `left` and then
`right` to the outside induced graph reconstructs the original graph. -/
noncomputable def addSplitEndpointsIso
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (left right : V) (hlr : G.Adj left right) :
    RotationSystemFan.addNodeGraph
        (RotationSystemFan.addNodeGraph
          (G.induce (({left, right} : Set V)ᶜ))
          (leftNeighborSet G left right))
        (rightNeighborSetAfterLeft G right) ≃g
      G where
  toFun
    | none => right
    | some none => left
    | some (some z) => z
  invFun z :=
    if hzr : z = right then none
    else if hzl : z = left then some none
    else some (some ⟨z, by simp [hzl, hzr]⟩)
  left_inv := by
    intro z
    rcases z with _ | z
    · simp
    · rcases z with _ | z
      · simp [hlr.ne]
      · have hzl : (z : V) ≠ left := by
          intro hz
          exact z.2 (by simp [hz])
        have hzr : (z : V) ≠ right := by
          intro hz
          exact z.2 (by simp [hz])
        simp [hzl, hzr]
  right_inv := by
    intro z
    by_cases hzr : z = right
    · simp [hzr]
    · by_cases hzl : z = left
      · subst z
        simp [hlr.ne]
      · simp [hzr, hzl]
  map_rel_iff' := by
    intro x y
    rcases x with (_ | (_ | x)) <;> rcases y with (_ | (_ | y)) <;>
      simp [RotationSystemFan.addNodeGraph, leftNeighborSet,
        rightNeighborSetAfterLeft, hlr]
    all_goals
      first
      | exact hlr.symm
      | exact G.adj_comm _ _

/-- The first `wagner3` add-node call.  The selected clean arc is retained as
a vertex-simple face, independently of which of the two cyclic orientations
realizes `CycleTwoArcs.first`. -/
theorem OutsideBoundarySegment.exists_addLeftAlongFirstArc
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {left right : V}
    (E : OutsideBoundarySegment G left right) :
    let H := G.induce (({left, right} : Set V)ᶜ)
    let A := leftNeighborSet G left right
    letI : DecidableRel (RotationSystemFan.addNodeGraph H A).Adj :=
      Classical.decRel _
    Exists fun S : RotationSystem (RotationSystemFan.addNodeGraph H A) =>
      S.toHypermap.dual.EulerPlanar ∧
        Exists fun B : RotationSystemFan.FaceBoundary S.toHypermap =>
          B.first.tail = none ∧
            ((B.first :: B.rest).map OrientedEdge.tail).Nodup ∧
              forall z, z ∈ E.arcs.first.support ->
                Exists fun d : OrientedEdge
                    (RotationSystemFan.addNodeGraph H A) =>
                  d ∈ B.first :: B.rest ∧ d.tail = some z := by
  classical
  let H := G.induce (({left, right} : Set V)ᶜ)
  let A := leftNeighborSet G left right
  let x1 := E.firstContact
  let x2 := E.secondContact
  let C := E.merged.cycle
  let hx1C : x1 ∈ C.support :=
    E.arcs.first_support x1 E.arcs.first.start_mem_support
  let C' : H.Walk x1 x1 := C.rotate x1 hx1C
  have hC' : C'.IsCycle := by
    simpa [C'] using SimpleGraph.Walk.IsCycle.rotate hx1C
      E.merged.cycle_isCycle
  have hfacial' :
      RotationSystemGluing.IsFacialCycle E.merged.rotation C' hC' := by
    exact RotationSystemFan.isFacialCycle_rotate E.merged.rotation C
      E.merged.cycle_isCycle E.merged.facial x1 hx1C
  let hx2C' : x2 ∈ C'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1C).mpr
      (E.arcs.first_support x2 E.arcs.first.end_mem_support)
  let P : H.Walk x1 x2 := C'.takeUntil x2 hx2C'
  let D : H.Walk x2 x1 := C'.dropUntil x2 hx2C'
  have hP : P.IsPath := by
    simpa [P] using hC'.isPath_takeUntil hx2C'
  have hPNotNil : ¬ P.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := P) E.arcs.endpoints_ne
  have hD : D.IsPath := by
    have hcycle : (P.append D).IsCycle := by
      simpa [P, D, SimpleGraph.Walk.take_spec C' hx2C'] using hC'
    exact hcycle.isPath_of_append_right hPNotNil
  have hchoice : E.arcs.first = P ∨ E.arcs.first = D.reverse := by
    simpa [x1, x2, C, hx1C, C', hx2C', P, D] using
      E.arcs.first_eq_forward_or_reverse_dropUntil
        E.merged.cycle_isCycle E.arcs.endpoints_ne
  rcases hchoice with hforward | hbackward
  · let C'' : H.Walk x2 x2 := C'.rotate x2 hx2C'
    have hC'' : C''.IsCycle := by
      simpa [C''] using SimpleGraph.Walk.IsCycle.rotate hx2C' hC'
    have hfacial'' :
        RotationSystemGluing.IsFacialCycle E.merged.rotation C'' hC'' := by
      exact RotationSystemFan.isFacialCycle_rotate E.merged.rotation C'
        hC' hfacial' x2 hx2C'
    have hcycle'' : C'' = D.append P := by
      rfl
    have hx2A : x2 ∈ A := by
      exact E.left_adj_second
    have hx1A : x1 ∈ A := by
      exact E.left_adj_first
    have hcoverA : forall z, z ∈ A -> z ∈ C''.support := by
      intro z hz
      have hzC : z ∈ C.support :=
        E.merged.left_neighbors z z.2 hz
      have hzC' : z ∈ C'.support :=
        (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1C).mpr hzC
      exact (SimpleGraph.Walk.mem_support_rotate_iff C' x2 hx2C').mpr hzC'
    have hcleanP : forall z, z ∈ Walk.InternalVertices P -> z ∉ A := by
      intro z hz hzA
      apply E.no_left_neighbor_interior z
      · rw [hforward]
        exact hz
      · exact hzA
    rcases RotationSystemFan.exists_addNodeGraph_preserving_clean_gap
        A E.merged.rotation E.merged.dualEulerPlanar C'' hC'' hfacial''
        D P hcycle'' hP E.arcs.endpoints_ne.symm hx2A hx1A
        hcoverA hcleanP with
      ⟨S, hS, B, hBfirst, hBnodup, hBcover⟩
    refine ⟨S, hS, B, hBfirst, hBnodup, ?_⟩
    intro z hz
    exact hBcover z (by simpa [hforward] using hz)
  · have hcycle' : C' = P.append D :=
      (SimpleGraph.Walk.take_spec C' hx2C').symm
    have hx1A : x1 ∈ A := by
      exact E.left_adj_first
    have hx2A : x2 ∈ A := by
      exact E.left_adj_second
    have hcoverA : forall z, z ∈ A -> z ∈ C'.support := by
      intro z hz
      have hzC : z ∈ C.support :=
        E.merged.left_neighbors z z.2 hz
      exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1C).mpr hzC
    have hcleanD : forall z, z ∈ Walk.InternalVertices D -> z ∉ A := by
      intro z hz hzA
      apply E.no_left_neighbor_interior z
      · rw [hbackward]
        exact (Walk.mem_internalVertices_reverse_iff D).mpr hz
      · exact hzA
    rcases RotationSystemFan.exists_addNodeGraph_preserving_clean_gap
        A E.merged.rotation E.merged.dualEulerPlanar C' hC' hfacial'
        P D hcycle' hD E.arcs.endpoints_ne hx1A hx2A
        hcoverA hcleanD with
      ⟨S, hS, B, hBfirst, hBnodup, hBcover⟩
    refine ⟨S, hS, B, hBfirst, hBnodup, ?_⟩
    intro z hz
    apply hBcover z
    have hzReverse : z ∈ D.reverse.support := by simpa [hbackward] using hz
    rw [SimpleGraph.Walk.support_reverse] at hzReverse
    exact List.mem_reverse.mp hzReverse

/-- The two Coq add-node calls, followed by its explicit `fwd`/`bwd`
isomorphism, reconstruct an Euler-planar rotation system on the original
three-connected graph. -/
theorem OutsideBoundarySegment.hasEulerRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {left right : V}
    (E : OutsideBoundarySegment G left right)
    (hlr : G.Adj left right) :
    HasEulerRotationSystem G := by
  classical
  let H := G.induce (({left, right} : Set V)ᶜ)
  let A := leftNeighborSet G left right
  let Gleft := RotationSystemFan.addNodeGraph H A
  let Aright : Set (Option {z : V // z ∈ (({left, right} : Set V)ᶜ)}) :=
    rightNeighborSetAfterLeft G right
  letI : DecidableRel Gleft.Adj := Classical.decRel _
  rcases E.exists_addLeftAlongFirstArc with
    ⟨Rleft, hRleft, B, hBfirst, hBnodup, hBcover⟩
  have hnone :
      (none : Option {z : V // z ∈ (({left, right} : Set V)ᶜ)}) ∈
        Aright := by
    simp [Aright, rightNeighborSetAfterLeft]
  have hcoverRight : forall z, z ∈ Aright ->
      Exists fun d : OrientedEdge Gleft =>
        d ∈ B.first :: B.rest ∧ d.tail = z := by
    intro z hz
    rcases z with _ | z
    · exact ⟨B.first, List.mem_cons_self, hBfirst⟩
    · have hrz : G.Adj right z := by
        simpa [Aright, rightNeighborSetAfterLeft] using hz
      exact hBcover z (E.right_neighbors_first z hrz)
  letI : DecidableRel (RotationSystemFan.addNodeGraph Gleft Aright).Adj :=
    Classical.decRel _
  rcases RotationSystemFan.exists_addNodeGraph_simple
      Aright
      (none : Option {z : V // z ∈ (({left, right} : Set V)ᶜ)})
      hnone Rleft hRleft B hBfirst
      hcoverRight hBnodup with ⟨Rboth, hRboth⟩
  let phi := addSplitEndpointsIso G left right hlr
  exact HasEulerRotationSystem.of_iso phi.symm ⟨Rboth, hRboth⟩

/-- Embedding-preserving form of the complete `wagner_no_cross` step. -/
theorem IsThreeConnected.exists_contractibleEdge_embeddedBoundarySegment
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsThreeConnected G)
    (hplanar : IsPlanar G)
    (hcard : 4 < Nat.card V)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel
            (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        Exists fun R :
            RotationSystem (GraphContraction.collapseEdge G hab).graph =>
          R.toHypermap.dual.EulerPlanar) :
    Exists fun a : V =>
      Exists fun b : V =>
        Exists fun _hab : G.Adj a b =>
          Nonempty (EmbeddedBoundarySegment G a b) := by
  classical
  rcases
      _root_.Schematic.Math.GraphTheory.FourColor.RotationSystemVertexDeletion.IsThreeConnected.exists_contractibleEdge_mergedFaceCycle
        hG hcard hcontract with
    ⟨a, b, hab, hthree, R, hR, u, c, hc, hfacial, hports⟩
  letI : DecidableRel
      (GraphContraction.collapseEdge G hab).graph.Adj := Classical.decRel _
  have hnode : forall d : OrientedEdge
      (GraphContraction.collapseEdge G hab).graph, R.node d ≠ d :=
    node_ne_self_of_isTwoConnected R
      (IsKConnected.mono (by omega) hthree)
  rcases mergedFaceCycle_lift_embedded hab R hR hnode u c hc hfacial hports with
    ⟨E⟩
  let includeOutside :=
    (SimpleGraph.Embedding.induce
      (G := G) (({a, b} : Set V)ᶜ)).toHom
  let C := E.cycle.map includeOutside
  have hC : C.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.map
      (p := E.cycle) (f := includeOutside)
        (SimpleGraph.Embedding.induce
          (G := G) (({a, b} : Set V)ᶜ)).injective E.cycle_isCycle
  have support_outside :
      forall z : V, z ∈ C.support -> z ∉ ({a, b} : Set V) := by
    intro z hz
    change z ∈ (E.cycle.map includeOutside).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨zOutside, _hzOutside, rfl⟩
    exact zOutside.2
  have hallA :
      forall z : V, G.Adj a z -> z ≠ b -> z ∈ C.support := by
    intro z haz hzb
    have hzout : z ∉ ({a, b} : Set V) := by
      simpa [Set.mem_insert_iff] using And.intro haz.ne' hzb
    have hzE := E.left_neighbors z hzout haz
    change z ∈ (E.cycle.map includeOutside).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨⟨z, hzout⟩, hzE, rfl⟩
  have hallB :
      forall z : V, G.Adj b z -> z ≠ a -> z ∈ C.support := by
    intro z hbz hza
    have hzout : z ∉ ({a, b} : Set V) := by
      simpa [Set.mem_insert_iff] using And.intro hza hbz.ne'
    have hzE := E.right_neighbors z hzout hbz
    change z ∈ (E.cycle.map includeOutside).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨⟨z, hzout⟩, hzE, rfl⟩
  have haC : a ∉ C.support := by
    intro ha
    exact support_outside a ha (by simp)
  have hbC : b ∉ C.support := by
    intro hb
    exact support_outside b hb (by simp)
  have hdegA : 3 <= G.degree a :=
    _root_.Schematic.Math.GraphTheory.IsKConnected.degree_atLeast hG a
  have hdegB : 3 <= G.degree b :=
    _root_.Schematic.Math.GraphTheory.IsKConnected.degree_atLeast hG b
  rcases exists_two_neighbors_other_than hab hdegA with
    ⟨a1, a2, haa1, haa2, ha1_ne_a2, ha1_ne_b, ha2_ne_b⟩
  rcases exists_two_neighbors_other_than hab.symm hdegB with
    ⟨b1, b2, hbb1, hbb2, hb1_ne_b2, hb1_ne_a, hb2_ne_a⟩
  have ha1C : a1 ∈ C.support := hallA a1 haa1 ha1_ne_b
  have ha2C : a2 ∈ C.support := hallA a2 haa2 ha2_ne_b
  have hb1C : b1 ∈ C.support := hallB b1 hbb1 hb1_ne_a
  have hb2C : b2 ∈ C.support := hallB b2 hbb2 hb2_ne_a
  rcases Wagner.IsPlanar.wagner_no_cross hplanar C hC
      ha1C ha2C ha1_ne_a2 haa1 haa2
      hb1C hb2C hb1_ne_b2 hbb1 hbb2 hab haC hbC with
    ⟨x, y, A, hax, hay, hallBFirst, hnoAInterior⟩
  refine ⟨a, b, hab, ⟨{
    merged := E
    firstContact := x
    secondContact := y
    arcs := A
    left_adj_first := hax
    left_adj_second := hay
    right_neighbors_first := ?_
    no_left_neighbor_interior := hnoAInterior
  }⟩⟩
  intro z hz hbz
  exact hallBFirst z hz hbz

/-- Complete Coq `wagner3`: a planar three-connected graph on at least five
vertices is Euler-embeddable once the recursively smaller edge contractions
are Euler-embeddable. -/
theorem IsThreeConnected.hasEulerRotationSystem_of_contractibleEdge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsThreeConnected G)
    (hplanar : IsPlanar G)
    (hcard : 4 < Nat.card V)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel
            (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        HasEulerRotationSystem
          (GraphContraction.collapseEdge G hab).graph) :
    HasEulerRotationSystem G := by
  classical
  have hcontractRotation :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel
            (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        Exists fun R :
            RotationSystem (GraphContraction.collapseEdge G hab).graph =>
          R.toHypermap.dual.EulerPlanar := by
    intro a b hab
    exact hcontract hab
  rcases IsThreeConnected.exists_contractibleEdge_embeddedBoundarySegment
      hG hplanar hcard hcontractRotation with ⟨a, b, hab, ⟨E⟩⟩
  rcases E.exists_outsideBoundarySegment with ⟨O⟩
  exact O.hasEulerRotationSystem hab

/-- Coq `wagner3` through the complete `wagner_no_cross` call.  The recursive
embedding of the contractible collapse and the selected facial segment are
returned together for the two add-node reconstruction steps. -/
theorem IsThreeConnected.exists_contractibleEdge_boundarySegment
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsThreeConnected G)
    (hplanar : IsPlanar G)
    (hcard : 4 < Nat.card V)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel
            (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        Exists fun R :
            RotationSystem (GraphContraction.collapseEdge G hab).graph =>
          (R.toHypermap).dual.EulerPlanar) :
    Exists fun a : V =>
      Exists fun b : V =>
        Exists fun hab : G.Adj a b =>
          letI : DecidableRel
              (GraphContraction.collapseEdge G hab).graph.Adj :=
            Classical.decRel _
          Exists fun R :
              RotationSystem
                (GraphContraction.collapseEdge G hab).graph =>
            (R.toHypermap).dual.EulerPlanar ∧
              Nonempty (BoundarySegment G a b) := by
  classical
  rcases
      _root_.Schematic.Math.GraphTheory.FourColor.WagnerThree.IsThreeConnected.exists_contractibleEdge_boundaryCycle
        hG hcard hcontract with
    ⟨a, b, hab, _hthree, R, hR, r, C, hC, haC, hbC, hallA, hallB⟩
  have hdegA : 3 <= G.degree a :=
    _root_.Schematic.Math.GraphTheory.IsKConnected.degree_atLeast hG a
  have hdegB : 3 <= G.degree b :=
    _root_.Schematic.Math.GraphTheory.IsKConnected.degree_atLeast hG b
  rcases exists_two_neighbors_other_than hab hdegA with
    ⟨a1, a2, haa1, haa2, ha1_ne_a2, ha1_ne_b, ha2_ne_b⟩
  rcases exists_two_neighbors_other_than hab.symm hdegB with
    ⟨b1, b2, hbb1, hbb2, hb1_ne_b2, hb1_ne_a, hb2_ne_a⟩
  have ha1C : a1 ∈ C.support := hallA a1 haa1 ha1_ne_b
  have ha2C : a2 ∈ C.support := hallA a2 haa2 ha2_ne_b
  have hb1C : b1 ∈ C.support := hallB b1 hbb1 hb1_ne_a
  have hb2C : b2 ∈ C.support := hallB b2 hbb2 hb2_ne_a
  rcases Wagner.IsPlanar.wagner_no_cross hplanar C hC
      ha1C ha2C ha1_ne_a2 haa1 haa2
      hb1C hb2C hb1_ne_b2 hbb1 hbb2 hab haC hbC with
    ⟨u, v, A, hau, hav, hallBFirst, hnoAInterior⟩
  refine ⟨a, b, hab, R, hR, ⟨?_⟩⟩
  exact {
    root := r
    cycle := C
    cycle_isCycle := hC
    left_not_mem := haC
    right_not_mem := hbC
    firstContact := u
    secondContact := v
    arcs := A
    left_adj_first := hau
    left_adj_second := hav
    right_neighbors_first := hallBFirst
    no_left_neighbor_interior := hnoAInterior
  }

end WagnerThree

end FourColor

end Schematic.Math.GraphTheory
