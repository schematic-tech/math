import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Rotation.Components

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Standard finite forest count:
`|E| + number_of_components <= |V|`.  For an acyclic graph every connected
component is a tree, and the component vertex/edge decompositions above sum
the tree equalities. -/
theorem edgeFinset_card_add_connectedComponent_card_le_card_of_isAcyclic
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) :
    G.edgeFinset.card + Nat.card G.ConnectedComponent <= Fintype.card V := by
  classical
  letI (C : G.ConnectedComponent) : Fintype C := C.supp.toFinite.fintype
  haveI (C : G.ConnectedComponent) :
      DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have hedge := edgeFinset_card_eq_sum_connectedComponent_edgeSet_natCard (G := G)
  have hverts := card_eq_sum_connectedComponent_natCard (G := G)
  rw [hedge, hverts, Nat.card_eq_fintype_card]
  have hsum_tree :
      (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) +
          Fintype.card G.ConnectedComponent =
        ∑ C : G.ConnectedComponent, Nat.card C := by
    calc
      (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) +
          Fintype.card G.ConnectedComponent =
          (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) +
            ∑ _C : G.ConnectedComponent, (1 : Nat) := by
            simp
      _ = ∑ C : G.ConnectedComponent,
            (Nat.card C.toSimpleGraph.edgeSet + 1) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ C : G.ConnectedComponent, Nat.card C := by
            apply Finset.sum_congr rfl
            intro C _
            have htree := hacyclic.isTree_connectedComponent C
            have h := htree.card_edgeFinset
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
              SimpleGraph.card_edgeSet]
            exact h
  omega

/-- Forest count on the non-isolated support, in the exact form consumed by
the rotation-system Euler-count bridge. -/
theorem edgeFinset_card_add_supportComponent_card_le_support_card_of_isAcyclic
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) :
    G.edgeFinset.card + Nat.card (G.induce G.support).ConnectedComponent <=
      Fintype.card G.support := by
  classical
  let H : SimpleGraph G.support := G.induce G.support
  have hHacyclic : H.IsAcyclic := hacyclic.induce G.support
  have hforest :=
    edgeFinset_card_add_connectedComponent_card_le_card_of_isAcyclic
      (G := H) hHacyclic
  have hedge : H.edgeFinset.card = G.edgeFinset.card := by
    simpa [H] using SimpleGraph.card_edgeFinset_induce_support (G := G)
  simpa [H, hedge] using hforest

/-- The connected components of the non-isolated support are represented by
support vertices, so their number is at most the support size.  This is the
global counting input needed when the connected degree-two rotation endpoint is
lifted componentwise. -/
theorem support_connectedComponent_card_le_support_card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    Nat.card (G.induce G.support).ConnectedComponent <=
      Fintype.card G.support := by
  classical
  let H : SimpleGraph G.support := G.induce G.support
  let f : G.support -> H.ConnectedComponent :=
    fun x => H.connectedComponentMk x
  have hf : Function.Surjective f := by
    intro C
    refine SimpleGraph.ConnectedComponent.ind ?_ C
    intro x
    exact ⟨x, rfl⟩
  have hcard := Fintype.card_le_of_surjective f hf
  simpa [H, Nat.card_eq_fintype_card] using hcard

/-- Every connected component of the non-isolated support has at least two
vertices.  A support vertex has a neighbour, and that neighbour is again in the
support and in the same support component. -/
theorem support_connectedComponent_nontrivial
    {V : Type u} {G : SimpleGraph V}
    (C : (G.induce G.support).ConnectedComponent) :
    Nontrivial C := by
  classical
  let H : SimpleGraph G.support := G.induce G.support
  obtain ⟨x, hxC⟩ := C.nonempty_supp
  rcases (SimpleGraph.mem_support (G := G)).mp x.property with ⟨y, hxy⟩
  have hy_support : y ∈ G.support :=
    (SimpleGraph.mem_support (G := G)).mpr ⟨(x : V), hxy.symm⟩
  let yS : G.support := ⟨y, hy_support⟩
  have hxyH : H.Adj x yS := by
    exact hxy
  have hyC : yS ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp hxC hxyH
  refine ⟨⟨x, hxC⟩, ⟨yS, hyC⟩, ?_⟩
  intro h
  have hxy_eq : (x : V) = y :=
    congrArg Subtype.val (congrArg Subtype.val h)
  exact hxy.ne hxy_eq

/-- For a component of the non-isolated support, the degree of a component
vertex is the same as its degree in the original graph. -/
theorem support_connectedComponent_degree_eq
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : (G.induce G.support).ConnectedComponent)
    [Fintype C] [DecidableRel C.toSimpleGraph.Adj]
    (v : C) :
    G.degree ((v : G.support) : V) = C.toSimpleGraph.degree v := by
  rw [← SimpleGraph.degree_induce_support (G := G) (v := (v : G.support))]
  exact connectedComponent_degree_eq C v

/-- If a support component contains no original-graph simple cycle, then its
component graph is acyclic. -/
theorem support_connectedComponent_toSimpleGraph_isAcyclic_of_no_cycle
    {V : Type u} {G : SimpleGraph V}
    (C : (G.induce G.support).ConnectedComponent)
    (hno :
      ¬ Exists fun u : V =>
        Exists fun hu : u ∈ G.support =>
          (⟨u, hu⟩ : G.support) ∈ C.supp ∧
            Exists fun c : G.Walk u u => c.IsCycle) :
    C.toSimpleGraph.IsAcyclic := by
  classical
  intro z c hc
  let φSupport : (G.induce G.support) →g G :=
    (SimpleGraph.Embedding.induce (G := G) G.support).toHom
  let φ : C.toSimpleGraph →g G := φSupport.comp C.toSimpleGraph_hom
  have hφ_injective : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hcG : (c.map φ).IsCycle :=
    SimpleGraph.Walk.IsCycle.map (p := c) (f := φ) hφ_injective hc
  exact hno
    ⟨((z : G.support) : V), (z : G.support).property, z.property,
      c.map φ, hcG⟩

/-- A non-cyclic support component has two distinct original degree-one
endpoints.  This is the graph-side leaf step for the mixed path/cycle bridge. -/
theorem support_connectedComponent_exists_two_degree_le_one_of_no_cycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : (G.induce G.support).ConnectedComponent)
    (hno :
      ¬ Exists fun u : V =>
        Exists fun hu : u ∈ G.support =>
          (⟨u, hu⟩ : G.support) ∈ C.supp ∧
            Exists fun c : G.Walk u u => c.IsCycle) :
    Exists fun a : G.support =>
      Exists fun b : G.support =>
        a ∈ C.supp ∧ b ∈ C.supp ∧ a ≠ b ∧
          G.degree (a : V) <= 1 ∧ G.degree (b : V) <= 1 := by
  classical
  letI : Fintype C := C.supp.toFinite.fintype
  haveI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  haveI : Nontrivial C := support_connectedComponent_nontrivial (G := G) C
  have htree : C.toSimpleGraph.IsTree := {
    connected := C.connected_toSimpleGraph
    isAcyclic :=
      support_connectedComponent_toSimpleGraph_isAcyclic_of_no_cycle
        (G := G) C hno }
  obtain ⟨a, b, hab, ha_degree, hb_degree⟩ :=
    IsTree.exists_two_distinct_degree_one_of_nontrivial
      (G := C.toSimpleGraph) htree
  refine ⟨(a : G.support), (b : G.support), a.property, b.property, ?_,
    ?_, ?_⟩
  · intro h
    exact hab (Subtype.ext h)
  · rw [support_connectedComponent_degree_eq (G := G) C a, ha_degree]
  · rw [support_connectedComponent_degree_eq (G := G) C b, hb_degree]

/-- Rotation-system form of
`support_connectedComponent_card_le_support_card`. -/
theorem RotationSystem.componentCount_le_support_card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).componentCount <= Fintype.card G.support := by
  rw [R.componentCount_eq_supportComponent_card]
  exact support_connectedComponent_card_le_support_card (G := G)

/-- General Euler-count bridge for graph rotation systems.  If the graph-side
forest-type count `|E| + componentCount <= |support|` holds, then any rotation
system has Euler-planar dual: each hypermap component contributes at least one
face orbit, and the standard rotation-system orbit counts identify graph
edges and non-isolated vertices with hypermap edge and node orbits. -/
theorem RotationSystem.dual_eulerPlanar_of_edge_add_component_le_support
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hcount :
      G.edgeFinset.card + (R.toHypermap).componentCount <=
        Fintype.card G.support) :
    (R.toHypermap).dual.EulerPlanar := by
  classical
  have hface :
      (R.toHypermap).componentCount <= (R.toHypermap).faceOrbitCount :=
    Hypermap.componentCount_le_faceOrbitCount (G := R.toHypermap)
  have hleft_le :
      (R.toHypermap).eulerLeft <= (R.toHypermap).eulerRight := by
    have hdart :
        Fintype.card (R.toHypermap).Dart = 2 * G.edgeFinset.card :=
      orientedEdge_card_eq_twice_card_edges (G := G)
    rw [Hypermap.eulerLeft, Hypermap.eulerRight,
      R.edgeOrbitCount_eq_edgeFinset_card,
      R.nodeOrbitCount_eq_support_card, hdart]
    omega
  have hplanar : (R.toHypermap).EulerPlanar :=
    Hypermap.eulerPlanar_of_eulerLeft_le_eulerRight
      (G := R.toHypermap) hleft_le
  exact (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mpr hplanar

/-- General graph-count endpoint for the SimpleGraph-to-hypermap bridge.  Once
the graph side proves the forest-type inequality
`|E| + supportComponentCount <= |support|`, the arbitrary vertex rotations
constructed above give an Euler-planar dual hypermap. -/
theorem exists_eulerRotationSystem_of_edge_component_count
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcount :
      G.edgeFinset.card + Nat.card (G.induce G.support).ConnectedComponent <=
        Fintype.card G.support) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  let R : RotationSystem G := arbitraryRotationSystem (G := G)
  have hcomponent_eq :
      (R.toHypermap).componentCount =
        Nat.card (G.induce G.support).ConnectedComponent :=
    R.componentCount_eq_supportComponent_card
  have hcountR :
      G.edgeFinset.card + (R.toHypermap).componentCount <=
        Fintype.card G.support := by
    simpa [hcomponent_eq] using hcount
  exact ⟨R, R.dual_eulerPlanar_of_edge_add_component_le_support hcountR⟩

/-- Full finite forest endpoint for the SimpleGraph-to-hypermap bridge. -/
theorem exists_eulerRotationSystem_of_isAcyclic
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  exists_eulerRotationSystem_of_edge_component_count
    (G := G)
    (edgeFinset_card_add_supportComponent_card_le_support_card_of_isAcyclic
      (G := G) hacyclic)

/-- Tree endpoint for the SimpleGraph-to-hypermap bridge.  A nontrivial tree
has full support, one support component, and `|E| + 1 = |V|`; the generic
Euler-count bridge then supplies an Euler-planar dual rotation system.  The
subsingleton case is edgeless. -/
theorem exists_eulerRotationSystem_of_isTree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hT : G.IsTree) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  by_cases htriv : Nontrivial V
  · letI : Nontrivial V := htriv
    have hsupport : G.support = Set.univ :=
      hT.preconnected.support_eq_univ
    have hsupport_card : Fintype.card G.support = Fintype.card V :=
      support_card_eq_of_support_eq_univ (G := G) hsupport
    haveI : Nonempty V := hT.connected.nonempty
    have hsupport_nonempty : Nonempty G.support := by
      let x : V := Classical.choice (inferInstance : Nonempty V)
      exact ⟨⟨x, by rw [hsupport]; trivial⟩⟩
    letI : Nonempty G.support := hsupport_nonempty
    have hcomp : Nat.card (G.induce G.support).ConnectedComponent = 1 :=
      supportComponent_card_eq_one_of_preconnected_nonempty
        (G := G) (support_preconnected_of_preconnected (G := G) hT.preconnected)
    have hedge : G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
    exact
      exists_eulerRotationSystem_of_edge_component_count
        (G := G)
        (by
          rw [hcomp, hsupport_card]
          exact le_of_eq hedge)
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp htriv
    exact exists_eulerRotationSystem_of_edgeless (G := G) (by
      intro x y hxy
      exact hxy.ne (Subsingleton.elim x y))

/-- Connected-support forest endpoint.  If the non-isolated support is
preconnected and the original graph is acyclic, then the induced support graph
is a tree, so its tree edge count gives the graph-side Euler count for the
arbitrary rotation system. -/
theorem exists_eulerRotationSystem_of_isAcyclic_support_preconnected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic)
    (hsupport : (G.induce G.support).Preconnected) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  by_cases hnonempty : Nonempty G.support
  · letI : Nonempty G.support := hnonempty
    let H : SimpleGraph G.support := G.induce G.support
    have hHconnected : H.Connected := {
      preconnected := hsupport
      nonempty := inferInstance }
    have hHtree : H.IsTree := {
      connected := hHconnected
      isAcyclic := hacyclic.induce G.support }
    have hedgeH : H.edgeFinset.card + 1 = Fintype.card G.support :=
      hHtree.card_edgeFinset
    have hedge_eq : H.edgeFinset.card = G.edgeFinset.card := by
      simpa [H] using SimpleGraph.card_edgeFinset_induce_support (G := G)
    have hcomp : Nat.card (G.induce G.support).ConnectedComponent = 1 :=
      supportComponent_card_eq_one_of_preconnected_nonempty (G := G) hsupport
    exact
      exists_eulerRotationSystem_of_edge_component_count
        (G := G)
        (by
          rw [hcomp]
          rw [← hedge_eq]
          exact le_of_eq hedgeH)
  · exact exists_eulerRotationSystem_of_edgeless (G := G) (by
      intro x y hxy
      exact hnonempty ⟨⟨x, hxy.left_mem_support⟩⟩)

/-- Preconnected forest endpoint, phrased on the original graph rather than on
its non-isolated support. -/
theorem exists_eulerRotationSystem_of_isAcyclic_preconnected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic)
    (hG : G.Preconnected) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  exists_eulerRotationSystem_of_isAcyclic_support_preconnected
    (G := G) hacyclic (support_preconnected_of_preconnected (G := G) hG)

/-- Exact Euler-count endpoint for the canonical maximum-degree-two rotation
system.  The connected path/cycle lemmas below prove this count directly in
their cases; the eventual disconnected bridge can use this theorem after
summing the componentwise margins. -/
theorem exists_eulerRotationSystem_of_degree_le_two_of_component_edge_count
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hcount :
      2 * (degreeLeTwoRotationSystem hdegree).toHypermap.componentCount +
          G.edgeFinset.card <=
        Fintype.card G.support +
          (degreeLeTwoRotationSystem hdegree).toHypermap.faceOrbitCount) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  have hleft_le :
      (R.toHypermap).eulerLeft <= (R.toHypermap).eulerRight := by
    have hdart :
        Fintype.card (R.toHypermap).Dart = 2 * G.edgeFinset.card :=
      orientedEdge_card_eq_twice_card_edges (G := G)
    have hcountR :
        2 * (R.toHypermap).componentCount + G.edgeFinset.card <=
          Fintype.card G.support + (R.toHypermap).faceOrbitCount := by
      simpa [R] using hcount
    rw [Hypermap.eulerLeft, Hypermap.eulerRight,
      R.edgeOrbitCount_eq_edgeFinset_card,
      R.nodeOrbitCount_eq_support_card, hdart]
    omega
  have hplanar : (R.toHypermap).EulerPlanar :=
    Hypermap.eulerPlanar_of_eulerLeft_le_eulerRight
      (G := R.toHypermap) hleft_le
  exact ⟨R, (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mpr hplanar⟩

/-- Disconnected-support count endpoint for the canonical maximum-degree-two
rotation system.  Once the graph side supplies the standard pseudoforest count
`|E| + c <= |supp|`, the generic face-surjectivity inequality gives the Euler
bound for the whole rotation system. -/
theorem exists_eulerRotationSystem_of_degree_le_two_of_edge_component_count
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hcount :
      G.edgeFinset.card + Nat.card (G.induce G.support).ConnectedComponent <=
        Fintype.card G.support) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  have hcomponent_eq :
      (R.toHypermap).componentCount =
        Nat.card (G.induce G.support).ConnectedComponent :=
    R.componentCount_eq_supportComponent_card
  have hcountR :
      G.edgeFinset.card + (R.toHypermap).componentCount <=
        Fintype.card G.support := by
    simpa [hcomponent_eq] using hcount
  exact ⟨R, R.dual_eulerPlanar_of_edge_add_component_le_support hcountR⟩

/-- Cyclic-component endpoint for disconnected maximum-degree-two graphs.
When every non-isolated support component has a simple cycle witness, the
componentwise face injection supplies two face orbits per component; combined
with `|E| <= |support|`, this proves Euler-planarity for the canonical
rotation system. -/
theorem exists_eulerRotationSystem_of_degree_le_two_of_component_cycles
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hcycle :
      forall C : (G.induce G.support).ConnectedComponent,
        Exists fun u : V =>
          Exists fun hu : u ∈ G.support =>
            (⟨u, hu⟩ : G.support) ∈ C.supp ∧
              Exists fun c : G.Walk u u => c.IsCycle) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  have hcomponent_eq :
      (R.toHypermap).componentCount =
        Nat.card (G.induce G.support).ConnectedComponent :=
    R.componentCount_eq_supportComponent_card
  have hface :
      2 * (R.toHypermap).componentCount <=
        (R.toHypermap).faceOrbitCount := by
    simpa [R, hcomponent_eq] using
      degreeLeTwoRotationSystem_two_mul_supportComponent_card_le_faceOrbitCount_of_component_cycles
        (G := G) hdegree hcycle
  have hedge :
      G.edgeFinset.card <= Fintype.card G.support :=
    edgeFinset_card_le_support_card_of_degree_le_two (G := G) hdegree
  exact
    exists_eulerRotationSystem_of_degree_le_two_of_component_edge_count
      (G := G) hdegree
      (by
        simpa [R] using
          (by omega :
            2 * (R.toHypermap).componentCount + G.edgeFinset.card <=
              Fintype.card G.support + (R.toHypermap).faceOrbitCount))

/-- Graph-side mixed path/cycle count for maximum-degree-two graphs.  If every
support component not listed as cyclic has two distinct degree-at-most-one
support vertices, then the handshaking count gives
`|E| + componentCount <= |support| + cyclicComponentCount`. -/
theorem edgeFinset_card_add_supportComponent_card_le_support_card_add_cyclic_card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (Cyc : Finset (G.induce G.support).ConnectedComponent)
    (hendpoints :
      forall C : (G.induce G.support).ConnectedComponent, C ∉ Cyc ->
        Exists fun a : G.support =>
          Exists fun b : G.support =>
            a ∈ C.supp ∧ b ∈ C.supp ∧ a ≠ b ∧
              G.degree (a : V) <= 1 ∧ G.degree (b : V) <= 1) :
    G.edgeFinset.card + Nat.card (G.induce G.support).ConnectedComponent <=
      Fintype.card G.support + Cyc.card := by
  classical
  let Comp := (G.induce G.support).ConnectedComponent
  let Noncyc : Finset Comp := Finset.univ.filter fun C : Comp => C ∉ Cyc
  let NoncycComp := {C : Comp // C ∈ Noncyc}
  let endpointA : forall C : NoncycComp, G.support := fun C =>
    (hendpoints C.1 (by
      have h := (Finset.mem_filter.mp C.2).2
      exact h)).choose
  let endpointB : forall C : NoncycComp, G.support := fun C =>
    (hendpoints C.1 (by
      have h := (Finset.mem_filter.mp C.2).2
      exact h)).choose_spec.choose
  have endpointA_mem :
      forall C : NoncycComp, endpointA C ∈ C.1.supp := fun C =>
    (hendpoints C.1 (by
      have h := (Finset.mem_filter.mp C.2).2
      exact h)).choose_spec.choose_spec.1
  have endpointB_mem :
      forall C : NoncycComp, endpointB C ∈ C.1.supp := fun C =>
    (hendpoints C.1 (by
      have h := (Finset.mem_filter.mp C.2).2
      exact h)).choose_spec.choose_spec.2.1
  have endpoint_ne :
      forall C : NoncycComp, endpointA C ≠ endpointB C := fun C =>
    (hendpoints C.1 (by
      have h := (Finset.mem_filter.mp C.2).2
      exact h)).choose_spec.choose_spec.2.2.1
  have endpointA_degree :
      forall C : NoncycComp, G.degree (endpointA C : V) <= 1 := fun C =>
    (hendpoints C.1 (by
      have h := (Finset.mem_filter.mp C.2).2
      exact h)).choose_spec.choose_spec.2.2.2.1
  have endpointB_degree :
      forall C : NoncycComp, G.degree (endpointB C : V) <= 1 := fun C =>
    (hendpoints C.1 (by
      have h := (Finset.mem_filter.mp C.2).2
      exact h)).choose_spec.choose_spec.2.2.2.2
  let endpoint : NoncycComp × Fin 2 -> G.support := fun Ci =>
    match Ci.2 with
    | 0 => endpointA Ci.1
    | _ => endpointB Ci.1
  have endpoint_injective : Function.Injective endpoint := by
    intro Ci Dj hmap
    rcases Ci with ⟨C, i⟩
    rcases Dj with ⟨D, j⟩
    dsimp [endpoint] at hmap
    have hCD : C = D := by
      have hCmk :
          (G.induce G.support).connectedComponentMk (endpoint (C, i)) = C.1 := by
        fin_cases i
        · exact
            (SimpleGraph.ConnectedComponent.mem_supp_iff C.1 (endpointA C)).mp
            (endpointA_mem C)
        · exact
            (SimpleGraph.ConnectedComponent.mem_supp_iff C.1 (endpointB C)).mp
            (endpointB_mem C)
      have hDmk :
          (G.induce G.support).connectedComponentMk (endpoint (D, j)) = D.1 := by
        fin_cases j
        · exact
            (SimpleGraph.ConnectedComponent.mem_supp_iff D.1 (endpointA D)).mp
            (endpointA_mem D)
        · exact
            (SimpleGraph.ConnectedComponent.mem_supp_iff D.1 (endpointB D)).mp
            (endpointB_mem D)
      have hmk :
          (G.induce G.support).connectedComponentMk (endpoint (C, i)) =
            (G.induce G.support).connectedComponentMk (endpoint (D, j)) := by
        simpa [endpoint] using
          congrArg (fun x : G.support =>
            (G.induce G.support).connectedComponentMk x) hmap
      exact Subtype.ext (hCmk.symm.trans (hmk.trans hDmk))
    subst D
    have hij : i = j := by
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (endpoint_ne C hmap)
      · exact False.elim (endpoint_ne C hmap.symm)
      · rfl
    subst j
    rfl
  let marked : Finset G.support := Finset.univ.map ⟨endpoint, endpoint_injective⟩
  have marked_card :
      marked.card = Fintype.card (NoncycComp × Fin 2) := by
    simp [marked]
  have endpoint_degree_of_mem :
      forall x : G.support, x ∈ marked -> G.degree (x : V) <= 1 := by
    intro x hx
    change x ∈ Finset.univ.map ⟨endpoint, endpoint_injective⟩ at hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨Ci, _hCi, hCi⟩
    rcases Ci with ⟨C, i⟩
    fin_cases i
    · have hxdeg :
          G.degree ((endpoint (C, (0 : Fin 2)) : G.support) : V) <= 1 := by
        simpa [endpoint] using endpointA_degree C
      exact hCi ▸ hxdeg
    · have hxdeg :
          G.degree ((endpoint (C, (1 : Fin 2)) : G.support) : V) <= 1 := by
        simpa [endpoint] using endpointB_degree C
      exact hCi ▸ hxdeg
  have hsum_support :
      (∑ x : G.support, G.degree (x : V)) =
        2 * G.edgeFinset.card := by
    let e : G.support ≃ {v : V // v ∈ G.support.toFinset} := {
      toFun x := ⟨x, by
        simp [x.property]⟩
      invFun x := ⟨x, by
        exact Set.mem_toFinset.mp x.property⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    calc
      (∑ x : G.support, G.degree (x : V)) =
          ∑ x : {v : V // v ∈ G.support.toFinset}, G.degree (x : V) := by
        exact Fintype.sum_equiv e _ _ (by intro x; rfl)
      _ = ∑ v ∈ G.support.toFinset, G.degree v := by
        exact G.support.toFinset.sum_attach (fun v => G.degree v)
      _ = 2 * G.edgeFinset.card :=
        G.sum_degrees_support_eq_twice_card_edges
  have hsum_bonus :
      (∑ x : G.support, (if x ∈ marked then (1 : Nat) else 0)) =
        marked.card := by
    classical
    rw [← Finset.sum_filter]
    simp
  have hsum_le :
      (∑ x : G.support,
          (G.degree (x : V) + if x ∈ marked then (1 : Nat) else 0)) <=
        ∑ _x : G.support, (2 : Nat) := by
    exact Finset.sum_le_sum (by
      intro x _hx
      by_cases hx : x ∈ marked
      · have hxdeg := endpoint_degree_of_mem x hx
        simp [hx]
        omega
      · have hxdeg := hdegree (x : V)
        simp [hx]
        omega)
  have hmarked_count :
      2 * G.edgeFinset.card + marked.card <=
        2 * Fintype.card G.support := by
    rw [Finset.sum_add_distrib, hsum_support, hsum_bonus] at hsum_le
    simpa [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] using hsum_le
  have hnoncyc_card :
      Fintype.card NoncycComp = Noncyc.card := by
    change Fintype.card {C : Comp // C ∈ Noncyc} = Noncyc.card
    rw [Fintype.card_subtype]
    simp
  have hpath_count :
      G.edgeFinset.card + Noncyc.card <= Fintype.card G.support := by
    have hmarked :
        marked.card = 2 * Noncyc.card := by
      rw [marked_card, Fintype.card_prod, Fintype.card_fin, hnoncyc_card]
      omega
    rw [hmarked] at hmarked_count
    omega
  have hcomp_split :
      Nat.card Comp = Cyc.card + Noncyc.card := by
    rw [Nat.card_eq_fintype_card]
    have hsplit :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset Comp)) (p := fun C : Comp => C ∈ Cyc)
    have hcyc_filter :
        ((Finset.univ : Finset Comp).filter fun C : Comp => C ∈ Cyc).card =
          Cyc.card := by
      have hfilter_eq :
          (Finset.univ.filter fun C : Comp => C ∈ Cyc) = Cyc := by
        ext C
        simp
      rw [hfilter_eq]
    have hnoncyc_filter :
        ((Finset.univ : Finset Comp).filter fun C : Comp => C ∉ Cyc).card =
          Noncyc.card := rfl
    rw [hcyc_filter, hnoncyc_filter, Finset.card_univ] at hsplit
    omega
  have hcomp_split' :
      Nat.card (G.induce G.support).ConnectedComponent =
        Cyc.card + Noncyc.card := by
    simpa [Comp] using hcomp_split
  omega

/-- Mixed path/cycle endpoint for disconnected maximum-degree-two graphs.  The
remaining graph-side input is exactly the standard component count
`|E| + c <= |support| + cyclicComponents`; the preceding face-count theorem
turns the listed cyclic components into the extra face orbits needed for the
Euler inequality. -/
theorem exists_eulerRotationSystem_of_degree_le_two_of_component_cycle_count
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (Cyc : Finset (G.induce G.support).ConnectedComponent)
    (hcycle :
      forall C : (G.induce G.support).ConnectedComponent, C ∈ Cyc ->
        Exists fun u : V =>
          Exists fun hu : u ∈ G.support =>
            (⟨u, hu⟩ : G.support) ∈ C.supp ∧
              Exists fun c : G.Walk u u => c.IsCycle)
    (hcount :
      G.edgeFinset.card + Nat.card (G.induce G.support).ConnectedComponent <=
        Fintype.card G.support + Cyc.card) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  have hcomponent_eq :
      (R.toHypermap).componentCount =
        Nat.card (G.induce G.support).ConnectedComponent :=
    R.componentCount_eq_supportComponent_card
  have hface :
      (R.toHypermap).componentCount + Cyc.card <=
        (R.toHypermap).faceOrbitCount := by
    simpa [R, hcomponent_eq] using
      degreeLeTwoRotationSystem_supportComponent_card_add_cyclic_card_le_faceOrbitCount
        (G := G) hdegree Cyc hcycle
  exact
    exists_eulerRotationSystem_of_degree_le_two_of_component_edge_count
      (G := G) hdegree
      (by
        have hcountR :
            G.edgeFinset.card + (R.toHypermap).componentCount <=
              Fintype.card G.support + Cyc.card := by
          simpa [hcomponent_eq] using hcount
        simpa [R] using
          (by omega :
            2 * (R.toHypermap).componentCount + G.edgeFinset.card <=
              Fintype.card G.support + (R.toHypermap).faceOrbitCount))

/-- Mixed path/cycle endpoint with concrete component data.  Cyclic support
components provide simple cycle witnesses; every remaining support component
provides two distinct supported endpoints of degree at most one.  The two
componentwise inputs feed the face-count and handshaking-count lemmas above,
so the canonical maximum-degree-two rotation system has Euler-planar dual. -/
theorem exists_eulerRotationSystem_of_degree_le_two_of_component_cycle_endpoint_data
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (Cyc : Finset (G.induce G.support).ConnectedComponent)
    (hcycle :
      forall C : (G.induce G.support).ConnectedComponent, C ∈ Cyc ->
        Exists fun u : V =>
          Exists fun hu : u ∈ G.support =>
            (⟨u, hu⟩ : G.support) ∈ C.supp ∧
              Exists fun c : G.Walk u u => c.IsCycle)
    (hendpoints :
      forall C : (G.induce G.support).ConnectedComponent, C ∉ Cyc ->
        Exists fun a : G.support =>
          Exists fun b : G.support =>
            a ∈ C.supp ∧ b ∈ C.supp ∧ a ≠ b ∧
              G.degree (a : V) <= 1 ∧ G.degree (b : V) <= 1) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  exists_eulerRotationSystem_of_degree_le_two_of_component_cycle_count
    (G := G) hdegree Cyc hcycle
    (edgeFinset_card_add_supportComponent_card_le_support_card_add_cyclic_card
      (G := G) hdegree Cyc hendpoints)
end FourColor

end Schematic.Math.GraphTheory
