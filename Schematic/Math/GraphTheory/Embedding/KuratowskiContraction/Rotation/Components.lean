import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Rotation.CycleFaces

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- A connected graph has connected non-isolated support.  Isolated vertices
are irrelevant to the oriented-edge hypermap, so this is the graph-side
connectivity bridge used before applying the degree-at-most-two endpoint. -/
theorem support_preconnected_of_preconnected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected) :
    (G.induce G.support).Preconnected := by
  intro x y
  exact RotationSystem.reachable_induce_support_of_reachable
    (G := G) (hG (x : V) (y : V))

/-- When a graph's support is all vertices, the support subtype has the same
finite cardinality as the vertex type. -/
noncomputable def supportEquivOfSupportEqUniv
    {V : Type u} {G : SimpleGraph V}
    (h : G.support = Set.univ) :
    G.support ≃ V where
  toFun x := x
  invFun x := ⟨x, by rw [h]; trivial⟩
  left_inv := by
    intro x
    ext
    rfl
  right_inv := by
    intro x
    rfl

theorem support_card_eq_of_support_eq_univ
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.support = Set.univ) :
    Fintype.card G.support = Fintype.card V := by
  classical
  exact Fintype.card_congr (supportEquivOfSupportEqUniv (G := G) h)

/-- A nonempty preconnected support has exactly one support component. -/
theorem supportComponent_card_eq_one_of_preconnected_nonempty
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hsupport : (G.induce G.support).Preconnected)
    [Nonempty G.support] :
    Nat.card (G.induce G.support).ConnectedComponent = 1 := by
  classical
  let x : G.support := Classical.choice inferInstance
  haveI : Subsingleton (G.induce G.support).ConnectedComponent :=
    SimpleGraph.Preconnected.subsingleton_connectedComponent hsupport
  haveI : Nonempty (G.induce G.support).ConnectedComponent :=
    ⟨(G.induce G.support).connectedComponentMk x⟩
  exact Nat.card_unique

/-- Vertices split as the dependent sum of connected components and vertices
inside each component. -/
noncomputable def connectedComponentVertexSigmaEquiv
    {V : Type u} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    V ≃ Sigma (fun C : G.ConnectedComponent => C) where
  toFun v := ⟨G.connectedComponentMk v,
    ⟨v, SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      (G := G) (v := v)⟩⟩
  invFun s := s.2.1
  left_inv := by
    intro v
    rfl
  right_inv := by
    intro s
    cases s with
    | mk C v =>
        cases v with
        | mk x hx =>
            have hC : G.connectedComponentMk x = C :=
              (SimpleGraph.ConnectedComponent.mem_supp_iff C x).mp hx
            cases hC
            rfl

/-- Cardinal form of `connectedComponentVertexSigmaEquiv`, using `Nat.card`
inside components so callers do not need component fintype instances in the
statement. -/
theorem card_eq_sum_connectedComponent_natCard
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    Fintype.card V = ∑ C : G.ConnectedComponent, Nat.card C := by
  classical
  letI (C : G.ConnectedComponent) : Fintype C := C.supp.toFinite.fintype
  have hcard := Fintype.card_congr
    (connectedComponentVertexSigmaEquiv (G := G))
  rw [Fintype.card_sigma] at hcard
  have hright :
      (∑ C : G.ConnectedComponent, Fintype.card C) =
        ∑ C : G.ConnectedComponent, Nat.card C := by
    apply Finset.sum_congr rfl
    intro C _
    rw [Nat.card_eq_fintype_card]
  simpa [hright] using hcard

/-- Oriented edges whose tail lies in a fixed connected component. -/
abbrev ComponentOrientedEdgeFiber
    {V : Type u} (G : SimpleGraph V)
    (C : G.ConnectedComponent) :=
  {e : OrientedEdge G // e.tail ∈ C.supp}

theorem OrientedEdge.connectedComponentMk_head_eq_tail
    {V : Type u} {G : SimpleGraph V}
    (e : OrientedEdge G) :
    G.connectedComponentMk e.head = G.connectedComponentMk e.tail :=
  SimpleGraph.ConnectedComponent.sound e.adj.symm.reachable

theorem OrientedEdge.connectedComponentMk_tail_eq_head
    {V : Type u} {G : SimpleGraph V}
    (e : OrientedEdge G) :
    G.connectedComponentMk e.tail = G.connectedComponentMk e.head :=
  (e.connectedComponentMk_head_eq_tail).symm

/-- Oriented edges in a component graph are the same as original oriented
edges whose tail lies in that component. -/
noncomputable def componentOrientedEdgeFiberEquiv
    {V : Type u} {G : SimpleGraph V} (C : G.ConnectedComponent) :
    OrientedEdge C.toSimpleGraph ≃ ComponentOrientedEdgeFiber G C where
  toFun e := ⟨⟨(((e.tail : C) : V), ((e.head : C) : V)), e.adj⟩,
    e.tail.property⟩
  invFun e :=
    let tailC : C := ⟨e.1.tail, e.2⟩
    let headC : C := ⟨e.1.head, C.mem_supp_of_adj_mem_supp e.2 e.1.adj⟩
    ⟨(tailC, headC), e.1.adj⟩
  left_inv := by
    intro e
    cases e with
    | mk e he =>
        cases e
        rfl
  right_inv := by
    intro e
    cases e with
    | mk e he =>
        cases e with
        | mk e hadj =>
            cases e
            rfl

/-- Oriented edges split by the connected component of their tail. -/
noncomputable def orientedEdgeComponentFiberSigmaEquiv
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} :
    OrientedEdge G ≃ Sigma (ComponentOrientedEdgeFiber G) where
  toFun e := ⟨G.connectedComponentMk e.tail, ⟨e,
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      (G := G) (v := e.tail)⟩⟩
  invFun s := s.2.1
  left_inv := by
    intro e
    rfl
  right_inv := by
    intro s
    cases s with
    | mk C e =>
        cases e with
        | mk e he =>
            have hC : G.connectedComponentMk e.tail = C :=
              (SimpleGraph.ConnectedComponent.mem_supp_iff C e.tail).mp he
            cases hC
            rfl

/-- Assemble a rotation system on a graph from rotation systems on all of its
connected components.  Isolated components contribute no darts; all oriented
edges are transported through their tail component. -/
noncomputable def componentRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph) :
    RotationSystem G where
  node :=
    let π : forall C : G.ConnectedComponent,
        Equiv.Perm (ComponentOrientedEdgeFiber G C) :=
      fun C => (componentOrientedEdgeFiberEquiv (G := G) C).permCongr
        (Rcomp C).node
    (orientedEdgeComponentFiberSigmaEquiv (G := G)).permCongr.symm
      (sigmaPerm (ComponentOrientedEdgeFiber G) π)
  node_tail := by
    intro e
    let E : OrientedEdge G ≃ Sigma (ComponentOrientedEdgeFiber G) :=
      orientedEdgeComponentFiberSigmaEquiv (G := G)
    let π : forall C : G.ConnectedComponent,
        Equiv.Perm (ComponentOrientedEdgeFiber G C) :=
      fun C => (componentOrientedEdgeFiberEquiv (G := G) C).permCongr
        (Rcomp C).node
    let C : G.ConnectedComponent := G.connectedComponentMk e.tail
    let eC : OrientedEdge C.toSimpleGraph :=
      (componentOrientedEdgeFiberEquiv (G := G) C).symm
        ⟨e, SimpleGraph.ConnectedComponent.connectedComponentMk_mem
          (G := G) (v := e.tail)⟩
    have hnode :
        (((Rcomp C).node eC).tail : V) = (eC.tail : V) :=
      congrArg Subtype.val ((Rcomp C).node_tail eC)
    have heC : (eC.tail : V) = e.tail := by
      change
        ((⟨e.tail, SimpleGraph.ConnectedComponent.connectedComponentMk_mem
          (G := G) (v := e.tail)⟩ : C) : V) = e.tail
      rfl
    simpa [E, π, C, eC, orientedEdgeComponentFiberSigmaEquiv,
      componentOrientedEdgeFiberEquiv, sigmaPerm] using hnode.trans heC
  node_orbit_of_same_tail := by
    intro e f hef
    let E : OrientedEdge G ≃ Sigma (ComponentOrientedEdgeFiber G) :=
      orientedEdgeComponentFiberSigmaEquiv (G := G)
    let π : forall C : G.ConnectedComponent,
        Equiv.Perm (ComponentOrientedEdgeFiber G C) :=
      fun C => (componentOrientedEdgeFiberEquiv (G := G) C).permCongr
        (Rcomp C).node
    let P : Equiv.Perm (Sigma (ComponentOrientedEdgeFiber G)) :=
      sigmaPerm (ComponentOrientedEdgeFiber G) π
    let N : Equiv.Perm (OrientedEdge G) := E.permCongr.symm P
    change PermReachable N e f
    rcases hEe : E e with ⟨C, ec⟩
    rcases hEf : E f with ⟨D, fc⟩
    have hCD : C = D := by
      have hbase : (E e).1 = (E f).1 := by
        simpa [E, orientedEdgeComponentFiberSigmaEquiv] using
          congrArg G.connectedComponentMk hef
      simpa [hEe, hEf] using hbase
    subst D
    have he_back : E.symm (Sigma.mk C ec) = e := by
      rw [← hEe]
      simp
    have hf_back : E.symm (Sigma.mk C fc) = f := by
      rw [← hEf]
      simp
    have htail_component :
        ((componentOrientedEdgeFiberEquiv (G := G) C).symm ec).tail =
          ((componentOrientedEdgeFiberEquiv (G := G) C).symm fc).tail := by
      apply Subtype.ext
      have htail_e : (((componentOrientedEdgeFiberEquiv (G := G) C).symm ec).tail : V) =
          e.tail := by
        simpa [E, orientedEdgeComponentFiberSigmaEquiv,
          componentOrientedEdgeFiberEquiv] using congrArg OrientedEdge.tail he_back
      have htail_f : (((componentOrientedEdgeFiberEquiv (G := G) C).symm fc).tail : V) =
          f.tail := by
        simpa [E, orientedEdgeComponentFiberSigmaEquiv,
          componentOrientedEdgeFiberEquiv] using congrArg OrientedEdge.tail hf_back
      calc
        (((componentOrientedEdgeFiberEquiv (G := G) C).symm ec).tail : V) =
            e.tail := htail_e
        _ = f.tail := hef
        _ = (((componentOrientedEdgeFiberEquiv (G := G) C).symm fc).tail : V) :=
            htail_f.symm
    have hlocal :
        PermReachable (π C) ec fc := by
      let F := componentOrientedEdgeFiberEquiv (G := G) C
      have hcomponent :
          PermReachable (Rcomp C).node (F.symm ec) (F.symm fc) :=
        (Rcomp C).node_orbit_of_same_tail (F.symm ec) (F.symm fc)
          htail_component
      have hconj :
          forall z : OrientedEdge C.toSimpleGraph,
            F ((Rcomp C).node z) = (π C) (F z) := by
        intro z
        simp [F, π]
      have hreach := permReachable_conj F (Rcomp C).node (π C) hconj
        hcomponent
      simpa [F] using hreach
    have hP :
        PermReachable P (Sigma.mk C ec) (Sigma.mk C fc) :=
      sigmaPerm_reachable_of_same_base hlocal
    have hconj_global :
        forall s : Sigma (ComponentOrientedEdgeFiber G),
          E.symm (P s) = N (E.symm s) := by
      intro s
      simp [N]
    have hN :
        PermReachable N (E.symm (Sigma.mk C ec)) (E.symm (Sigma.mk C fc)) :=
      permReachable_conj E.symm P N hconj_global hP
    simpa [he_back, hf_back] using hN

/-- For the componentwise rotation system, a generated dart component of the
global hypermap is exactly the oriented-edge type of the corresponding graph
connected component. -/
noncomputable def componentRotationSystem_componentDartEquiv
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (c : ((componentRotationSystem (G := G) Rcomp).toHypermap).Component) :
    ((componentRotationSystem (G := G) Rcomp).toHypermap).ComponentDart c ≃
      OrientedEdge
        (G.connectedComponentMk
          (Quotient.out c :
            ((componentRotationSystem (G := G) Rcomp).toHypermap).Dart).tail
        ).toSimpleGraph where
  toFun y :=
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    let x0 : OrientedEdge G := Quotient.out c
    let C : G.ConnectedComponent := G.connectedComponentMk x0.tail
    (componentOrientedEdgeFiberEquiv (G := G) C).symm
      ⟨y.1, by
        have hx0 : (R.toHypermap).componentOf x0 = c := Quotient.out_eq c
        have hyx0 :
            (R.toHypermap).componentOf y.1 =
              (R.toHypermap).componentOf x0 :=
          y.2.trans hx0.symm
        have hreachH : (R.toHypermap).Reachable y.1 x0 :=
          (R.toHypermap).reachable_of_componentOf_eq hyx0
        have hreachG : G.Reachable y.1.tail x0.tail :=
          R.toHypermap_reachable_tail_reachable hreachH
        have hmk :
            G.connectedComponentMk y.1.tail = C :=
          SimpleGraph.ConnectedComponent.sound hreachG
        exact
          (SimpleGraph.ConnectedComponent.mem_supp_iff C y.1.tail).mpr hmk⟩
  invFun z :=
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    let x0 : OrientedEdge G := Quotient.out c
    let C : G.ConnectedComponent := G.connectedComponentMk x0.tail
    let e : ComponentOrientedEdgeFiber G C :=
      componentOrientedEdgeFiberEquiv (G := G) C z
    ⟨e.1, by
      have hx0 : (R.toHypermap).componentOf x0 = c := Quotient.out_eq c
      have hmk_tail :
          G.connectedComponentMk e.1.tail = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C e.1.tail).mp e.2
      have hmk_x0 : G.connectedComponentMk x0.tail = C := rfl
      have hreachG : G.Reachable e.1.tail x0.tail :=
        SimpleGraph.ConnectedComponent.exact (hmk_tail.trans hmk_x0.symm)
      have hreachH : (R.toHypermap).Reachable e.1 x0 :=
        R.toHypermap_reachable_of_tail_reachable hreachG
      exact ((R.toHypermap).componentOf_eq_componentOf hreachH).trans hx0⟩
  left_inv := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro z
    apply Subtype.ext
    cases z with
    | mk z hz =>
        cases z
        rfl

/-- Tails of all darts in one generated component of the componentwise
rotation system lie in the same graph connected component as the chosen
representative dart. -/
theorem componentRotationSystem_componentDart_connectedComponentMk_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (c : ((componentRotationSystem (G := G) Rcomp).toHypermap).Component)
    (x : ((componentRotationSystem (G := G) Rcomp).toHypermap).ComponentDart c) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    G.connectedComponentMk x.1.tail =
      G.connectedComponentMk (Quotient.out c : R.toHypermap.Dart).tail := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  have hx0 : (R.toHypermap).componentOf
      (Quotient.out c : R.toHypermap.Dart) = c :=
    Quotient.out_eq c
  have hxcomp_out :
      (R.toHypermap).componentOf x.1 =
        (R.toHypermap).componentOf (Quotient.out c : R.toHypermap.Dart) :=
    x.2.trans hx0.symm
  have hreachH : (R.toHypermap).Reachable x.1
      (Quotient.out c : R.toHypermap.Dart) :=
    (R.toHypermap).reachable_of_componentOf_eq hxcomp_out
  exact SimpleGraph.ConnectedComponent.sound
    (R.toHypermap_reachable_tail_reachable hreachH)

/-- The component dart equivalence commutes with the edge involution. -/
theorem componentRotationSystem_componentDartEquiv_map_edge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (c : ((componentRotationSystem (G := G) Rcomp).toHypermap).Component)
    (x : ((componentRotationSystem (G := G) Rcomp).toHypermap).ComponentDart c) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    let C : G.ConnectedComponent :=
      G.connectedComponentMk
        (Quotient.out c : R.toHypermap.Dart).tail
    letI : Fintype C := C.supp.toFinite.fintype
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    let e :
        R.toHypermap.ComponentDart c ≃ OrientedEdge C.toSimpleGraph :=
      componentRotationSystem_componentDartEquiv (G := G) Rcomp c
    e ((R.toHypermap.componentHypermap c).edge x) =
      (Rcomp C).toHypermap.edge (e x) := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  let C : G.ConnectedComponent :=
    G.connectedComponentMk
      (Quotient.out c : R.toHypermap.Dart).tail
  letI : Fintype C := C.supp.toFinite.fintype
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let e :
      R.toHypermap.ComponentDart c ≃ OrientedEdge C.toSimpleGraph :=
    componentRotationSystem_componentDartEquiv (G := G) Rcomp c
  cases x with
  | mk x hx =>
      cases x with
      | mk x hxadj =>
          cases x
          apply Subtype.ext
          rfl

/-- Local computation of the node permutation assembled by
`componentRotationSystem`, at the component determined by the dart tail. -/
theorem componentRotationSystem_node_tailComponent
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (x : OrientedEdge G) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    let C : G.ConnectedComponent := G.connectedComponentMk x.tail
    letI : Fintype C := C.supp.toFinite.fintype
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    let F := componentOrientedEdgeFiberEquiv (G := G) C
    let xF : ComponentOrientedEdgeFiber G C :=
      ⟨x, SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        (G := G) (v := x.tail)⟩
    let nxF : ComponentOrientedEdgeFiber G C :=
      ⟨R.node x, by
        rw [R.node_tail x]
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
          (G := G) (v := x.tail)⟩
    F.symm nxF = (Rcomp C).node (F.symm xF) := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  let C : G.ConnectedComponent := G.connectedComponentMk x.tail
  letI : Fintype C := C.supp.toFinite.fintype
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let F := componentOrientedEdgeFiberEquiv (G := G) C
  cases x with
  | mk x hx =>
      cases x
      apply Subtype.ext
      rfl

/-- Local computation of the assembled node permutation in any component that
contains the dart tail.  This is the transport-friendly form used by the
generated-component equivalence: the component is supplied by the caller
rather than fixed definitionally as `connectedComponentMk x.tail`. -/
theorem componentRotationSystem_node_component
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (C : G.ConnectedComponent)
    (x : OrientedEdge G)
    (hxC : x.tail ∈ C.supp) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    letI : Fintype C := C.supp.toFinite.fintype
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    let F := componentOrientedEdgeFiberEquiv (G := G) C
    let xF : ComponentOrientedEdgeFiber G C := ⟨x, hxC⟩
    let nxF : ComponentOrientedEdgeFiber G C :=
      ⟨R.node x, by
        rw [R.node_tail x]
        exact hxC⟩
    F.symm nxF = (Rcomp C).node (F.symm xF) := by
  classical
  have hC : G.connectedComponentMk x.tail = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C x.tail).mp hxC
  cases hC
  exact componentRotationSystem_node_tailComponent (G := G) Rcomp x

/-- The component dart equivalence commutes with the node permutation. -/
theorem componentRotationSystem_componentDartEquiv_map_node
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (c : ((componentRotationSystem (G := G) Rcomp).toHypermap).Component)
    (x : ((componentRotationSystem (G := G) Rcomp).toHypermap).ComponentDart c) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    let C : G.ConnectedComponent :=
      G.connectedComponentMk
        (Quotient.out c : R.toHypermap.Dart).tail
    letI : Fintype C := C.supp.toFinite.fintype
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    let e :
        R.toHypermap.ComponentDart c ≃ OrientedEdge C.toSimpleGraph :=
      componentRotationSystem_componentDartEquiv (G := G) Rcomp c
    e ((R.toHypermap.componentHypermap c).node x) =
      (Rcomp C).toHypermap.node (e x) := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  let C : G.ConnectedComponent :=
    G.connectedComponentMk
      (Quotient.out c : R.toHypermap.Dart).tail
  letI : Fintype C := C.supp.toFinite.fintype
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let e :
      R.toHypermap.ComponentDart c ≃ OrientedEdge C.toSimpleGraph :=
    componentRotationSystem_componentDartEquiv (G := G) Rcomp c
  cases x with
  | mk x hx =>
      have hxC : x.tail ∈ C.supp := by
        have hx0 : (R.toHypermap).componentOf
            (Quotient.out c : R.toHypermap.Dart) = c :=
          Quotient.out_eq c
        have hxc :
            (R.toHypermap).componentOf x =
              (R.toHypermap).componentOf
                (Quotient.out c : R.toHypermap.Dart) :=
          hx.trans hx0.symm
        have hreach : (R.toHypermap).Reachable x
            (Quotient.out c : R.toHypermap.Dart) :=
          (R.toHypermap).reachable_of_componentOf_eq hxc
        have hmk : G.connectedComponentMk x.tail = C :=
          SimpleGraph.ConnectedComponent.sound
            (R.toHypermap_reachable_tail_reachable hreach)
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff C x.tail).mpr hmk
      have hnode :=
        componentRotationSystem_node_component
          (G := G) Rcomp C x hxC
      simpa [R, C, e, componentRotationSystem_componentDartEquiv] using hnode

/-- The component dart equivalence commutes with the face permutation. -/
theorem componentRotationSystem_componentDartEquiv_map_face
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (c : ((componentRotationSystem (G := G) Rcomp).toHypermap).Component)
    (x : ((componentRotationSystem (G := G) Rcomp).toHypermap).ComponentDart c) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    let C : G.ConnectedComponent :=
      G.connectedComponentMk
        (Quotient.out c : R.toHypermap.Dart).tail
    letI : Fintype C := C.supp.toFinite.fintype
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    let e :
        R.toHypermap.ComponentDart c ≃ OrientedEdge C.toSimpleGraph :=
      componentRotationSystem_componentDartEquiv (G := G) Rcomp c
    e ((R.toHypermap.componentHypermap c).face x) =
      (Rcomp C).toHypermap.face (e x) := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  let C : G.ConnectedComponent :=
    G.connectedComponentMk
      (Quotient.out c : R.toHypermap.Dart).tail
  letI : Fintype C := C.supp.toFinite.fintype
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let e :
      R.toHypermap.ComponentDart c ≃ OrientedEdge C.toSimpleGraph :=
    componentRotationSystem_componentDartEquiv (G := G) Rcomp c
  let Hc : Hypermap := R.toHypermap.componentHypermap c
  let H : Hypermap := (Rcomp C).toHypermap
  have hnode : forall y : Hc.Dart, e (Hc.node y) = H.node (e y) := by
    intro y
    simpa [R, C, e, Hc, H] using
      componentRotationSystem_componentDartEquiv_map_node
        (G := G) Rcomp c y
  have hedge : forall y : Hc.Dart, e (Hc.edge y) = H.edge (e y) := by
    intro y
    simpa [R, C, e, Hc, H] using
      componentRotationSystem_componentDartEquiv_map_edge
        (G := G) Rcomp c y
  have hfaceHc : Hc.face x = Hc.node.symm (Hc.edge x) := by
    cases x
    apply Subtype.ext
    rfl
  have hfaceH : H.face (e x) = H.node.symm (H.edge (e x)) := by
    rfl
  calc
    e (Hc.face x) =
        e (Hc.node.symm (Hc.edge x)) := by rw [hfaceHc]
    _ = H.node.symm (e (Hc.edge x)) :=
        perm_conj_symm_apply e Hc.node H.node hnode (Hc.edge x)
    _ = H.node.symm (H.edge (e x)) := by rw [hedge x]
    _ = H.face (e x) := hfaceH.symm

/-- Each generated hypermap component of a componentwise rotation system is
isomorphic to the hypermap of the corresponding graph connected component. -/
noncomputable def componentRotationSystem_componentHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (c : ((componentRotationSystem (G := G) Rcomp).toHypermap).Component) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    let C : G.ConnectedComponent :=
      G.connectedComponentMk
        (Quotient.out c : R.toHypermap.Dart).tail
    letI : Fintype C := C.supp.toFinite.fintype
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    Hypermap.Iso (R.toHypermap.componentHypermap c) (Rcomp C).toHypermap := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  let C : G.ConnectedComponent :=
    G.connectedComponentMk
      (Quotient.out c : R.toHypermap.Dart).tail
  letI : Fintype C := C.supp.toFinite.fintype
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let e :
      R.toHypermap.ComponentDart c ≃ OrientedEdge C.toSimpleGraph :=
    componentRotationSystem_componentDartEquiv (G := G) Rcomp c
  refine
    { toEquiv := e
      map_edge := ?_
      map_node := ?_
      map_face := ?_ }
  · intro x
    simpa [R, C, e] using
      componentRotationSystem_componentDartEquiv_map_edge
        (G := G) Rcomp c x
  · intro x
    simpa [R, C, e] using
      componentRotationSystem_componentDartEquiv_map_node
        (G := G) Rcomp c x
  · intro x
    simpa [R, C, e] using
      componentRotationSystem_componentDartEquiv_map_face
        (G := G) Rcomp c x

/-- Euler-planarity glues across the rotation system assembled from graph
connected components. -/
theorem componentRotationSystem_dual_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph)
    (hcomp :
      forall C : G.ConnectedComponent,
        letI : Fintype C := C.supp.toFinite.fintype
        letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
        ((Rcomp C).toHypermap).dual.EulerPlanar) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    (R.toHypermap).dual.EulerPlanar := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  have hprimal : (R.toHypermap).EulerPlanar := by
    refine
      Hypermap.componentHypermap.eulerPlanar_of_forall_component_eulerLeft_le_eulerRight
        (G := R.toHypermap) ?_
    intro c
    let C : G.ConnectedComponent :=
      G.connectedComponentMk
        (Quotient.out c : R.toHypermap.Dart).tail
    letI : Fintype C := C.supp.toFinite.fintype
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    have htarget :
        ((Rcomp C).toHypermap).EulerPlanar :=
      (Hypermap.dual_eulerPlanar_iff (G := (Rcomp C).toHypermap)).mp
        (hcomp C)
    have hcomponent :
        (R.toHypermap.componentHypermap c).EulerPlanar := by
      let φ := componentRotationSystem_componentHypermapIso (G := G) Rcomp c
      simpa [R, C] using (φ.eulerPlanar_iff).mpr htarget
    have heq :
        (R.toHypermap.componentHypermap c).eulerLeft =
          (R.toHypermap.componentHypermap c).eulerRight :=
      Hypermap.euler_eq_of_evenGenus_planar
        (G := R.toHypermap.componentHypermap c)
        (Hypermap.evenGenus (R.toHypermap.componentHypermap c))
        hcomponent
    exact le_of_eq heq
  exact (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mpr hprimal

/-- Node orbits of the componentwise rotation system split as the sum of the
node orbits of the component rotation systems.  This is the first count-level
component gluing lemma that avoids choosing a representative dart component. -/
theorem componentRotationSystem_nodeOrbitCount_eq_sum
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    Nat.card (PermOrbit R.node) =
      ∑ C : G.ConnectedComponent, Nat.card (PermOrbit (Rcomp C).node) := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  let E : OrientedEdge G ≃ Sigma (ComponentOrientedEdgeFiber G) :=
    orientedEdgeComponentFiberSigmaEquiv (G := G)
  let π : forall C : G.ConnectedComponent,
      Equiv.Perm (ComponentOrientedEdgeFiber G C) :=
    fun C => (componentOrientedEdgeFiberEquiv (G := G) C).permCongr
      (Rcomp C).node
  let P : Equiv.Perm (Sigma (ComponentOrientedEdgeFiber G)) :=
    sigmaPerm (ComponentOrientedEdgeFiber G) π
  have hconj :
      forall x : OrientedEdge G, E (R.node x) = P (E x) := by
    intro x
    simp [R, E, P, π, componentRotationSystem]
  calc
    Nat.card (PermOrbit R.node) =
        Nat.card (PermOrbit P) :=
      Nat.card_congr (permOrbitEquivOfConj E R.node P hconj)
    _ = ∑ C : G.ConnectedComponent, Nat.card (PermOrbit (π C)) := by
      exact sigmaPerm_orbitCount_eq_sum (β := ComponentOrientedEdgeFiber G) π
    _ = ∑ C : G.ConnectedComponent,
          Nat.card (PermOrbit (Rcomp C).node) := by
      apply Finset.sum_congr rfl
      intro C _hC
      let F := componentOrientedEdgeFiberEquiv (G := G) C
      have hconjC :
          forall x : OrientedEdge C.toSimpleGraph,
            F ((Rcomp C).node x) = π C (F x) := by
        intro x
        simp [F, π]
      exact (Nat.card_congr
        (permOrbitEquivOfConj F (Rcomp C).node (π C) hconjC)).symm

/-- Edge count decomposes as the sum of component edge counts.  The component
counts are stated as `Nat.card edgeSet`, avoiding typeclass arguments in the
theorem statement. -/
theorem edgeFinset_card_eq_sum_connectedComponent_edgeSet_natCard
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    G.edgeFinset.card =
      ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet := by
  classical
  letI (C : G.ConnectedComponent) : Fintype C := C.supp.toFinite.fintype
  haveI (C : G.ConnectedComponent) :
      DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have hcard := Fintype.card_congr
    (orientedEdgeComponentFiberSigmaEquiv (G := G))
  rw [Fintype.card_sigma] at hcard
  have hleft : Fintype.card (OrientedEdge G) = 2 * G.edgeFinset.card :=
    orientedEdge_card_eq_twice_card_edges (G := G)
  have hright :
      (∑ C : G.ConnectedComponent,
          Fintype.card (ComponentOrientedEdgeFiber G C)) =
        ∑ C : G.ConnectedComponent, 2 * Nat.card C.toSimpleGraph.edgeSet := by
    apply Finset.sum_congr rfl
    intro C _
    calc
      Fintype.card (ComponentOrientedEdgeFiber G C) =
          Fintype.card (OrientedEdge C.toSimpleGraph) :=
        Fintype.card_congr (componentOrientedEdgeFiberEquiv (G := G) C).symm
      _ = 2 * C.toSimpleGraph.edgeFinset.card :=
        orientedEdge_card_eq_twice_card_edges (G := C.toSimpleGraph)
      _ = 2 * Nat.card C.toSimpleGraph.edgeSet := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  rw [hleft, hright, ← Finset.mul_sum] at hcard
  omega

/-- Edge orbits of the componentwise rotation system split as the sum of the
edge orbits of the component graphs. -/
theorem componentRotationSystem_edgeOrbitCount_eq_sum
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Rcomp : forall C : G.ConnectedComponent, RotationSystem C.toSimpleGraph) :
    let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
    Nat.card (PermOrbit R.toHypermap.edge) =
      ∑ C : G.ConnectedComponent,
        Nat.card (PermOrbit (OrientedEdge.edgePerm C.toSimpleGraph)) := by
  classical
  let R : RotationSystem G := componentRotationSystem (G := G) Rcomp
  have hglobal :
      Nat.card (PermOrbit R.toHypermap.edge) = G.edgeFinset.card := by
    simpa [Hypermap.edgeOrbitCount] using
      R.edgeOrbitCount_eq_edgeFinset_card
  change Nat.card (PermOrbit R.toHypermap.edge) =
    ∑ C : G.ConnectedComponent,
      Nat.card (PermOrbit (OrientedEdge.edgePerm C.toSimpleGraph))
  rw [hglobal, edgeFinset_card_eq_sum_connectedComponent_edgeSet_natCard]
  apply Finset.sum_congr rfl
  intro C _hC
  letI : Fintype C := C.supp.toFinite.fintype
  haveI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have hlocal :
      Nat.card (PermOrbit (OrientedEdge.edgePerm C.toSimpleGraph)) =
        C.toSimpleGraph.edgeFinset.card := by
    simpa [Hypermap.edgeOrbitCount] using
      (Rcomp C).edgeOrbitCount_eq_edgeFinset_card
  rw [hlocal, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
end FourColor

end Schematic.Math.GraphTheory
