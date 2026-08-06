import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.Foundations
import Schematic.Math.GraphTheory.Embedding.FaceOrbit

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph
instance K33Graph.instDecidableAdj : DecidableRel K33Graph.Adj := by
  intro x y
  cases x <;> cases y
  · exact isFalse id
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id

theorem RotationSystem.node_ne_self_of_min_degree_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hdegree : forall v : V, 2 <= G.degree v) :
    forall d : OrientedEdge G, R.node d ≠ d := by
  classical
  intro d hfixed
  have hcard : 1 < (G.neighborSet d.tail).ncard := by
    have hdegree_card :
        (G.neighborSet d.tail).ncard = G.degree d.tail := by
      rw [← Set.fintypeCard_eq_ncard,
        SimpleGraph.card_neighborSet_eq_degree]
    have hddegree := hdegree d.tail
    omega
  obtain ⟨w, hw, hwne⟩ :=
    (G.neighborSet d.tail).exists_ne_of_one_lt_ncard hcard d.head
  let f : OrientedEdge G := ⟨(d.tail, w), hw⟩
  have hreach : PermReachable R.node d f :=
    R.node_orbit_of_same_tail d f rfl
  have hfd : f = d :=
    PermSkip.eq_of_permReachable_fixed R.node hfixed
      (PermReachable.symm R.node hreach)
  exact hwne (by
    have := congrArg (fun e : OrientedEdge G => e.head) hfd
    simpa [f] using this)

theorem RotationSystem.face_arity_ge_three_of_node_ne_self
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hnode : forall d : OrientedEdge G, R.node d ≠ d)
    (e : OrientedEdge G) :
    3 <= R.toHypermap.arity e := by
  have hpos := R.toHypermap.arity_pos e
  by_contra hlt
  have hle : R.toHypermap.arity e <= 2 := by omega
  have harity : R.toHypermap.arity e = 1 ∨
      R.toHypermap.arity e = 2 := by omega
  rcases harity with harity | harity
  · have hreturn := R.toHypermap.face_iterate_arity e
    rw [harity] at hreturn
    simp only [Function.iterate_one] at hreturn
    have htail := R.toHypermap_face_tail e
    rw [hreturn] at htail
    exact e.adj.ne htail
  · have hreturn := R.toHypermap.face_iterate_arity e
    rw [harity] at hreturn
    have hreturn' :
        R.toHypermap.face (R.toHypermap.face e) = e := by
      simpa [Function.iterate_succ_apply] using hreturn
    let f := R.toHypermap.face e
    have hftail : f.tail = e.head := R.toHypermap_face_tail e
    have hfhead : f.head = e.tail := by
      have h := R.toHypermap_face_tail f
      rw [show R.toHypermap.face f = e by simpa [f] using hreturn'] at h
      exact h.symm
    have hfe : f = e.symm := by
      apply Subtype.ext
      apply Prod.ext
      · exact hftail
      · exact hfhead
    have hface : R.toHypermap.face e = e.symm := hfe
    change R.node.symm e.symm = e.symm at hface
    have hfixed : R.node e.symm = e.symm := by
      apply_fun R.node at hface
      simpa using hface.symm
    exact hnode e.symm hfixed

theorem RotationSystem.face_arity_ge_three_of_min_degree_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hdegree : forall v : V, 2 <= G.degree v)
    (e : OrientedEdge G) :
    3 <= R.toHypermap.arity e :=
  R.face_arity_ge_three_of_node_ne_self
    (R.node_ne_self_of_min_degree_two hdegree) e

theorem RotationSystem.face_arity_ge_four_of_min_degree_two_triangle_free
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hdegree : forall v : V, 2 <= G.degree v)
    (htriangle : forall a b c : V,
      G.Adj a b -> G.Adj b c -> Not (G.Adj c a))
    (e : OrientedEdge G) :
    4 <= R.toHypermap.arity e := by
  have hthree := R.face_arity_ge_three_of_min_degree_two hdegree e
  by_contra hfour
  have harity : R.toHypermap.arity e = 3 := by omega
  have hreturn := R.toHypermap.face_iterate_arity e
  rw [harity] at hreturn
  have hreturn' :
      R.toHypermap.face
          (R.toHypermap.face (R.toHypermap.face e)) = e := by
    simpa [Function.iterate_succ_apply] using hreturn
  let f := R.toHypermap.face e
  let g := R.toHypermap.face f
  have hab : G.Adj e.tail e.head := e.adj
  have hbc : G.Adj e.head f.head := by
    have hf := f.adj
    have htail : f.tail = e.head := R.toHypermap_face_tail e
    simpa [htail] using hf
  have hca : G.Adj f.head e.tail := by
    have hg := g.adj
    have hgtail : g.tail = f.head := R.toHypermap_face_tail f
    have hghead : g.head = e.tail := by
      have h := R.toHypermap_face_tail g
      rw [show R.toHypermap.face g = e by simpa [g, f] using hreturn'] at h
      exact h.symm
    simpa [hgtail, hghead] using hg
  exact htriangle e.tail e.head f.head hab hbc hca

theorem Hypermap.mul_faceOrbitCount_le_card_dart_of_arity_ge
    (G : Hypermap)
    (k : Nat)
    (h : forall x : G.Dart, k <= G.arity x) :
    k * G.faceOrbitCount <= Fintype.card G.Dart := by
  have hsum :
      (∑ o : G.FaceOrbit, k) <=
        ∑ o : G.FaceOrbit, G.arity (Quotient.out o) := by
    exact Finset.sum_le_sum (fun o _ => h (Quotient.out o))
  rw [G.sum_arity_faceOrbit_eq_card_dart] at hsum
  simpa [Hypermap.faceOrbitCount, Nat.card_eq_fintype_card,
    Nat.mul_comm] using hsum

theorem K5Graph_preconnected : K5Graph.Preconnected := by
  intro x y
  by_cases hxy : x = y
  · subst y
    exact SimpleGraph.Reachable.rfl
  · exact (by simpa [K5Graph, CompleteGraphOn] using hxy :
      K5Graph.Adj x y).reachable

theorem K33Graph_preconnected : K33Graph.Preconnected := by
  intro x y
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          exact
            (show K33Graph.Adj (Sum.inl i) (Sum.inr 0) by
              simp [K33Graph]).reachable.trans
            (show K33Graph.Adj (Sum.inr 0) (Sum.inl j) by
              simp [K33Graph]).reachable
      | inr j =>
          exact (show K33Graph.Adj (Sum.inl i) (Sum.inr j) by
            simp [K33Graph]).reachable
  | inr i =>
      cases y with
      | inl j =>
          exact (show K33Graph.Adj (Sum.inr i) (Sum.inl j) by
            simp [K33Graph]).reachable
      | inr j =>
          exact
            (show K33Graph.Adj (Sum.inr i) (Sum.inl 0) by
              simp [K33Graph]).reachable.trans
            (show K33Graph.Adj (Sum.inl 0) (Sum.inr j) by
              simp [K33Graph]).reachable

theorem not_hasEulerRotationSystem_K5Graph :
    Not (HasEulerRotationSystem K5Graph) := by
  rintro ⟨R, hRdual⟩
  have hedgeCard : K5Graph.edgeFinset.card = 10 := by
    simpa [K5Graph, CompleteGraphOn] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin 5))
  have hsupport : K5Graph.support = Set.univ := by
    ext x
    simp [K5Graph, CompleteGraphOn]
  have hsupportCard : Fintype.card K5Graph.support = 5 := by
    rw [support_card_eq_of_support_eq_univ (G := K5Graph) hsupport]
    simp
  letI : Nonempty K5Graph.support :=
    ⟨⟨0, by rw [SimpleGraph.mem_support]; exact ⟨1, by simp⟩⟩⟩
  have hcomponent : R.toHypermap.componentCount = 1 := by
    rw [R.componentCount_eq_supportComponent_card]
    exact supportComponent_card_eq_one_of_preconnected_nonempty
      (G := K5Graph)
      (support_preconnected_of_preconnected
        (G := K5Graph) K5Graph_preconnected)
  have hedge : R.toHypermap.edgeOrbitCount = 10 := by
    rw [R.edgeOrbitCount_eq_edgeFinset_card, hedgeCard]
  have hnode : R.toHypermap.nodeOrbitCount = 5 := by
    rw [R.nodeOrbitCount_eq_support_card, hsupportCard]
  have hdart : Fintype.card R.toHypermap.Dart = 20 := by
    change Fintype.card (OrientedEdge K5Graph) = 20
    rw [orientedEdge_card_eq_twice_card_edges, hedgeCard]
  have hprimal : R.toHypermap.EulerPlanar :=
    R.toHypermap.dual_eulerPlanar_iff.mp hRdual
  have heuler : R.toHypermap.eulerLeft = R.toHypermap.eulerRight :=
    Hypermap.euler_eq_of_evenGenus_planar
      (Hypermap.evenGenus R.toHypermap) hprimal
  have hfaceLower : 3 * R.toHypermap.faceOrbitCount <= 20 := by
    rw [← hdart]
    exact R.toHypermap.mul_faceOrbitCount_le_card_dart_of_arity_ge 3
      (R.face_arity_ge_three_of_min_degree_two
        (fun v => by rw [K5Graph_degree]; omega))
  unfold Hypermap.eulerLeft Hypermap.eulerRight at heuler
  rw [hcomponent, hedge, hnode, hdart] at heuler
  omega

theorem not_hasEulerRotationSystem_K33Graph :
    Not (HasEulerRotationSystem K33Graph) := by
  rintro ⟨R, hRdual⟩
  have hedgeCard : K33Graph.edgeFinset.card = 9 := by decide
  have hsupport : K33Graph.support = Set.univ := by
    ext x
    rw [SimpleGraph.mem_support]
    constructor
    · intro _
      trivial
    · intro _
      exact K33Graph_exists_adj x
  have hsupportCard : Fintype.card K33Graph.support = 6 := by
    rw [support_card_eq_of_support_eq_univ (G := K33Graph) hsupport]
    exact card_K33Vertex
  letI : Nonempty K33Graph.support :=
    ⟨⟨Sum.inl 0, by
      rw [SimpleGraph.mem_support]
      exact ⟨Sum.inr 0, by simp [K33Graph]⟩⟩⟩
  have hcomponent : R.toHypermap.componentCount = 1 := by
    rw [R.componentCount_eq_supportComponent_card]
    exact supportComponent_card_eq_one_of_preconnected_nonempty
      (G := K33Graph)
      (support_preconnected_of_preconnected
        (G := K33Graph) K33Graph_preconnected)
  have hedge : R.toHypermap.edgeOrbitCount = 9 := by
    rw [R.edgeOrbitCount_eq_edgeFinset_card, hedgeCard]
  have hnode : R.toHypermap.nodeOrbitCount = 6 := by
    rw [R.nodeOrbitCount_eq_support_card, hsupportCard]
  have hdart : Fintype.card R.toHypermap.Dart = 18 := by
    change Fintype.card (OrientedEdge K33Graph) = 18
    rw [orientedEdge_card_eq_twice_card_edges, hedgeCard]
  have htriangle : forall a b c : K33Vertex,
      K33Graph.Adj a b -> K33Graph.Adj b c ->
        Not (K33Graph.Adj c a) := by
    intro a b c hab hbc hca
    cases a <;> cases b <;> cases c <;> simp_all [K33Graph]
  have hprimal : R.toHypermap.EulerPlanar :=
    R.toHypermap.dual_eulerPlanar_iff.mp hRdual
  have heuler : R.toHypermap.eulerLeft = R.toHypermap.eulerRight :=
    Hypermap.euler_eq_of_evenGenus_planar
      (Hypermap.evenGenus R.toHypermap) hprimal
  have hfaceLower : 4 * R.toHypermap.faceOrbitCount <= 18 := by
    rw [← hdart]
    exact R.toHypermap.mul_faceOrbitCount_le_card_dart_of_arity_ge 4
      (R.face_arity_ge_four_of_min_degree_two_triangle_free
        (fun v => by rw [K33Graph_degree]; omega) htriangle)
  unfold Hypermap.eulerLeft Hypermap.eulerRight at heuler
  rw [hcomponent, hedge, hnode, hdart] at heuler
  omega


end Schematic.Math.GraphTheory.FourColor
