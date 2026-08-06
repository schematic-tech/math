import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.NeighborFaces
import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.FacialCycles
import Schematic.Math.GraphTheory.Connectivity

/-!
Extraction of facial graph cycles and the merged face used in the three-connected branch.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemVertexDeletion

/-- In a vertex-simple face orbit, the two orientations of an edge cannot
share a face when node orbits have no fixed darts. -/
theorem not_faceReachable_symm_of_faceOrbitsVertexSimple
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (hsimple : FaceOrbitsVertexSimple R)
    (e : OrientedEdge G) :
    ¬ PermReachable (R.toHypermap).face e e.symm := by
  intro he
  have hfaceE :
      PermReachable (R.toHypermap).face
        ((R.toHypermap).face e) e.symm := by
    have hback :
        PermReachable (R.toHypermap).face
          ((R.toHypermap).face e) e := by
      simpa using
        PermReachable.backward (R.toHypermap).face
          ((R.toHypermap).face e)
    exact
      PermReachable.trans (R.toHypermap).face hback he
  have htail :
      ((R.toHypermap).face e).tail = e.symm.tail := by
    exact R.toHypermap_face_tail e
  have hfaceEq : (R.toHypermap).face e = e.symm :=
    (hsimple hfaceE).1 htail
  have hfixedSymm : R.node.symm e.symm = e.symm := by
    simpa using hfaceEq
  have hfixed : R.node e.symm = e.symm := by
    apply R.node.symm.injective
    simp [hfixedSymm]
  exact hnode e.symm hfixed

/-- A vertex-simple face orbit is itself a simple graph cycle.  The returned
walk retains every dart of the orbit, unlike the generic `toPath` extractor
which may discard repeated vertices. -/
theorem exists_isCycle_darts_iff_faceReachable
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (hsimple : FaceOrbitsVertexSimple R)
    (e : OrientedEdge G) :
    ∃ c : G.Walk e.tail e.tail,
      c.IsCycle ∧
        ∀ z : OrientedEdge G,
          orientedEdgeDartEquiv z ∈ c.darts ↔
            PermReachable (R.toHypermap).face e z := by
  classical
  rcases
      Hypermap.exists_ordered_faceOrbitCycle
        (G := R.toHypermap) e with
    ⟨p, hpFace, hpClose, hpNodup, hpMem⟩
  have hpNe : p ≠ [] := by
    intro hp
    subst p
    have hface : (R.toHypermap).face e = e := by
      simpa [List.getLastD] using hpClose
    have htail := R.toHypermap_face_tail e
    rw [hface] at htail
    exact e.adj.ne htail
  cases p with
  | nil =>
      exact (hpNe rfl).elim
  | cons d p =>
    have hed :
        (R.toHypermap).face e = d := by
      exact
        ((Hypermap.FacePath.cons
          (G := R.toHypermap) e d p).mp hpFace).1
    have hdp :
        (R.toHypermap).FacePath d p := by
      exact
        ((Hypermap.FacePath.cons
          (G := R.toHypermap) e d p).mp hpFace).2
    have hchainFace :
        List.IsChain
          (fun a b : OrientedEdge G =>
            (R.toHypermap).face a = b)
          (d :: p) :=
      (Hypermap.FacePath.iff_isChain R.toHypermap).mp hdp
    let dartEquiv : OrientedEdge G ≃ G.Dart :=
      orientedEdgeDartEquiv (G := G)
    let ds : List G.Dart := (d :: p).map dartEquiv
    have hchainOriented :
        List.IsChain
          (fun a b : OrientedEdge G =>
            G.DartAdj (dartEquiv a) (dartEquiv b))
          (d :: p) := by
      exact hchainFace.imp (fun {a b} hab => by
        change a.head = b.tail
        rw [← hab]
        exact (R.toHypermap_face_tail a).symm)
    have hchain :
        List.IsChain G.DartAdj ds := by
      exact (List.isChain_map dartEquiv).mpr hchainOriented
    have hdsNe : ds ≠ [] := by
      simp [ds]
    let q0 :=
      SimpleGraph.Walk.ofDarts ds hdsNe hchain
    have hdTail : d.tail = e.head := by
      rw [← hed]
      exact R.toHypermap_face_tail e
    have hlastFace :
        (R.toHypermap).face ((d :: p).getLastD d) = e := by
      simpa [List.getLastD] using hpClose
    have hlastHead :
        ((d :: p).getLastD d).head = e.tail := by
      have htail :=
        R.toHypermap_face_tail ((d :: p).getLastD d)
      rw [hlastFace] at htail
      exact htail.symm
    have hq0Start :
        (ds.head hdsNe).fst = e.head := by
      simpa [ds, dartEquiv, orientedEdgeDartEquiv] using hdTail
    have hq0End :
        (ds.getLast hdsNe).snd = e.tail := by
      simpa [ds, dartEquiv, orientedEdgeDartEquiv] using hlastHead
    let q : G.Walk e.head e.tail :=
      q0.copy hq0Start hq0End
    let c : G.Walk e.tail e.tail :=
      SimpleGraph.Walk.cons e.adj q
    have hqDarts : q.darts = ds := by
      simp [q, q0]
    have hcDarts :
        c.darts = (e :: d :: p).map dartEquiv := by
      rw [show c.darts =
          orientedEdgeDartEquiv e :: q.darts by
        rfl, hqDarts]
      change dartEquiv e :: ds = (e :: d :: p).map dartEquiv
      rw [show ds = dartEquiv d :: p.map dartEquiv by
        exact List.map_cons]
      rw [List.map_cons, List.map_cons]
    have hheadNodup :
        ((e :: d :: p).map OrientedEdge.head).Nodup := by
      apply List.Nodup.map_on
      · intro a ha b hb hab
        have hea :
            PermReachable (R.toHypermap).face e a :=
          (hpMem a).mp ha
        have heb :
            PermReachable (R.toHypermap).face e b :=
          (hpMem b).mp hb
        have habReach :
            PermReachable (R.toHypermap).face a b :=
          PermReachable.trans (R.toHypermap).face
            (PermReachable.symm (R.toHypermap).face hea) heb
        exact (hsimple habReach).2 hab
      · exact hpNodup
    have htailSupport : c.support.tail.Nodup := by
      rw [← SimpleGraph.Walk.map_snd_darts, hcDarts]
      simpa [dartEquiv, orientedEdgeDartEquiv] using hheadNodup
    have hedgeNodup :
        ((e :: d :: p).map
          (fun z : OrientedEdge G => s(z.tail, z.head))).Nodup := by
      apply List.Nodup.map_on
      · intro a ha b hb hab
        have hea :
            PermReachable (R.toHypermap).face e a :=
          (hpMem a).mp ha
        have heb :
            PermReachable (R.toHypermap).face e b :=
          (hpMem b).mp hb
        have hba :
            PermReachable (R.toHypermap).face b a :=
          PermReachable.trans (R.toHypermap).face
            (PermReachable.symm (R.toHypermap).face heb) hea
        have habDart :
            (orientedEdgeDartEquiv a).edge =
              (orientedEdgeDartEquiv b).edge := by
          simpa [orientedEdgeDartEquiv, SimpleGraph.Dart.edge] using hab
        rcases
            (SimpleGraph.dart_edge_eq_iff
              (orientedEdgeDartEquiv a)
              (orientedEdgeDartEquiv b)).mp habDart with
          habEq | habSymm
        · exact (orientedEdgeDartEquiv (G := G)).injective habEq
        · have haEq : a = b.symm := by
            apply (orientedEdgeDartEquiv (G := G)).injective
            simpa [orientedEdgeDartEquiv] using habSymm
          apply False.elim
          exact
            (not_faceReachable_symm_of_faceOrbitsVertexSimple
              R hnode hsimple b) (by simpa [haEq] using hba)
      · exact hpNodup
    have hedges : c.edges.Nodup := by
      change (c.darts.map SimpleGraph.Dart.edge).Nodup
      rw [hcDarts]
      simpa [List.map_map, dartEquiv, orientedEdgeDartEquiv,
        SimpleGraph.Dart.edge] using hedgeNodup
    have hc : c.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_def]
      exact ⟨⟨hedges⟩, by simp [c], htailSupport⟩
    refine ⟨c, hc, ?_⟩
    intro z
    rw [hcDarts, List.mem_map]
    constructor
    · rintro ⟨a, ha, haz⟩
      have haEq : a = z :=
        (orientedEdgeDartEquiv (G := G)).injective haz
      subst a
      exact (hpMem z).mp ha
    · intro hz
      exact ⟨z, (hpMem z).mpr hz, rfl⟩

private theorem isFacialCycle_of_darts_iff_faceReachable
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (e : OrientedEdge G)
    {c : G.Walk e.tail e.tail}
    (hc : c.IsCycle)
    (hmem :
      ∀ z : OrientedEdge G,
        orientedEdgeDartEquiv z ∈ c.darts ↔
          PermReachable (R.toHypermap).face e z) :
    RotationSystemGluing.IsFacialCycle R c hc := by
  have hfirstForward : CycleForwardDart c (cycleFirstDart c hc) :=
    cycleForwardDart_first c hc
  have hfirstMem :
      orientedEdgeDartEquiv (cycleFirstDart c hc) ∈ c.darts :=
    (cycleForwardDart_iff_mem_darts c (cycleFirstDart c hc)).mp
      hfirstForward
  have heFirst :
      PermReachable (R.toHypermap).face e (cycleFirstDart c hc) :=
    (hmem (cycleFirstDart c hc)).mp hfirstMem
  intro z
  rw [cycleForwardDart_iff_mem_darts, hmem]
  constructor
  · intro hez
    exact PermReachable.trans (R.toHypermap).face
      (PermReachable.symm (R.toHypermap).face heFirst) hez
  · intro hfirstZ
    exact PermReachable.trans (R.toHypermap).face heFirst hfirstZ

/-- A vertex-simple face orbit is represented by a directed facial cycle, not
merely by an abstract simple cycle with the same support. -/
theorem exists_isFacialCycle_of_faceOrbitsVertexSimple
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (hsimple : FaceOrbitsVertexSimple R)
    (e : OrientedEdge G) :
    Exists fun c : G.Walk e.tail e.tail =>
      Exists fun hc : c.IsCycle =>
        RotationSystemGluing.IsFacialCycle R c hc := by
  classical
  rcases exists_isCycle_darts_iff_faceReachable R hnode hsimple e with
    ⟨c, hc, hmem⟩
  exact
    ⟨c, hc,
      isFacialCycle_of_darts_iff_faceReachable R e hc hmem⟩

/-- The merged facial cycle in Coq's three-connected `wagner3` branch.
Select a contractible edge, recursively embed its collapse, delete the
collapsed vertex, and retain the complete face containing every surviving
port formerly incident with that vertex. -/
theorem IsThreeConnected.exists_contractibleEdge_mergedFaceCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hG : IsThreeConnected G)
    (hcard : 4 < Nat.card V)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        letI : DecidableRel
            (GraphContraction.collapseEdge G hab).graph.Adj :=
          Classical.decRel _
        Exists fun R :
            RotationSystem
              (GraphContraction.collapseEdge G hab).graph =>
          (R.toHypermap).dual.EulerPlanar) :
    Exists fun a : V =>
      Exists fun b : V =>
        Exists fun hab : G.Adj a b =>
          letI : DecidableRel
              (GraphContraction.collapseEdge G hab).graph.Adj :=
            Classical.decRel _
          Exists fun hthree :
              IsThreeConnected
                (GraphContraction.collapseEdge G hab).graph =>
            Exists fun R :
                RotationSystem
                  (GraphContraction.collapseEdge G hab).graph =>
              (R.toHypermap).dual.EulerPlanar ∧
                Exists fun u :
                    (({(none :
                        (GraphContraction.collapseEdge G hab).Target)} :
                      Set (GraphContraction.collapseEdge G hab).Target)ᶜ :
                      Set (GraphContraction.collapseEdge G hab).Target) =>
                  Exists fun c :
                      ((GraphContraction.collapseEdge G hab).graph.induce
                        ({(none :
                            (GraphContraction.collapseEdge G hab).Target)} :
                          Set
                            (GraphContraction.collapseEdge G hab).Target)ᶜ).Walk
                        u u =>
                    Exists fun hc : c.IsCycle =>
                      RotationSystemGluing.IsFacialCycle
                          (vertexDeletedRotationSystem R
                            (none :
                              (GraphContraction.collapseEdge G hab).Target))
                          c hc ∧
                        forall
                        (x : OrientedEdge
                          (GraphContraction.collapseEdge G hab).graph)
                        (hx :
                          x.tail =
                            (none :
                              (GraphContraction.collapseEdge G hab).Target)),
                        orientedEdgeDartEquiv
                            (vertexDeletedFacePort R
                              (none :
                                (GraphContraction.collapseEdge G hab).Target)
                              (node_ne_self_of_isTwoConnected R
                                (IsKConnected.mono (by omega) hthree))
                              x hx) ∈
                          c.darts := by
  classical
  rcases hG.exists_adj_collapseEdge_isThreeConnected hcard with
    ⟨a, b, hab, hthree⟩
  let C : GraphContraction G :=
    GraphContraction.collapseEdge G hab
  letI : DecidableRel C.graph.Adj := Classical.decRel _
  have htwo : IsTwoConnected C.graph :=
    IsKConnected.mono (by omega) hthree
  have hcardC : 1 < Fintype.card C.Target := by
    have hthreeCard : 3 < Nat.card C.Target := hthree.1
    simpa [Nat.card_eq_fintype_card] using
      (show 1 < Nat.card C.Target by omega)
  letI : Nontrivial C.Target :=
    Fintype.one_lt_card_iff_nontrivial.mp hcardC
  let collapsed : C.Target := none
  obtain ⟨y, hcollapsedY⟩ :=
    hthree.connected (by decide) |>.preconnected.exists_adj_of_nontrivial
      collapsed
  let x0 : OrientedEdge C.graph :=
    ⟨(collapsed, y), hcollapsedY⟩
  have hx0 : x0.tail = collapsed := rfl
  rcases hcontract hab with ⟨R, hR⟩
  let D : RotationSystem
      (C.graph.induce ({collapsed} : Set C.Target)ᶜ) :=
    vertexDeletedRotationSystem R collapsed
  have htwoDeleted :
      IsTwoConnected
        (C.graph.induce ({collapsed} : Set C.Target)ᶜ) :=
    hthree.delete_vertex_isTwoConnected collapsed
  have hDdual : (D.toHypermap).dual.EulerPlanar := by
    exact vertexDeletedRotationSystem_dual_eulerPlanar R collapsed hR
  have hDprimal : (D.toHypermap).EulerPlanar :=
    (D.toHypermap.dual_eulerPlanar_iff).mp hDdual
  have hsimple : FaceOrbitsVertexSimple D :=
    faceOrbitsVertexSimple_of_isTwoConnected_eulerPlanar
      D htwoDeleted hDprimal
  let p0 : OrientedEdge
      (C.graph.induce ({collapsed} : Set C.Target)ᶜ) :=
    vertexDeletedFacePort R collapsed
      (node_ne_self_of_isTwoConnected R htwo) x0 hx0
  rcases
      exists_isCycle_darts_iff_faceReachable D
        (node_ne_self_of_isTwoConnected D htwoDeleted)
        hsimple p0 with
    ⟨c, hc, hcycleMem⟩
  have hfacial : RotationSystemGluing.IsFacialCycle D c hc :=
    isFacialCycle_of_darts_iff_faceReachable D p0 hc hcycleMem
  refine ⟨a, b, hab, hthree, R, hR, p0.tail, c, hc, hfacial, ?_⟩
  intro x hx
  have hportReach :
      PermReachable D.toHypermap.face p0
        (vertexDeletedFacePort R collapsed
          (node_ne_self_of_isTwoConnected R htwo) x hx) := by
    exact
      vertexDeletedFacePort_faceReachable_of_isTwoConnected_dualEulerPlanar
        R htwo hR collapsed x0 x hx0 hx
  exact (hcycleMem _).mpr hportReach

/-- Coq `hcycle.v`/`embedding.v` face-cycle consequence in Lean walk form:
every edge of a selected face in a two-connected Euler-planar rotation lies
on a simple graph cycle carried by that face orbit. -/
theorem exists_isCycle_edge_mem_faceOrbit_of_isTwoConnected_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (h2 : IsTwoConnected G)
    (hR : (R.toHypermap).EulerPlanar)
    (e : OrientedEdge G) :
    ∃ u : V, ∃ c : G.Walk u u,
      c.IsCycle ∧
        s(e.tail, e.head) ∈ c.edges ∧
          ∀ f ∈ c.edges,
            ∃ d : OrientedEdge G,
              PermReachable (R.toHypermap).face e d ∧
                f = s(d.tail, d.head) := by
  apply R.exists_isCycle_edge_mem_of_not_faceReachable_symm e
  exact
    not_faceReachable_symm_of_faceOrbitsVertexSimple R
      (node_ne_self_of_isTwoConnected R h2)
      (faceOrbitsVertexSimple_of_isTwoConnected_eulerPlanar R h2 hR)
      e

/-- Dual-planarity form of the face-cycle extractor. -/
theorem exists_isCycle_edge_mem_faceOrbit_of_isTwoConnected_dualEulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (h2 : IsTwoConnected G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    (e : OrientedEdge G) :
    ∃ u : V, ∃ c : G.Walk u u,
      c.IsCycle ∧
        s(e.tail, e.head) ∈ c.edges ∧
          ∀ f ∈ c.edges,
            ∃ d : OrientedEdge G,
              PermReachable (R.toHypermap).face e d ∧
                f = s(d.tail, d.head) := by
  exact
    exists_isCycle_edge_mem_faceOrbit_of_isTwoConnected_eulerPlanar
      R h2 (R.toHypermap.dual_eulerPlanar_iff.mp hR) e


end RotationSystemVertexDeletion

end FourColor

end Schematic.Math.GraphTheory
