import Schematic.Math.GraphTheory.Minors.Society.RuralGluing.ComplementaryBoundary

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The union of the two side boundary-augmented graphs is exactly the
ambient boundary-augmented society graph.  The common cut path occurs in both
side polygons, while the two complementary paths together are precisely the
ambient boundary polygon. -/
theorem DiskRuralCertificate.sideAugmented_sup_eq_ambientAugmented
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C₁ : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (C₂ : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (hleftArc : P.leftBoundaryArc.Nonempty)
    (hrightArc : P.rightBoundaryArc.Nonempty)
    (a : (boundaryAugmentedGraphOfLength
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
          (C₁.n + 3) C₁.boundary_length).Walk P.t P.s)
    (haDarts :
      let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
      let c := L.boundaryCycleWalkOfLength C₁.n C₁.boundary_length
      a.darts = c.darts.drop (P.path.length + 1) ++ c.darts.take 1)
    (b : (boundaryAugmentedGraphOfLength
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
          (C₂.n + 3) C₂.boundary_length).Walk P.s P.t)
    (hbDarts :
      let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
      let d := R.boundaryCycleWalkOfLength C₂.n C₂.boundary_length
      b.darts =
        d.darts.drop (P.path.reverse.length + 1) ++ d.darts.take 1)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    let A₁ := L.boundaryAugmentedGraphOfLength
      (C₁.n + 3) C₁.boundary_length
    let A₂ := R.boundaryAugmentedGraphOfLength
      (C₂.n + 3) C₂.boundary_length
    A₁ ⊔ A₂ = S.boundaryAugmentedGraphOfLength (n + 3) hlength := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₁ := GeneralSociety.boundaryAugmentedGraphOfLength
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
      (C₁.n + 3) C₁.boundary_length
  let A₂ := GeneralSociety.boundaryAugmentedGraphOfLength
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
      (C₂.n + 3) C₂.boundary_length
  let c : (A₁ ⊔ A₂).Walk P.t P.t :=
    (a.mapLe (show A₁ ≤ A₁ ⊔ A₂ from le_sup_left)).append
      (b.mapLe (show A₂ ≤ A₁ ⊔ A₂ from le_sup_right))
  have haSupport :
      a.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s] :=
    C₁.leftComplementaryPath_support P hno_cross a haDarts
  have hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t] :=
    C₂.rightComplementaryPath_support P hno_cross b hbDarts
  have hleftCycle :
      L.boundary.cycleGraphOfLength (C₁.n + 3) C₁.boundary_length =
        P.pathEdgeGraph ⊔ a.toSubgraph.spanningCoe := by
    simpa [L] using
      C₁.leftBoundaryCycle_eq_path_sup_complement
        P hno_cross hleftArc a haDarts
  have hrightCycle :
      R.boundary.cycleGraphOfLength (C₂.n + 3) C₂.boundary_length =
        P.pathEdgeGraph ⊔ b.toSubgraph.spanningCoe := by
    simpa [R] using
      C₂.rightBoundaryCycle_eq_path_sup_complement
        P hno_cross hrightArc b hbDarts
  have hcSpan :
      c.toSubgraph.spanningCoe =
        S.boundary.cycleGraphOfLength (n + 3) hlength := by
    simpa only [c] using
      P.complementaryAppend_spans_boundaryCycle a b haSupport hbSupport
        hleftArc n hlength
  have hcAppendSpan :
      c.toSubgraph.spanningCoe =
        a.toSubgraph.spanningCoe ⊔ b.toSubgraph.spanningCoe := by
    ext x y
    simp [c, SimpleGraph.Walk.toSubgraph_append,
      SimpleGraph.Subgraph.spanningCoe_adj,
      SimpleGraph.Walk.adj_toSubgraph_mapLe]
  have hboundaryCycle :
      S.boundary.cycleGraphOfLength (n + 3) hlength =
        a.toSubgraph.spanningCoe ⊔ b.toSubgraph.spanningCoe :=
    hcSpan.symm.trans hcAppendSpan
  have hgraph :
      S.graph = L.graph ⊔ R.graph ⊔ P.pathEdgeGraph := by
    simpa [L, R] using
      GMIX24Split.canonicalOfNoCross_graph_eq_split_sup_pathEdgeGraph
        P hno_cross
  change
    (L.graph ⊔
        L.boundary.cycleGraphOfLength (C₁.n + 3) C₁.boundary_length) ⊔
      (R.graph ⊔
        R.boundary.cycleGraphOfLength (C₂.n + 3) C₂.boundary_length) =
      S.graph ⊔ S.boundary.cycleGraphOfLength (n + 3) hlength
  rw [hleftCycle, hrightCycle, hgraph, hboundaryCycle]
  ext x y
  simp only [SimpleGraph.sup_adj]
  tauto

/-- If the left open boundary arc is empty, the right side augmentation is
missing exactly the direct ambient boundary edge between the cut endpoints.
The cut path itself remains in the right side polygon, while the retained
right complementary path supplies every other ambient boundary edge. -/
theorem DiskRuralCertificate.rightAugmented_sup_endpointEdge_eq_ambientAugmented
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (hleftEmpty : P.leftBoundaryArc = ∅)
    (hrightArc : P.rightBoundaryArc.Nonempty)
    (b : (boundaryAugmentedGraphOfLength
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
          (C.n + 3) C.boundary_length).Walk P.s P.t)
    (hbDarts :
      let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
      let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
      b.darts =
        d.darts.drop (P.path.reverse.length + 1) ++ d.darts.take 1)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    let A₂ := R.boundaryAugmentedGraphOfLength
      (C.n + 3) C.boundary_length
    A₂ ⊔ SimpleGraph.edge P.t P.s =
      S.boundaryAugmentedGraphOfLength (n + 3) hlength := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₂ := R.boundaryAugmentedGraphOfLength
    (C.n + 3) C.boundary_length
  let E := SimpleGraph.edge P.t P.s
  have hts : E.Adj P.t P.s := by
    rw [SimpleGraph.edge_adj]
    exact ⟨Or.inl ⟨rfl, rfl⟩, P.s_ne_t.symm⟩
  let a : E.Walk P.t P.s := hts.toWalk
  have hleftList : P.leftBoundaryArcList = [] :=
    P.leftBoundaryArcList_eq_nil_of_leftBoundaryArc_eq_empty hleftEmpty
  have haSupport :
      a.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s] := by
    simp [a, hleftList]
  have hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t] :=
    C.rightComplementaryPath_support P hno_cross b hbDarts
  let c : (E ⊔ A₂).Walk P.t P.t :=
    (a.mapLe (show E ≤ E ⊔ A₂ from le_sup_left)).append
      (b.mapLe (show A₂ ≤ E ⊔ A₂ from le_sup_right))
  have hc : c.IsCycle := by
    simpa [c] using
      P.complementaryAppend_isCycle_of_arc_nonempty
        a b haSupport hbSupport (Or.inr hrightArc)
  let w := S.boundaryCycleWalkOfLength n hlength
  have hw : w.IsCycle :=
    S.boundaryCycleWalkOfLength_isCycle n hlength
  have htailRotated : c.support.tail ~r w.support.tail := by
    simpa [c, w] using
      P.complementaryAppend_tail_isRotated_boundaryCycle
        a b haSupport hbSupport n hlength
  have hcSpan :
      c.toSubgraph.spanningCoe =
        S.boundary.cycleGraphOfLength (n + 3) hlength := by
    calc
      c.toSubgraph.spanningCoe = w.toSubgraph.spanningCoe :=
        SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_isCycle_tail_isRotated
          c w hc hw htailRotated
      _ = S.boundary.cycleGraphOfLength (n + 3) hlength :=
        S.boundaryCycleWalkOfLength_toSubgraph_spanningCoe n hlength
  have hcAppendSpan :
      c.toSubgraph.spanningCoe =
        a.toSubgraph.spanningCoe ⊔ b.toSubgraph.spanningCoe := by
    ext x y
    simp [c, SimpleGraph.Walk.toSubgraph_append,
      SimpleGraph.Subgraph.spanningCoe_adj,
      SimpleGraph.Walk.adj_toSubgraph_mapLe]
  have haSpan : a.toSubgraph.spanningCoe = E := by
    ext x y
    simp [a, E, SimpleGraph.edge_adj]
  have hboundaryCycle :
      S.boundary.cycleGraphOfLength (n + 3) hlength =
        E ⊔ b.toSubgraph.spanningCoe := by
    calc
      S.boundary.cycleGraphOfLength (n + 3) hlength =
          c.toSubgraph.spanningCoe := hcSpan.symm
      _ = a.toSubgraph.spanningCoe ⊔ b.toSubgraph.spanningCoe :=
        hcAppendSpan
      _ = E ⊔ b.toSubgraph.spanningCoe := by rw [haSpan]
  have hrightCycle :
      R.boundary.cycleGraphOfLength (C.n + 3) C.boundary_length =
        P.pathEdgeGraph ⊔ b.toSubgraph.spanningCoe := by
    simpa [R] using
      C.rightBoundaryCycle_eq_path_sup_complement
        P hno_cross hrightArc b hbDarts
  have hleftGraph :
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph = ⊥ := by
    simpa [GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross,
      GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical] using
      P.leftGraph_eq_bot_of_leftBoundaryArc_eq_empty hleftEmpty
  have hgraph : S.graph = R.graph ⊔ P.pathEdgeGraph := by
    have hsplit :=
      GMIX24Split.canonicalOfNoCross_graph_eq_split_sup_pathEdgeGraph
        P hno_cross
    rw [hleftGraph] at hsplit
    simpa [R] using hsplit
  change
    (R.graph ⊔
        R.boundary.cycleGraphOfLength (C.n + 3) C.boundary_length) ⊔ E =
      S.graph ⊔ S.boundary.cycleGraphOfLength (n + 3) hlength
  rw [hrightCycle, hgraph, hboundaryCycle]
  ext x y
  simp only [SimpleGraph.sup_adj]
  tauto

/-- For a nontrivial induced cut path, the endpoint chord is absent from the
right marked side graph.  The side graph itself has no edge between cut-path
vertices; in the marked polygon the chord could only be a cut-path edge or an
edge of the complementary boundary path, and either possibility would force
the corresponding simple path to have length one. -/
theorem DiskRuralCertificate.not_adj_rightAugmented_cutEndpoints_of_path_length_ne_one
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (hrightArc : P.rightBoundaryArc.Nonempty)
    (b : (boundaryAugmentedGraphOfLength
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
          (C.n + 3) C.boundary_length).Walk P.s P.t)
    (hb : b.IsPath)
    (hbDarts :
      let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
      let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
      b.darts =
        d.darts.drop (P.path.reverse.length + 1) ++ d.darts.take 1)
    (hpathLength : P.path.length ≠ 1) :
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    let A₂ := R.boundaryAugmentedGraphOfLength
      (C.n + 3) C.boundary_length
    Not (A₂.Adj P.s P.t) := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₂ := R.boundaryAugmentedGraphOfLength
    (C.n + 3) C.boundary_length
  have hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t] :=
    C.rightComplementaryPath_support P hno_cross b hbDarts
  have hrightCycle :
      R.boundary.cycleGraphOfLength (C.n + 3) C.boundary_length =
        P.pathEdgeGraph ⊔ b.toSubgraph.spanningCoe := by
    simpa [R] using
      C.rightBoundaryCycle_eq_path_sup_complement
        P hno_cross hrightArc b hbDarts
  change Not (A₂.Adj P.s P.t)
  intro hst
  have hst' : R.graph.Adj P.s P.t ∨
      (R.boundary.cycleGraphOfLength
        (C.n + 3) C.boundary_length).Adj P.s P.t := by
    simpa [A₂, R, boundaryAugmentedGraphOfLength] using hst
  rcases hst' with hside | hpolygon
  · have hright : P.rightGraph.Adj P.s P.t := by
      simpa [R, GMIX24Split.canonicalOfNoCross,
        GMIX24Split.ofCanonicalGraphsOfNoCross,
        GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical] using hside
    exact P.rightGraph_not_adj_between_path_vertices
      P.s_mem_pathSet P.t_mem_pathSet hright
  · rw [hrightCycle] at hpolygon
    rcases hpolygon with hpath | hboundary
    · exact hpathLength
        (_root_.Schematic.Math.GraphTheory.SimpleGraph.Walk.IsPath.length_eq_one_of_endpoints_mem_edges
          P.path_isPath hpath.2)
    · have hmem : s(P.s, P.t) ∈ b.edges := by
        simpa [SimpleGraph.Subgraph.spanningCoe_adj,
          SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges] using hboundary
      have hbLength : b.length = 1 :=
        _root_.Schematic.Math.GraphTheory.SimpleGraph.Walk.IsPath.length_eq_one_of_endpoints_mem_edges
          hb hmem
      rcases hrightArc with ⟨z, hz⟩
      have hzSupport : z ∈ b.support := by
        rw [hbSupport]
        simp only [List.mem_cons, List.mem_append, List.mem_reverse]
        exact Or.inl (Or.inr (P.mem_rightBoundaryArcList.mpr hz))
      rw [_root_.Schematic.Math.GraphTheory.SimpleGraph.Walk.support_eq_pair_of_length_eq_one
        b hbLength] at hzSupport
      simp at hzSupport
      rcases hzSupport with hzs | hzt
      · exact P.rightBoundaryArc_ne_s hz hzs
      · exact P.rightBoundaryArc_ne_t hz hzt

/-- Degenerate gluing when the left boundary arc is empty and the cut path is
already the single endpoint edge.  In this case the right augmented graph is
the ambient augmented graph, and its marked boundary differs from the ambient
canonical boundary only by a cyclic change of basepoint. -/
theorem DiskRuralCertificate.exists_ambient_of_rightCertificate_leftArc_empty_length_one
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (hleftEmpty : P.leftBoundaryArc = ∅)
    (hrightArc : P.rightBoundaryArc.Nonempty)
    (hpathLength : P.path.length = 1)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    Nonempty (DiskRuralCertificate S) := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₂ := R.boundaryAugmentedGraphOfLength
    (C.n + 3) C.boundary_length
  let A := S.boundaryAugmentedGraphOfLength (n + 3) hlength
  let E := SimpleGraph.edge P.t P.s
  letI : DecidableRel A₂.Adj := Classical.decRel _
  letI : DecidableRel A.Adj := Classical.decRel _
  rcases C.exists_rightComplementaryPath P hno_cross hrightArc with
    ⟨b, hb, hbDarts⟩
  have hrightCycle :
      R.boundary.cycleGraphOfLength (C.n + 3) C.boundary_length =
        P.pathEdgeGraph ⊔ b.toSubgraph.spanningCoe := by
    simpa [R] using
      C.rightBoundaryCycle_eq_path_sup_complement
        P hno_cross hrightArc b hbDarts
  have hpathAdj : P.pathEdgeGraph.Adj P.t P.s := by
    refine ⟨(P.path.adj_of_length_eq_one hpathLength).symm, ?_⟩
    rw [_root_.Schematic.Math.GraphTheory.SimpleGraph.Walk.edges_eq_singleton_of_length_eq_one
      P.path hpathLength]
    simp [Sym2.eq_swap]
  have hA₂Adj : A₂.Adj P.t P.s := by
    change R.graph.Adj P.t P.s ∨
      (R.boundary.cycleGraphOfLength
        (C.n + 3) C.boundary_length).Adj P.t P.s
    exact Or.inr (by rw [hrightCycle]; exact Or.inl hpathAdj)
  have hedgeSup : A₂ ⊔ E = A₂ := by
    exact SimpleGraph.sup_edge_of_adj (G := A₂) hA₂Adj
  have hgraph : A₂ = A := by
    calc
      A₂ = A₂ ⊔ E := hedgeSup.symm
      _ = A := by
        simpa [A₂, A, E] using
          C.rightAugmented_sup_endpointEdge_eq_ambientAugmented
            P hno_cross hleftEmpty hrightArc b hbDarts n hlength
  let phi : A ≃g A₂ :=
    FourColor.RotationSystemFan.graphIsoOfEq hgraph.symm
  let Rambient : FourColor.RotationSystem A :=
    FourColor.RotationSystem.ofIso phi C.rotation
  let psi : FourColor.Hypermap.Iso
      Rambient.toHypermap C.rotation.toHypermap :=
    FourColor.RotationSystem.ofIso_toHypermapIso phi C.rotation
  have hRambient : Rambient.toHypermap.dual.EulerPlanar := by
    have hSidePrimal : C.rotation.toHypermap.EulerPlanar :=
      (FourColor.Hypermap.dual_eulerPlanar_iff
        (G := C.rotation.toHypermap)).mp C.dual_eulerPlanar
    have hAmbientPrimal : Rambient.toHypermap.EulerPlanar :=
      (psi.eulerPlanar_iff).mpr hSidePrimal
    exact
      (FourColor.Hypermap.dual_eulerPlanar_iff
        (G := Rambient.toHypermap)).mpr hAmbientPrimal
  let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
  have hd : d.IsCycle :=
    R.boundaryCycleWalkOfLength_isCycle C.n C.boundary_length
  let dAmbient : A.Walk
      (phi.symm (R.boundary.embeddingOfLength
        (C.n + 3) C.boundary_length 0))
      (phi.symm (R.boundary.embeddingOfLength
        (C.n + 3) C.boundary_length 0)) :=
    d.map phi.symm.toHom
  have hdAmbient : dAmbient.IsCycle :=
    SimpleGraph.Walk.IsCycle.map
      (p := d) (f := phi.symm.toHom) phi.symm.toEquiv.injective hd
  have hdAmbientFacial :
      FourColor.RotationSystemGluing.IsFacialCycle
        Rambient dAmbient hdAmbient := by
    simpa [Rambient, dAmbient, hdAmbient] using
      FourColor.RotationSystemFan.isFacialCycle_ofIso
        phi C.rotation d hd C.boundary_facial
  let w := S.boundaryCycleWalkOfLength n hlength
  have hw : w.IsCycle :=
    S.boundaryCycleWalkOfLength_isCycle n hlength
  have hdAmbientSupport : dAmbient.support = d.support := by
    change (d.map phi.symm.toHom).support = d.support
    rw [SimpleGraph.Walk.support_map]
    simp [phi, FourColor.RotationSystemFan.graphIsoOfEq]
  have hdTail :
      d.support.tail =
        P.path.support.reverse ++ P.rightBoundaryArcList.reverse := by
    rw [show d.support =
        (R.boundary.cycleWalkOfLength C.n C.boundary_length).support by
      exact R.boundaryCycleWalkOfLength_support C.n C.boundary_length]
    rw [R.boundary.cycleWalkOfLength_support C.n C.boundary_length]
    simp only [List.tail_cons]
    simp [R, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross,
      GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical,
      GMIX24CutPath.rightOrderedCutBoundary,
      GMIX24CutPath.rightOrderedCutBoundaryVertices]
  have hpSupport : P.path.support = [P.s, P.t] :=
    _root_.Schematic.Math.GraphTheory.SimpleGraph.Walk.support_eq_pair_of_length_eq_one
      P.path hpathLength
  have hwTail : w.support.tail = S.boundary.vertices.reverse := by
    rw [show w.support =
        (S.boundary.cycleWalkOfLength n hlength).support by
      exact S.boundaryCycleWalkOfLength_support n hlength]
    rw [S.boundary.cycleWalkOfLength_support n hlength]
    simp only [List.tail_cons]
  have hleftList : P.leftBoundaryArcList = [] :=
    P.leftBoundaryArcList_eq_nil_of_leftBoundaryArc_eq_empty hleftEmpty
  have hboundaryRotated :
      S.boundary.vertices ~r
        (P.s :: P.t :: P.rightBoundaryArcList) := by
    simpa [hleftList] using
      (show S.boundary.vertices ~r
          (P.s :: P.leftBoundaryArcList ++
            P.t :: P.rightBoundaryArcList) from
        ⟨S.boundary.indexOf P.s, P.boundary_rotate_start_eq_arcs⟩)
  have hreverse :
      S.boundary.vertices.reverse ~r
        P.rightBoundaryArcList.reverse ++ [P.t, P.s] := by
    simpa [List.reverse_append, List.append_assoc] using
      hboundaryRotated.reverse
  have hswap :
      P.rightBoundaryArcList.reverse ++ [P.t, P.s] ~r
        [P.t, P.s] ++ P.rightBoundaryArcList.reverse :=
    List.isRotated_append
  have hwToSide : w.support.tail ~r dAmbient.support.tail := by
    rw [hwTail, hdAmbientSupport, hdTail, hpSupport, List.reverse_cons,
      List.reverse_singleton]
    simpa [List.append_assoc] using hreverse.trans hswap
  have hwFacial :
      FourColor.RotationSystemGluing.IsFacialCycle Rambient w hw :=
    FourColor.RotationSystemFan.isFacialCycle_of_tailSupport_isRotated
      Rambient dAmbient hdAmbient hdAmbientFacial w hw hwToSide
  exact ⟨{
    n := n
    boundary_length := hlength
    rotation := Rambient
    dual_eulerPlanar := by simpa [A] using hRambient
    boundary_facial := by simpa [A, w, hw] using hwFacial
  }⟩

/-- Degenerate gluing when the left open boundary arc is empty and the
induced cut path has more than one edge.  The right marked disk is missing
exactly the endpoint boundary edge.  Insert that edge across its marked outer
face; the complementary split face is the ambient boundary polygon. -/
theorem DiskRuralCertificate.exists_ambient_of_rightCertificate_leftArc_empty_length_ne_one
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (hleftEmpty : P.leftBoundaryArc = ∅)
    (hrightArc : P.rightBoundaryArc.Nonempty)
    (hpathLength : P.path.length ≠ 1)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    Nonempty (DiskRuralCertificate S) := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₂ := R.boundaryAugmentedGraphOfLength
    (C.n + 3) C.boundary_length
  let A := S.boundaryAugmentedGraphOfLength (n + 3) hlength
  let E := SimpleGraph.edge P.s P.t
  let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
  letI : DecidableRel A₂.Adj := Classical.decRel _
  letI : DecidableRel A.Adj := Classical.decRel _
  letI : DecidableRel
      (FourColor.RotationSystemFan.addNodeGraph A₂
        (insert P.s ({P.t} : Set V))).Adj := Classical.decRel _
  rcases C.exists_rightCutFaceSplit P hno_cross hrightArc with
    ⟨p, hp, hpSupport, hproper, ⟨D⟩⟩
  have hpLength : p.length = P.path.reverse.length := by
    have h := congrArg List.length hpSupport
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_support] at h
    omega
  have hd : d.IsCycle :=
    R.boundaryCycleWalkOfLength_isCycle C.n C.boundary_length
  have hpSegment :
      p.support = ((d.drop 1).take p.length).support := by
    calc
      p.support = P.path.reverse.support := hpSupport
      _ = ((d.drop 1).take P.path.reverse.length).support := by
        symm
        calc
          ((d.drop 1).take P.path.reverse.length).support =
              (((R.boundary.cycleWalkOfLength
                C.n C.boundary_length).drop 1).take
                  P.path.reverse.length).support :=
            R.boundaryCycleWalkOfLength_drop_take_support
              C.n C.boundary_length 1 P.path.reverse.length
          _ = P.path.reverse.support := by
            simpa [R, GMIX24Split.canonicalOfNoCross,
              GMIX24Split.ofCanonicalGraphsOfNoCross,
              GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical] using
              P.rightOrderedCutBoundary_cycle_segment_support
                C.n C.boundary_length
      _ = ((d.drop 1).take p.length).support := by rw [hpLength]
  have hproper' : p.length + 1 < d.length := by
    simpa [hpLength, d, R] using hproper
  rcases D.exists_complementaryPath hd hpSegment hproper' with
    ⟨b, hb, hbDarts, hbOriented⟩
  have hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t] :=
    C.rightComplementaryPath_support P hno_cross b
      (by simpa [hpLength] using hbDarts)
  have hnotA₂ : Not (A₂.Adj P.s P.t) := by
    apply C.not_adj_rightAugmented_cutEndpoints_of_path_length_ne_one
      P hno_cross hrightArc b hb
    · simpa [hpLength] using hbDarts
    · exact hpathLength
  have hgraph : A₂ ⊔ E = A := by
    simpa [A₂, A, E, SimpleGraph.edge_comm] using
      C.rightAugmented_sup_endpointEdge_eq_ambientAugmented
        P hno_cross hleftEmpty hrightArc b
          (by simpa [hpLength] using hbDarts) n hlength
  have hAAdj : A.Adj P.s P.t := by
    rw [← hgraph]
    exact Or.inr (by
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, P.s_ne_t⟩)
  have hdel : FourColor.EdgeDeletion.deletedGraph A P.s P.t = A₂ := by
    rw [← hgraph]
    ext x y
    simp only [FourColor.EdgeDeletion.deletedGraph,
      SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxy | hxy, hne⟩
      · exact hxy
      · exact False.elim (hne hxy.1)
    · intro hxy
      refine ⟨Or.inl hxy, ?_⟩
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hxs, hyt⟩ | ⟨hxt, hys⟩
      · subst x
        subst y
        exact hnotA₂ hxy
      · subst x
        subst y
        exact hnotA₂ hxy.symm
  let OE := FourColor.orientedEdgeDartEquiv (G := A₂)
  let pds : List (FourColor.OrientedEdge A₂) := p.darts.map OE.symm
  let B₀ := FourColor.RotationSystemFan.orderedFacialCycleBoundary
    C.rotation d hd C.boundary_facial
  have hB₀full :
      B₀.first :: B₀.rest =
        D.closing :: (pds ++ D.next :: D.outer) := by
    rw [show B₀.first :: B₀.rest =
        d.darts.map OE.symm by
      simpa [B₀, OE] using
        FourColor.RotationSystemFan.orderedFacialCycleBoundary_darts
          C.rotation d hd C.boundary_facial]
    simpa [pds, OE] using D.ordered_darts
  have hB₀first : B₀.first = D.closing :=
    (List.cons.inj hB₀full).1
  have hB₀rest : B₀.rest = pds ++ D.next :: D.outer :=
    (List.cons.inj hB₀full).2
  let B : FourColor.RotationSystemFan.FaceBoundary C.rotation.toHypermap :=
    B₀.rotateFromRest D.next pds D.outer hB₀rest
  let pre : List (FourColor.OrientedEdge A₂) := D.outer ++ [D.closing]
  have hpNotNil : ¬p.Nil := p.not_nil_of_ne P.s_ne_t.symm
  have hpdsNe : pds ≠ [] := by
    simp [pds, OE,
      SimpleGraph.Walk.darts_eq_nil.not.mpr hpNotNil]
  let q : FourColor.OrientedEdge A₂ := pds.head hpdsNe
  let post : List (FourColor.OrientedEdge A₂) := pds.tail
  have hpdsCons : pds = q :: post := by
    exact (List.cons_head_tail hpdsNe).symm
  have hBrest : B.rest = pre ++ q :: post := by
    have hrot :=
      FourColor.RotationSystemFan.FaceBoundary.rotateFromRest_rest
        B₀ D.next pds D.outer hB₀rest
    rw [hB₀first] at hrot
    rw [show B.rest = D.outer ++ D.closing :: pds by exact hrot]
    rw [hpdsCons]
    simp [pre, List.append_assoc]
  have hbNotNil : ¬b.Nil := b.not_nil_of_ne P.s_ne_t
  have hBprefix :
      B.first :: pre =
        b.darts.map (FourColor.orientedEdgeDartEquiv (G := A₂)).symm := by
    rw [show B.first = D.next by rfl]
    simpa [pre, List.append_assoc] using hbOriented.symm
  have hBtail : B.first.tail = P.s :=
    FourColor.RotationSystemFan.FaceBoundary.first_tail_eq_walk_from
      B b hbNotNil pre hBprefix
  have hqtail : q.tail = P.t :=
    FourColor.RotationSystemFan.FaceBoundary.next_tail_eq_walk_to
      C.rotation B q pre post hBrest b hbNotNil hBprefix
  rcases
      FourColor.RotationSystemFan.exists_addEdgeSplitBoundaries_of_deletedGraph_eq
        hAAdj hdel C.rotation C.dual_eulerPlanar B q pre post
          hBrest hBtail hqtail with
    ⟨Rambient, hRambient, _retained, complementary,
      _hretainedTail, hcomplementaryTail, lift,
      hliftTail, hliftHead, _hretainedRest, hcomplementaryRest⟩
  have hA₂le : A₂ ≤ A := by
    rw [← hgraph]
    exact le_sup_left
  let a : A.Walk P.t P.s := hAAdj.symm.toWalk
  let bA : A.Walk P.s P.t := b.mapLe hA₂le
  let c : A.Walk P.t P.t := a.append bA
  have hbA : bA.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hA₂le hb
  have hbNoEndpoint : s(P.t, P.s) ∉ bA.edges := by
    intro he
    have he' : s(P.t, P.s) ∈ b.edges := by
      simpa [bA, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact hnotA₂ (b.adj_of_mem_edges he').symm
  have hc : c.IsCycle := by
    simpa [c, a] using
      (SimpleGraph.Walk.cons_isCycle_iff bA hAAdj.symm).mpr
        ⟨hbA, hbNoEndpoint⟩
  have hcomplementaryHead : complementary.first.head = P.s := by
    have hstep :
        Rambient.toHypermap.face complementary.first = lift B.first := by
      have hpath := complementary.path
      rw [hcomplementaryRest] at hpath
      exact hpath.1
    calc
      complementary.first.head =
          (Rambient.toHypermap.face complementary.first).tail :=
        (Rambient.toHypermap_face_tail complementary.first).symm
      _ = (lift B.first).tail := congrArg FourColor.OrientedEdge.tail hstep
      _ = B.first.tail := hliftTail B.first
      _ = P.s := hBtail
  let newDart : FourColor.OrientedEdge A :=
    ⟨(P.t, P.s), hAAdj.symm⟩
  have hcomplementaryFirst : complementary.first = newDart := by
    apply FourColor.orientedEdge_eq_of_tail_head
    · exact hcomplementaryTail
    · exact hcomplementaryHead
  let oldLift : FourColor.OrientedEdge A₂ -> FourColor.OrientedEdge A :=
    FourColor.RotationSystemGluing.liftOrientedEdge hA₂le
  have hliftEq : forall e : FourColor.OrientedEdge A₂,
      lift e = oldLift e := by
    intro e
    apply FourColor.orientedEdge_eq_of_tail_head
    · simpa [oldLift] using hliftTail e
    · simpa [oldLift] using hliftHead e
  have hrestList :
      complementary.rest =
        (b.darts.map
          (FourColor.orientedEdgeDartEquiv (G := A₂)).symm).map oldLift := by
    calc
      complementary.rest = lift B.first :: pre.map lift :=
        hcomplementaryRest
      _ = (B.first :: pre).map lift := by rfl
      _ = (b.darts.map
            (FourColor.orientedEdgeDartEquiv (G := A₂)).symm).map lift := by
        rw [hBprefix]
      _ = (b.darts.map
            (FourColor.orientedEdgeDartEquiv (G := A₂)).symm).map oldLift := by
        apply List.map_congr_left
        intro e _he
        exact hliftEq e
  have hbAOriented :
      bA.darts.map
          (FourColor.orientedEdgeDartEquiv (G := A)).symm =
        (b.darts.map
          (FourColor.orientedEdgeDartEquiv (G := A₂)).symm).map oldLift := by
    simpa [bA, oldLift] using
      FourColor.RotationSystemGluing.walkMapLe_orientedDarts hA₂le b
  have haOriented :
      a.darts.map
          (FourColor.orientedEdgeDartEquiv (G := A)).symm = [newDart] := by
    rfl
  have hcOriented :
      c.darts.map
          (FourColor.orientedEdgeDartEquiv (G := A)).symm =
        newDart ::
          (b.darts.map
            (FourColor.orientedEdgeDartEquiv (G := A₂)).symm).map oldLift := by
    rw [show c.darts = a.darts ++ bA.darts by
      exact SimpleGraph.Walk.darts_append a bA]
    rw [List.map_append, haOriented, hbAOriented]
    rfl
  have hfaceList :
      complementary.first :: complementary.rest =
        c.darts.map
          (FourColor.orientedEdgeDartEquiv (G := A)).symm := by
    rw [hcomplementaryFirst, hrestList]
    exact hcOriented.symm
  let OA := FourColor.orientedEdgeDartEquiv (G := A)
  let cds : List (FourColor.OrientedEdge A) := c.darts.map OA.symm
  have hcDartsNe : c.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hc.not_nil
  have hcdsNe : cds ≠ [] := by simp [cds, hcDartsNe]
  have hcdsFirst : cds.head hcdsNe =
      FourColor.cycleFirstDart c hc := by
    apply OA.injective
    rw [List.head_map, OA.apply_symm_apply]
    rw [← c.firstDart_eq_head_darts hc.not_nil]
    apply SimpleGraph.Dart.ext
    exact calc
      (c.firstDart hc.not_nil).toProd = (P.t, c.snd) :=
        c.firstDart_toProd hc.not_nil
      _ = (OA (FourColor.cycleFirstDart c hc)).toProd := by
        apply Prod.ext
        · exact
            (FourColor.cycleFirstDart_tail c hc).symm
        · rfl
  have hcdsCons : cds =
      FourColor.cycleFirstDart c hc :: cds.tail := by
    calc
      cds = cds.head hcdsNe :: cds.tail := (List.cons_head_tail hcdsNe).symm
      _ = FourColor.cycleFirstDart c hc :: cds.tail := by
        rw [hcdsFirst]
  have hfaceFirst : complementary.first =
      FourColor.cycleFirstDart c hc := by
    have hlist : complementary.first :: complementary.rest = cds := by
      simpa [cds, OA] using hfaceList
    rw [hcdsCons] at hlist
    exact (List.cons.inj hlist).1
  have hcFacial :
      FourColor.RotationSystemGluing.IsFacialCycle Rambient c hc :=
    complementary.isFacialCycle_of_eq_cycleDarts
      c hc hfaceFirst hfaceList
  let Ewalk : E.Walk P.t P.s := by
    have hts : E.Adj P.t P.s := by
      rw [SimpleGraph.edge_adj]
      exact ⟨by simp, P.s_ne_t.symm⟩
    exact hts.toWalk
  let c₀ : (E ⊔ A₂).Walk P.t P.t :=
    (Ewalk.mapLe (show E ≤ E ⊔ A₂ from le_sup_left)).append
      (b.mapLe (show A₂ ≤ E ⊔ A₂ from le_sup_right))
  have hleftList : P.leftBoundaryArcList = [] :=
    P.leftBoundaryArcList_eq_nil_of_leftBoundaryArc_eq_empty hleftEmpty
  have hEwalkSupport :
      Ewalk.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s] := by
    simp [Ewalk, hleftList]
  have hc₀Tail :
      c₀.support.tail ~r
        (S.boundaryCycleWalkOfLength n hlength).support.tail := by
    simpa [c₀] using
      P.complementaryAppend_tail_isRotated_boundaryCycle
        Ewalk b hEwalkSupport hbSupport n hlength
  have hcSupport : c.support = c₀.support := by
    simp [c, c₀, a, bA, Ewalk,
      SimpleGraph.Walk.support_mapLe_eq_support]
  let w := S.boundaryCycleWalkOfLength n hlength
  have hw : w.IsCycle :=
    S.boundaryCycleWalkOfLength_isCycle n hlength
  have hwToC : w.support.tail ~r c.support.tail := by
    rw [hcSupport]
    simpa [w] using hc₀Tail.symm
  have hwFacial :
      FourColor.RotationSystemGluing.IsFacialCycle Rambient w hw :=
    FourColor.RotationSystemFan.isFacialCycle_of_tailSupport_isRotated
      Rambient c hc hcFacial w hw hwToC
  exact ⟨{
    n := n
    boundary_length := hlength
    rotation := Rambient
    dual_eulerPlanar := by simpa [A] using hRambient
    boundary_facial := by simpa [A, w, hw] using hwFacial
  }⟩

/-- Complete left-empty-arc constructor, dispatching according to whether the
cut path itself is already the missing endpoint edge. -/
theorem DiskRuralCertificate.exists_ambient_of_rightCertificate_leftArc_empty
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (hleftEmpty : P.leftBoundaryArc = ∅)
    (hrightArc : P.rightBoundaryArc.Nonempty)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    Nonempty (DiskRuralCertificate S) := by
  by_cases hpath : P.path.length = 1
  · exact C.exists_ambient_of_rightCertificate_leftArc_empty_length_one
      P hno_cross hleftEmpty hrightArc hpath n hlength
  · exact C.exists_ambient_of_rightCertificate_leftArc_empty_length_ne_one
      P hno_cross hleftEmpty hrightArc hpath n hlength

/-- Symmetric complete constructor for an empty right boundary arc.  It is the
left-empty construction applied to the reversed cut path, with the canonical
right society transported to the original left society. -/
theorem DiskRuralCertificate.exists_ambient_of_leftCertificate_rightArc_empty
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (hrightEmpty : P.rightBoundaryArc = ∅)
    (hleftArc : P.leftBoundaryArc.Nonempty)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    Nonempty (DiskRuralCertificate S) := by
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).rightSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_rightSociety P hno_cross
  have Crev : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).rightSociety := by
    rw [hSoc]
    exact C
  exact Crev.exists_ambient_of_rightCertificate_leftArc_empty
    P.reverse hno_cross (by simpa using hrightEmpty)
      (by simpa using hleftArc) n hlength

/-- Glue two marked side disks along a nondegenerate induced cut path.

The auxiliary vertex used by the rotation-system cycle sum is deleted before
the result is returned.  The two retained complementary faces then merge to
the canonical ambient boundary face, and the exact side-graph union theorem
transports the resulting rotation to the ambient boundary augmentation. -/
theorem DiskRuralCertificate.exists_ambient_of_sideCertificates_bothArcs
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C₁ : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (C₂ : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (hleftArc : P.leftBoundaryArc.Nonempty)
    (hrightArc : P.rightBoundaryArc.Nonempty)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    Nonempty (DiskRuralCertificate S) := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₁ := L.boundaryAugmentedGraphOfLength
    (C₁.n + 3) C₁.boundary_length
  let A₂ := R.boundaryAugmentedGraphOfLength
    (C₂.n + 3) C₂.boundary_length
  let H₁ := FourColor.RotationSystemFan.addNodeGraph A₁
    (insert P.t ({P.s} : Set V))
  let H₂ := FourColor.RotationSystemFan.addNodeGraph A₂
    (insert P.s ({P.t} : Set V))
  let A := S.boundaryAugmentedGraphOfLength (n + 3) hlength
  letI : DecidableRel A₁.Adj := Classical.decRel _
  letI : DecidableRel A₂.Adj := Classical.decRel _
  letI : DecidableRel H₁.Adj := Classical.decRel _
  letI : DecidableRel H₂.Adj := Classical.decRel _
  letI : DecidableRel (H₁ ⊔ H₂).Adj := inferInstance
  letI : DecidableRel (A₁ ⊔ A₂).Adj := Classical.decRel _
  letI : DecidableRel A.Adj := Classical.decRel _
  rcases
      C₁.exists_canonicalFreshCycleSum hthree P hno_cross C₂
        hleftArc hrightArc with
    ⟨a, ha, haDarts, b, hb, hbDarts, hsectorsNodup,
      U, hU, haFacial, hbFacial⟩
  have haSupport :
      a.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s] :=
    C₁.leftComplementaryPath_support P hno_cross a haDarts
  have hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t] :=
    C₂.rightComplementaryPath_support P hno_cross b hbDarts
  let c : (A₁ ⊔ A₂).Walk P.t P.t :=
    (a.mapLe (show A₁ ≤ A₁ ⊔ A₂ from le_sup_left)).append
      (b.mapLe (show A₂ ≤ A₁ ⊔ A₂ from le_sup_right))
  have hc : c.IsCycle := by
    simpa [c] using
      P.complementaryAppend_isCycle_of_arc_nonempty
        a b haSupport hbSupport (Or.inl hleftArc)
  rcases
      FourColor.RotationSystemGluing.exists_oldUnion_facialAppend_of_fresh_path_faces
        (insert P.t ({P.s} : Set V))
        (insert P.s ({P.t} : Set V))
        (by simp) (by simp) (by simp) (by simp)
        P.s_ne_t a ha b hb U hU haFacial hbFacial hsectorsNodup hc with
    ⟨R₀, hR₀, hcFacial⟩
  have hgraph : A₁ ⊔ A₂ = A := by
    simpa [A₁, A₂, A] using
      C₁.sideAugmented_sup_eq_ambientAugmented P hno_cross C₂
        hleftArc hrightArc a haDarts b hbDarts n hlength
  let phi : A ≃g (A₁ ⊔ A₂) :=
    FourColor.RotationSystemFan.graphIsoOfEq hgraph.symm
  let Rambient : FourColor.RotationSystem A :=
    FourColor.RotationSystem.ofIso phi R₀
  let psi : FourColor.Hypermap.Iso Rambient.toHypermap R₀.toHypermap :=
    FourColor.RotationSystem.ofIso_toHypermapIso phi R₀
  have hRambient : Rambient.toHypermap.dual.EulerPlanar := by
    have hR₀Primal : R₀.toHypermap.EulerPlanar :=
      (FourColor.Hypermap.dual_eulerPlanar_iff
        (G := R₀.toHypermap)).mp hR₀
    have hAmbientPrimal : Rambient.toHypermap.EulerPlanar :=
      (psi.eulerPlanar_iff).mpr hR₀Primal
    exact
      (FourColor.Hypermap.dual_eulerPlanar_iff
        (G := Rambient.toHypermap)).mpr hAmbientPrimal
  let cAmbient : A.Walk P.t P.t := c.map phi.symm.toHom
  have hcAmbient : cAmbient.IsCycle :=
    SimpleGraph.Walk.IsCycle.map
      (p := c) (f := phi.symm.toHom) phi.symm.toEquiv.injective hc
  have hcAmbientFacial :
      FourColor.RotationSystemGluing.IsFacialCycle
        Rambient cAmbient hcAmbient := by
    simpa [Rambient, cAmbient, hcAmbient] using
      FourColor.RotationSystemFan.isFacialCycle_ofIso
        phi R₀ c hc hcFacial
  let w := S.boundaryCycleWalkOfLength n hlength
  have hw : w.IsCycle :=
    S.boundaryCycleWalkOfLength_isCycle n hlength
  have hcAmbientSupport : cAmbient.support = c.support := by
    change (c.map phi.symm.toHom).support = c.support
    rw [SimpleGraph.Walk.support_map]
    simp [phi, FourColor.RotationSystemFan.graphIsoOfEq]
  have hcTailRotated : c.support.tail ~r w.support.tail := by
    simpa [c, w] using
      P.complementaryAppend_tail_isRotated_boundaryCycle
        a b haSupport hbSupport n hlength
  have hwTailRotated : w.support.tail ~r cAmbient.support.tail := by
    rw [hcAmbientSupport]
    exact hcTailRotated.symm
  have hwFacial :
      FourColor.RotationSystemGluing.IsFacialCycle Rambient w hw :=
    FourColor.RotationSystemFan.isFacialCycle_of_tailSupport_isRotated
      Rambient cAmbient hcAmbient hcAmbientFacial w hw hwTailRotated
  exact ⟨{
    n := n
    boundary_length := hlength
    rotation := Rambient
    dual_eulerPlanar := by simpa [A] using hRambient
    boundary_facial := by simpa [A, w, hw] using hwFacial
  }⟩

end GeneralSociety

end Schematic.Math.GraphTheory
