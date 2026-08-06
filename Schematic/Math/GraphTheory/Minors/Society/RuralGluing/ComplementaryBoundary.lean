import Schematic.Math.GraphTheory.Minors.Society.RuralGluing.FreshCycleSum

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- Extract the complementary marked-face path from the right recursive disk
without constructing the two-sided cycle sum.  This is the input used when
the opposite boundary arc is empty and disk gluing reduces to inserting the
single endpoint chord. -/
theorem DiskRuralCertificate.exists_rightComplementaryPath
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (hrightArc : P.rightBoundaryArc.Nonempty) :
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    let A := R.boundaryAugmentedGraphOfLength
      (C.n + 3) C.boundary_length
    let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
    Exists fun b : A.Walk P.s P.t =>
      Exists fun _hb : b.IsPath =>
        b.darts =
          d.darts.drop (P.path.reverse.length + 1) ++ d.darts.take 1 := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A := R.boundaryAugmentedGraphOfLength
    (C.n + 3) C.boundary_length
  let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
  letI : DecidableRel A.Adj := Classical.decRel _
  letI : DecidableRel
      (FourColor.RotationSystemFan.addNodeGraph A
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
    ⟨b, hb, hbDarts, _hbOriented⟩
  exact ⟨b, hb, by simpa [hpLength] using hbDarts⟩

/-- The complementary path extracted from the left marked side face traverses
exactly the original left boundary arc, from `P.t` back to `P.s`. -/
theorem DiskRuralCertificate.leftComplementaryPath_support
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (a : (boundaryAugmentedGraphOfLength
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
          (C.n + 3) C.boundary_length).Walk P.t P.s)
    (haDarts :
      let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
      let c := L.boundaryCycleWalkOfLength C.n C.boundary_length
      a.darts = c.darts.drop (P.path.length + 1) ++ c.darts.take 1) :
    a.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s] := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let c := L.boundaryCycleWalkOfLength C.n C.boundary_length
  have hcTail : c.support.tail =
      P.path.support ++ P.leftBoundaryArcList.reverse := by
    rw [show c.support =
        (L.boundary.cycleWalkOfLength C.n C.boundary_length).support by
      exact L.boundaryCycleWalkOfLength_support C.n C.boundary_length]
    rw [L.boundary.cycleWalkOfLength_support C.n C.boundary_length]
    simp only [List.tail_cons]
    simp [L, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross,
      GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical,
      GMIX24CutPath.leftOrderedCutBoundary,
      GMIX24CutPath.leftOrderedCutBoundaryVertices]
  rw [← a.cons_map_snd_darts]
  rw [show a.darts = c.darts.drop (P.path.length + 1) ++
      c.darts.take 1 by simpa [L, c] using haDarts]
  simp only [List.map_append, List.map_drop, List.map_take]
  rw [c.map_snd_darts, hcTail]
  have htake :
      (P.path.support ++ P.leftBoundaryArcList.reverse).take 1 = [P.s] := by
    rw [List.take_append_of_le_length (by
      simp)]
    rw [List.take_one]
    have hhead : P.path.support.head? = some P.s := by
      have h := congrArg some P.path.head_support
      simp [List.head?_eq_some_head] at h ⊢
    simp [hhead]
  simp [SimpleGraph.Walk.length_support, htake]

/-- The complementary path extracted from the right marked side face traverses
exactly the original right boundary arc, from `P.s` back to `P.t`. -/
theorem DiskRuralCertificate.rightComplementaryPath_support
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (b : (boundaryAugmentedGraphOfLength
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
          (C.n + 3) C.boundary_length).Walk P.s P.t)
    (hbDarts :
      let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
      let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
      b.darts =
        d.darts.drop (P.path.reverse.length + 1) ++ d.darts.take 1) :
    b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t] := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
  have hdTail : d.support.tail =
      P.path.reverse.support ++ P.rightBoundaryArcList.reverse := by
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
  rw [← b.cons_map_snd_darts]
  rw [show b.darts = d.darts.drop (P.path.reverse.length + 1) ++
      d.darts.take 1 by simpa [R, d] using hbDarts]
  simp only [List.map_append, List.map_drop, List.map_take]
  rw [d.map_snd_darts, hdTail]
  have htake :
      (P.path.support.reverse ++ P.rightBoundaryArcList.reverse).take 1 =
        [P.t] := by
    rw [← P.path.support_reverse]
    rw [List.take_append_of_le_length (by
      simp)]
    rw [List.take_one]
    have hlast : P.path.support.getLast? = some P.t := by
      have h := congrArg some P.path.getLast_support
      simp [List.getLast?_eq_some_getLast] at h ⊢
    simp [hlast]
  simp [SimpleGraph.Walk.length_support, htake]

/-- The two complementary side-face paths, after inclusion into the union of
the side augmentations, traverse the counterclockwise ambient boundary based
at `P.t`. -/
theorem GMIX24CutPath.complementaryAppend_support
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {G K : SimpleGraph V}
    (a : G.Walk P.t P.s) (b : K.Walk P.s P.t)
    (haSupport :
      a.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s])
    (hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t]) :
    ((a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
      (b.mapLe (show K ≤ G ⊔ K from le_sup_right))).support =
        P.t :: P.leftBoundaryArcList.reverse ++
          P.s :: P.rightBoundaryArcList.reverse ++ [P.t] := by
  rw [SimpleGraph.Walk.support_append]
  simp [SimpleGraph.Walk.support_mapLe_eq_support, haSupport, hbSupport,
    List.append_assoc]

/-- If the ambient boundary has a vertex other than the two cut endpoints,
the two complementary side-face paths form a simple cycle.  Their only common
vertices are the cut endpoints, because the two open arcs of a cyclic boundary
are disjoint.  This includes either degenerate case in which exactly one open
arc is empty and its complementary path is the single endpoint edge. -/
theorem GMIX24CutPath.complementaryAppend_isCycle_of_arc_nonempty
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {G K : SimpleGraph V}
    (a : G.Walk P.t P.s)
    (b : K.Walk P.s P.t)
    (haSupport :
      a.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s])
    (hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t])
    (harc : P.leftBoundaryArc.Nonempty ∨ P.rightBoundaryArc.Nonempty) :
    ((a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
      (b.mapLe (show K ≤ G ⊔ K from le_sup_right))).IsCycle := by
  classical
  let c : (G ⊔ K).Walk P.t P.t :=
    (a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
      (b.mapLe (show K ≤ G ⊔ K from le_sup_right))
  have hcSupport :
      c.support =
        P.t :: P.leftBoundaryArcList.reverse ++
          P.s :: P.rightBoundaryArcList.reverse ++ [P.t] := by
    exact P.complementaryAppend_support a b haSupport hbSupport
  have hrightEndNodup :
      (P.rightBoundaryArcList.reverse ++ [P.t]).Nodup := by
    exact (List.nodup_reverse.mpr P.rightBoundaryArcList_nodup).append
      (by simp) (by
        intro z hz hzt
        simp only [List.mem_singleton] at hzt
        subst z
        exact P.end_not_mem_rightBoundaryArcList
          (List.mem_reverse.mp hz))
  have hrightTailNodup :
      (P.s :: P.rightBoundaryArcList.reverse ++ [P.t]).Nodup := by
    simpa only [List.cons_append] using
      (List.nodup_cons.mpr ⟨(by
        simp only [List.mem_append, List.mem_reverse, List.mem_singleton,
          not_or]
        exact ⟨P.start_not_mem_rightBoundaryArcList, P.s_ne_t⟩),
        hrightEndNodup⟩)
  have hdisjoint :
      P.leftBoundaryArcList.reverse.Disjoint
        (P.s :: P.rightBoundaryArcList.reverse ++ [P.t]) := by
    intro z hzLeft hzRight
    have hzLeftArc : z ∈ P.leftBoundaryArc := by
      apply P.mem_leftBoundaryArcList.mp
      exact List.mem_reverse.mp hzLeft
    rcases List.mem_cons.mp hzRight with hzs | hzRest
    · exact P.leftBoundaryArc_ne_s hzLeftArc hzs
    · rcases List.mem_append.mp hzRest with hzRightArc | hzt
      · exact Set.disjoint_left.mp P.leftBoundaryArc_disjoint_right
          hzLeftArc
          (P.mem_rightBoundaryArcList.mp (List.mem_reverse.mp hzRightArc))
      · simp only [List.mem_singleton] at hzt
        exact P.leftBoundaryArc_ne_t hzLeftArc hzt
  have htailNodup :
      (P.leftBoundaryArcList.reverse ++
        P.s :: P.rightBoundaryArcList.reverse ++ [P.t]).Nodup := by
    simpa only [List.cons_append, List.append_assoc] using
      (List.nodup_reverse.mpr P.leftBoundaryArcList_nodup).append
        hrightTailNodup hdisjoint
  have hcNotNil : ¬ c.Nil := by
    intro hcNil
    have hsMem : P.s ∈ c.support := by
      rw [hcSupport]
      simp
    have hsupportNil := SimpleGraph.Walk.nil_iff_support_eq.mp hcNil
    rw [hsupportNil] at hsMem
    exact P.s_ne_t (by simpa using hsMem)
  have hcTailSupport :
      c.tail.support =
        P.leftBoundaryArcList.reverse ++
          P.s :: P.rightBoundaryArcList.reverse ++ [P.t] := by
    rw [c.support_tail_of_not_nil hcNotNil, hcSupport]
    simp only [List.cons_append, List.tail_cons, List.append_assoc]
  have harcList :
      P.leftBoundaryArcList ≠ [] ∨ P.rightBoundaryArcList ≠ [] := by
    rcases harc with hleftArc | hrightArc
    · left
      obtain ⟨z, hz⟩ := hleftArc
      exact List.ne_nil_of_mem (P.mem_leftBoundaryArcList.mpr hz)
    · right
      obtain ⟨z, hz⟩ := hrightArc
      exact List.ne_nil_of_mem (P.mem_rightBoundaryArcList.mpr hz)
  have hcLengthThree : 3 ≤ c.length := by
    have hsupportLength := congrArg List.length hcSupport
    rw [SimpleGraph.Walk.length_support] at hsupportLength
    simp only [List.length_cons, List.length_append, List.length_reverse]
      at hsupportLength
    rcases harcList with hleftListNe | hrightListNe
    · have hleftPos : 0 < P.leftBoundaryArcList.length :=
        List.length_pos_iff_ne_nil.mpr hleftListNe
      omega
    · have hrightPos : 0 < P.rightBoundaryArcList.length :=
        List.length_pos_iff_ne_nil.mpr hrightListNe
      omega
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, hcLengthThree⟩
  rw [SimpleGraph.Walk.isPath_def, hcTailSupport]
  exact htailNodup

/-- The complementary side-face paths traverse the canonical ambient boundary
cycle in the same directed cyclic order.  The two walks use different
basepoints, so the comparison is made on their tails. -/
theorem GMIX24CutPath.complementaryAppend_tail_isRotated_boundaryCycle
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {G K : SimpleGraph V}
    (a : G.Walk P.t P.s)
    (b : K.Walk P.s P.t)
    (haSupport :
      a.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s])
    (hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t])
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    let c :=
      (a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
        (b.mapLe (show K ≤ G ⊔ K from le_sup_right))
    let w := S.boundaryCycleWalkOfLength n hlength
    c.support.tail ~r w.support.tail := by
  classical
  let c : (G ⊔ K).Walk P.t P.t :=
    (a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
      (b.mapLe (show K ≤ G ⊔ K from le_sup_right))
  let w := S.boundaryCycleWalkOfLength n hlength
  have hcSupport :
      c.support =
        P.t :: P.leftBoundaryArcList.reverse ++
          P.s :: P.rightBoundaryArcList.reverse ++ [P.t] := by
    exact P.complementaryAppend_support a b haSupport hbSupport
  have hcTail :
      c.support.tail =
        P.leftBoundaryArcList.reverse ++
          P.s :: P.rightBoundaryArcList.reverse ++ [P.t] := by
    rw [hcSupport]
    simp only [List.cons_append, List.tail_cons, List.append_assoc]
  have hwTail : w.support.tail = S.boundary.vertices.reverse := by
    rw [show w.support =
        (S.boundary.cycleWalkOfLength n hlength).support by
      exact S.boundaryCycleWalkOfLength_support n hlength]
    rw [S.boundary.cycleWalkOfLength_support n hlength]
    simp only [List.tail_cons]
  have hboundaryRotated :
      S.boundary.vertices ~r
        (P.s :: P.leftBoundaryArcList ++
          P.t :: P.rightBoundaryArcList) :=
    ⟨S.boundary.indexOf P.s, P.boundary_rotate_start_eq_arcs⟩
  have hreverse :
      S.boundary.vertices.reverse ~r
        (P.rightBoundaryArcList.reverse ++ [P.t]) ++
          (P.leftBoundaryArcList.reverse ++ [P.s]) := by
    simpa [List.reverse_append, List.append_assoc] using
      hboundaryRotated.reverse
  have hswap :
      (P.rightBoundaryArcList.reverse ++ [P.t]) ++
          (P.leftBoundaryArcList.reverse ++ [P.s]) ~r
        P.leftBoundaryArcList.reverse ++
          P.s :: P.rightBoundaryArcList.reverse ++ [P.t] := by
    simpa [List.append_assoc] using
      (List.isRotated_append
        (l := P.rightBoundaryArcList.reverse ++ [P.t])
        (l' := P.leftBoundaryArcList.reverse ++ [P.s]))
  have htailRotated : c.support.tail ~r w.support.tail := by
    rw [hcTail, hwTail]
    exact (hreverse.trans hswap).symm
  exact htailRotated

/-- The simple cycle formed by the two complementary side-face paths spans
exactly the ambient society boundary polygon.  The returned cycle is based at
`P.t`; the canonical boundary walk may use a different basepoint, so the
comparison is made through their cyclic tail-support orders. -/
theorem GMIX24CutPath.complementaryAppend_spans_boundaryCycle
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {G K : SimpleGraph V}
    (a : G.Walk P.t P.s)
    (b : K.Walk P.s P.t)
    (haSupport :
      a.support = P.t :: P.leftBoundaryArcList.reverse ++ [P.s])
    (hbSupport :
      b.support = P.s :: P.rightBoundaryArcList.reverse ++ [P.t])
    (hleftArc : P.leftBoundaryArc.Nonempty)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    let c :=
      (a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
        (b.mapLe (show K ≤ G ⊔ K from le_sup_right))
    c.toSubgraph.spanningCoe =
      S.boundary.cycleGraphOfLength (n + 3) hlength := by
  classical
  let c : (G ⊔ K).Walk P.t P.t :=
    (a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
      (b.mapLe (show K ≤ G ⊔ K from le_sup_right))
  let w := S.boundaryCycleWalkOfLength n hlength
  have hc : c.IsCycle :=
    P.complementaryAppend_isCycle_of_arc_nonempty
      a b haSupport hbSupport (Or.inl hleftArc)
  have hw : w.IsCycle :=
    S.boundaryCycleWalkOfLength_isCycle n hlength
  have htailRotated : c.support.tail ~r w.support.tail := by
    simpa [c, w] using
      P.complementaryAppend_tail_isRotated_boundaryCycle
        a b haSupport hbSupport n hlength
  calc
    c.toSubgraph.spanningCoe = w.toSubgraph.spanningCoe :=
      SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_isCycle_tail_isRotated
        c w hc hw htailRotated
    _ = S.boundary.cycleGraphOfLength (n + 3) hlength :=
      S.boundaryCycleWalkOfLength_toSubgraph_spanningCoe n hlength

private theorem boundaryCycle_eq_prefix_sup_complement
    {G Q : SimpleGraph V} {u v z : V}
    (c : G.Walk z z) (p : G.Walk u v) (a : G.Walk v u)
    (k : Nat)
    (hpDarts : p.darts = ((c.drop 1).take k).darts)
    (haDarts :
      a.darts = c.darts.drop (k + 1) ++ c.darts.take 1)
    (hproper : k + 1 < c.length)
    (hpSpan : p.toSubgraph.spanningCoe = Q) :
    c.toSubgraph.spanningCoe = Q ⊔ a.toSubgraph.spanningCoe := by
  classical
  have happendDarts :
      (p.append a).darts = c.darts.drop 1 ++ c.darts.take 1 := by
    rw [SimpleGraph.Walk.darts_append, hpDarts, haDarts]
    simp only [SimpleGraph.Walk.darts_take, SimpleGraph.Walk.darts_drop]
    rw [← List.append_assoc, List.drop_take_append_drop' c.darts 1 k]
  have hone : 1 ≤ c.darts.length := by
    rw [SimpleGraph.Walk.length_darts]
    exact (Nat.succ_le_succ (Nat.zero_le k)).trans hproper.le
  have happendRotate : (p.append a).darts = c.darts.rotate 1 := by
    rw [happendDarts, List.rotate_eq_drop_append_take hone]
  have hedgesRotated : (p.append a).edges ~r c.edges := by
    rw [SimpleGraph.Walk.edges, SimpleGraph.Walk.edges, happendRotate,
      List.map_rotate]
    exact (show c.edges ~r c.edges.rotate 1 from ⟨1, rfl⟩).symm
  have hspan :
      (p.append a).toSubgraph.spanningCoe = c.toSubgraph.spanningCoe :=
    SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_edges_isRotated
      (p.append a) c hedgesRotated
  calc
    c.toSubgraph.spanningCoe = (p.append a).toSubgraph.spanningCoe :=
      hspan.symm
    _ = p.toSubgraph.spanningCoe ⊔ a.toSubgraph.spanningCoe := by
      ext x y
      simp [SimpleGraph.Walk.toSubgraph_append,
        SimpleGraph.Subgraph.spanningCoe_adj]
    _ = Q ⊔ a.toSubgraph.spanningCoe := by rw [hpSpan]

/-- The left side boundary polygon is exactly the union of the common cut
path and the complementary original-boundary path extracted from its marked
face. -/
theorem DiskRuralCertificate.leftBoundaryCycle_eq_path_sup_complement
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (hleftArc : P.leftBoundaryArc.Nonempty)
    (a : (boundaryAugmentedGraphOfLength
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
          (C.n + 3) C.boundary_length).Walk P.t P.s)
    (haDarts :
      let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
      let c := L.boundaryCycleWalkOfLength C.n C.boundary_length
      a.darts = c.darts.drop (P.path.length + 1) ++ c.darts.take 1) :
    let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
    L.boundary.cycleGraphOfLength (C.n + 3) C.boundary_length =
      P.pathEdgeGraph ⊔ a.toSubgraph.spanningCoe := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let A := L.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
  let c := L.boundaryCycleWalkOfLength C.n C.boundary_length
  rcases C.exists_leftCutPathSegment P hno_cross hleftArc with
    ⟨p, _hp, hpSupport, hpDarts, hproper⟩
  have hpDarts' :
      p.darts = ((c.drop 1).take P.path.length).darts := by
    simpa [L, c] using hpDarts
  have haDarts' :
      a.darts = c.darts.drop (P.path.length + 1) ++ c.darts.take 1 := by
    simpa [L, c] using haDarts
  have hpSpan : p.toSubgraph.spanningCoe = P.pathEdgeGraph := by
    calc
      p.toSubgraph.spanningCoe = P.path.toSubgraph.spanningCoe :=
        SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_support_eq
          p P.path hpSupport
      _ = P.pathEdgeGraph := P.path_toSubgraph_spanningCoe_eq_pathEdgeGraph
  calc
    L.boundary.cycleGraphOfLength (C.n + 3) C.boundary_length =
        c.toSubgraph.spanningCoe :=
      (L.boundaryCycleWalkOfLength_toSubgraph_spanningCoe
        C.n C.boundary_length).symm
    _ = P.pathEdgeGraph ⊔ a.toSubgraph.spanningCoe :=
      boundaryCycle_eq_prefix_sup_complement
        c p a P.path.length hpDarts' haDarts' hproper hpSpan

/-- Right-side counterpart of
`leftBoundaryCycle_eq_path_sup_complement`. -/
theorem DiskRuralCertificate.rightBoundaryCycle_eq_path_sup_complement
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
    (hbDarts :
      let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
      let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
      b.darts =
        d.darts.drop (P.path.reverse.length + 1) ++ d.darts.take 1) :
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    R.boundary.cycleGraphOfLength (C.n + 3) C.boundary_length =
      P.pathEdgeGraph ⊔ b.toSubgraph.spanningCoe := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A := R.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
  let d := R.boundaryCycleWalkOfLength C.n C.boundary_length
  rcases C.exists_rightCutPathSegment P hno_cross hrightArc with
    ⟨q, _hq, hqSupport, hqDarts, hproper⟩
  have hqDarts' :
      q.darts = ((d.drop 1).take P.path.reverse.length).darts := by
    simpa [R, d] using hqDarts
  have hbDarts' :
      b.darts = d.darts.drop (P.path.reverse.length + 1) ++
        d.darts.take 1 := by
    simpa [R, d] using hbDarts
  have hqSpan : q.toSubgraph.spanningCoe = P.pathEdgeGraph := by
    calc
      q.toSubgraph.spanningCoe = P.path.reverse.toSubgraph.spanningCoe :=
        SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_support_eq
          q P.path.reverse hqSupport
      _ = P.path.toSubgraph.spanningCoe := by
        rw [SimpleGraph.Walk.toSubgraph_reverse]
      _ = P.pathEdgeGraph := P.path_toSubgraph_spanningCoe_eq_pathEdgeGraph
  calc
    R.boundary.cycleGraphOfLength (C.n + 3) C.boundary_length =
        d.toSubgraph.spanningCoe :=
      (R.boundaryCycleWalkOfLength_toSubgraph_spanningCoe
        C.n C.boundary_length).symm
    _ = P.pathEdgeGraph ⊔ b.toSubgraph.spanningCoe :=
      boundaryCycle_eq_prefix_sup_complement
        d q b P.path.reverse.length hqDarts' hbDarts' hproper hqSpan

end GeneralSociety

end Schematic.Math.GraphTheory
