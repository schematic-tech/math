import Schematic.Math.GraphTheory.Minors.Society.RuralGluing.CutFaceSplits
import Schematic.Math.GraphTheory.Embedding.RotationSystemPathGluing

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

theorem DiskRuralCertificate.leftAugmented_support_subset_side_or_path
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety) :
    let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
    let A := L.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
    A.support ⊆ P.leftSide ∪ P.pathSet := by
  let L : GeneralSociety V :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let A := L.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
  change A.support ⊆ P.leftSide ∪ P.pathSet
  intro (v : V) hv
  have hvActive : v ∈ L.activeSet := by
    have hv' : v ∈ L.graph.support ∪ L.boundarySet :=
      GeneralSociety.boundaryAugmentedGraphOfLength_support_subset
        L C.n C.boundary_length hv
    simpa [GeneralSociety.activeSet] using hv'
  exact
    GMIX24Split.canonicalOfNoCross_leftSociety_activeSet_subset_side_or_path
      P hno_cross hvActive

theorem DiskRuralCertificate.rightAugmented_support_subset_side_or_path
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety) :
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    let A := R.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
    A.support ⊆ P.rightSide ∪ P.pathSet := by
  let R : GeneralSociety V :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A := R.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
  change A.support ⊆ P.rightSide ∪ P.pathSet
  intro (v : V) hv
  have hvActive : v ∈ R.activeSet := by
    have hv' : v ∈ R.graph.support ∪ R.boundarySet :=
      GeneralSociety.boundaryAugmentedGraphOfLength_support_subset
        R C.n C.boundary_length hv
    simpa [GeneralSociety.activeSet] using hv'
  exact
    GMIX24Split.canonicalOfNoCross_rightSociety_activeSet_subset_side_or_path
      P hno_cross hvActive

/-- The two fresh-node augmented side graphs meet only on the selected
fresh-node closure of the cut path. -/
theorem DiskRuralCertificate.freshSide_support_inter_subset_selected
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C₁ : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (C₂ : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (p : (GeneralSociety.boundaryAugmentedGraphOfLength
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
        (C₁.n + 3) C₁.boundary_length).Walk P.s P.t)
    (hsupport : p.support = P.path.support) :
    forall ⦃v : Option V⦄,
      v ∈ (FourColor.RotationSystemFan.addNodeGraph
          (GeneralSociety.boundaryAugmentedGraphOfLength
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
              (C₁.n + 3) C₁.boundary_length)
          (insert P.t ({P.s} : Set V))).support ->
        v ∈ (FourColor.RotationSystemFan.addNodeGraph
            (GeneralSociety.boundaryAugmentedGraphOfLength
              (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
                (C₂.n + 3) C₂.boundary_length)
            (insert P.s ({P.t} : Set V))).support ->
          v ∈ (FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew p).support := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₁ := L.boundaryAugmentedGraphOfLength
    (C₁.n + 3) C₁.boundary_length
  let A₂ := R.boundaryAugmentedGraphOfLength
    (C₂.n + 3) C₂.boundary_length
  intro v hv₁ hv₂
  cases v with
  | none =>
      exact SimpleGraph.Walk.start_mem_support
        (FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew p)
  | some x =>
      have hxLeft : x ∈ P.leftSide ∪ P.pathSet := by
        rcases
            FourColor.RotationSystemFan.addNodeGraph_some_mem_support.mp hv₁ with
          hxA | hxEnd
        · exact C₁.leftAugmented_support_subset_side_or_path
            P hno_cross hxA
        · have hxEnd' : x = P.t ∨ x = P.s := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxEnd
          rcases hxEnd' with hxt | hxs
          · simpa [hxt] using Or.inr P.t_mem_pathSet
          · simpa [hxs] using Or.inr P.s_mem_pathSet
      have hxRight : x ∈ P.rightSide ∪ P.pathSet := by
        rcases
            FourColor.RotationSystemFan.addNodeGraph_some_mem_support.mp hv₂ with
          hxA | hxEnd
        · exact C₂.rightAugmented_support_subset_side_or_path
            P hno_cross hxA
        · have hxEnd' : x = P.s ∨ x = P.t := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxEnd
          rcases hxEnd' with hxs | hxt
          · simpa [hxs] using Or.inr P.s_mem_pathSet
          · simpa [hxt] using Or.inr P.t_mem_pathSet
      have hxPath : x ∈ P.pathSet := by
        rcases hxLeft with hxSide | hxPath
        · rcases hxRight with hxRightSide | hxPath
          · exact False.elim
              (Set.disjoint_left.mp
                (P.leftSide_disjoint_rightSide_of_no_cross hno_cross)
                hxSide hxRightSide)
          · exact hxPath
        · exact hxPath
      have hxp : x ∈ p.support := by
        rw [hsupport]
        simpa [GMIX24CutPath.pathSet] using hxPath
      rw [FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew_support]
      simp [hxp]

/-- Every edge shared by the two fresh-node side augmentations lies in the
selected closure of the cut path.  Nonempty outer arcs are encoded by the
strict-prefix inequality supplied by `exists_leftCutPathSegment`. -/
theorem DiskRuralCertificate.freshSide_common_adj_selected
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C₁ : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (C₂ : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (p : (GeneralSociety.boundaryAugmentedGraphOfLength
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
        (C₁.n + 3) C₁.boundary_length).Walk P.s P.t)
    (hsupport : p.support = P.path.support)
    (hproper : P.path.length + 1 <
      (GeneralSociety.boundaryCycleWalkOfLength
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
          C₁.n C₁.boundary_length).length) :
    forall ⦃x y : Option V⦄,
      (FourColor.RotationSystemFan.addNodeGraph
        (GeneralSociety.boundaryAugmentedGraphOfLength
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
            (C₁.n + 3) C₁.boundary_length)
        (insert P.t ({P.s} : Set V))).Adj x y ->
      (FourColor.RotationSystemFan.addNodeGraph
        (GeneralSociety.boundaryAugmentedGraphOfLength
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
            (C₂.n + 3) C₂.boundary_length)
        (insert P.s ({P.t} : Set V))).Adj x y ->
      (FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe.Adj
        x y := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₁ := L.boundaryAugmentedGraphOfLength
    (C₁.n + 3) C₁.boundary_length
  let A₂ := R.boundaryAugmentedGraphOfLength
    (C₂.n + 3) C₂.boundary_length
  let c := L.boundaryCycleWalkOfLength C₁.n C₁.boundary_length
  have hc : c.IsCycle :=
    L.boundaryCycleWalkOfLength_isCycle C₁.n C₁.boundary_length
  have hsegmentSupport :
      (((c.drop 1).take P.path.length).support) = P.path.support := by
    calc
      (((c.drop 1).take P.path.length).support) =
          ((((L.boundary.cycleWalkOfLength C₁.n C₁.boundary_length).drop 1).take
            P.path.length).support) :=
        L.boundaryCycleWalkOfLength_drop_take_support
          C₁.n C₁.boundary_length 1 P.path.length
      _ = P.path.support := by
        simpa [L, GMIX24Split.canonicalOfNoCross,
          GMIX24Split.ofCanonicalGraphsOfNoCross,
          GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical] using
          P.leftOrderedCutBoundary_cycle_segment_support
            C₁.n C₁.boundary_length
  have hpSegment :
      p.support = ((c.drop 1).take P.path.length).support :=
    hsupport.trans hsegmentSupport.symm
  intro x y h₁ h₂
  cases x with
  | none =>
      cases y with
      | none => exact False.elim ((FourColor.RotationSystemFan.addNodeGraph
          A₁ (insert P.t ({P.s} : Set V))).irrefl h₁)
      | some y =>
          apply
            (FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew_none_some_adj
              p).mpr
          simpa only [FourColor.RotationSystemFan.addNodeGraph_none_some,
            Set.mem_insert_iff, Set.mem_singleton_iff, or_comm] using h₁
  | some x =>
      cases y with
      | none =>
          apply
            (FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew_some_none_adj
              p).mpr
          simpa only [FourColor.RotationSystemFan.addNodeGraph_some_none,
            Set.mem_insert_iff, Set.mem_singleton_iff, or_comm] using h₁
      | some y =>
          have hxSelected :=
            DiskRuralCertificate.freshSide_support_inter_subset_selected
              P hno_cross C₁ C₂ p hsupport
                h₁.left_mem_support h₂.left_mem_support
          have hySelected :=
            DiskRuralCertificate.freshSide_support_inter_subset_selected
              P hno_cross C₁ C₂ p hsupport
                h₁.right_mem_support h₂.right_mem_support
          have hxP : x ∈ p.support := by
            simpa [FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew_support]
              using hxSelected
          have hyP : y ∈ p.support := by
            simpa [FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew_support]
              using hySelected
          have hxPath : x ∈ P.pathSet := by
            simpa [GMIX24CutPath.pathSet, hsupport] using hxP
          have hyPath : y ∈ P.pathSet := by
            simpa [GMIX24CutPath.pathSet, hsupport] using hyP
          have hA₁ : A₁.Adj x y := by
            simpa [FourColor.RotationSystemFan.addNodeGraph] using h₁
          change L.graph.Adj x y ∨
            (L.boundary.cycleGraphOfLength
              (C₁.n + 3) C₁.boundary_length).Adj x y at hA₁
          rcases hA₁ with hleft | hcycle
          · have hleft' : P.leftGraph.Adj x y := by
              simpa [L, GMIX24Split.canonicalOfNoCross,
                GMIX24Split.ofCanonicalGraphsOfNoCross,
                GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical]
                using hleft
            exact False.elim
              (P.leftGraph_not_adj_between_path_vertices
                hxPath hyPath hleft')
          · apply
              (FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew_some_some_adj
                p).mpr
            apply Walk.IsCycle.toSubgraph_adj_of_drop_one_take_copy
              hc hpSegment hproper hxP hyP
            rw [L.boundaryCycleWalkOfLength_toSubgraph_spanningCoe
              C₁.n C₁.boundary_length]
            exact hcycle

/-- Glue the two canonical disk certificates along the fresh-node closure of
the induced cut path.  Besides the Euler-planar sum, retain the two actual
complementary boundary paths and the proofs that their fresh-node closures are
faces of the sum.  This is the data needed to delete the fresh vertex and
identify the merged face with the ambient society boundary. -/
theorem DiskRuralCertificate.exists_canonicalFreshCycleSum
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
    (hrightArc : P.rightBoundaryArc.Nonempty) :
    let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    let A₁ := L.boundaryAugmentedGraphOfLength
      (C₁.n + 3) C₁.boundary_length
    let A₂ := R.boundaryAugmentedGraphOfLength
      (C₂.n + 3) C₂.boundary_length
    let c := L.boundaryCycleWalkOfLength C₁.n C₁.boundary_length
    let d := R.boundaryCycleWalkOfLength C₂.n C₂.boundary_length
    letI : DecidableRel
        (FourColor.RotationSystemFan.addNodeGraph A₁
          (insert P.t ({P.s} : Set V))).Adj := Classical.decRel _
    letI : DecidableRel
        (FourColor.RotationSystemFan.addNodeGraph A₂
          (insert P.s ({P.t} : Set V))).Adj := Classical.decRel _
    letI : DecidableRel
        (FourColor.RotationSystemFan.addNodeGraph A₁
            (insert P.t ({P.s} : Set V)) ⊔
          FourColor.RotationSystemFan.addNodeGraph A₂
            (insert P.s ({P.t} : Set V))).Adj := inferInstance
    Exists fun a : A₁.Walk P.t P.s =>
      Exists fun ha : a.IsPath =>
        a.darts = c.darts.drop (P.path.length + 1) ++ c.darts.take 1 ∧
          Exists fun b : A₂.Walk P.s P.t =>
            Exists fun hb : b.IsPath =>
              b.darts =
                  d.darts.drop (P.path.reverse.length + 1) ++ d.darts.take 1 ∧
                let left :=
                  ((a.darts.map
                      (FourColor.orientedEdgeDartEquiv (G := A₁)).symm).map
                    (FourColor.RotationSystemFan.addNodeGraphSomeOrientedEdge A₁
                      (insert P.t ({P.s} : Set V)))).map
                      (FourColor.RotationSystemGluing.liftOrientedEdge (show
                        FourColor.RotationSystemFan.addNodeGraph A₁
                            (insert P.t ({P.s} : Set V)) <=
                          FourColor.RotationSystemFan.addNodeGraph A₁
                              (insert P.t ({P.s} : Set V)) ⊔
                            FourColor.RotationSystemFan.addNodeGraph A₂
                              (insert P.s ({P.t} : Set V)) from le_sup_left))
                let right :=
                  ((b.darts.map
                      (FourColor.orientedEdgeDartEquiv (G := A₂)).symm).map
                    (FourColor.RotationSystemFan.addNodeGraphSomeOrientedEdge A₂
                      (insert P.s ({P.t} : Set V)))).map
                      (FourColor.RotationSystemGluing.liftOrientedEdge (show
                        FourColor.RotationSystemFan.addNodeGraph A₂
                            (insert P.s ({P.t} : Set V)) <=
                          FourColor.RotationSystemFan.addNodeGraph A₁
                              (insert P.t ({P.s} : Set V)) ⊔
                            FourColor.RotationSystemFan.addNodeGraph A₂
                              (insert P.s ({P.t} : Set V)) from le_sup_right))
                (left ++ right).Nodup ∧
                Exists fun U : FourColor.RotationSystem
                    (FourColor.RotationSystemFan.addNodeGraph A₁
                        (insert P.t ({P.s} : Set V)) ⊔
                      FourColor.RotationSystemFan.addNodeGraph A₂
                        (insert P.s ({P.t} : Set V))) =>
                  U.toHypermap.dual.EulerPlanar ∧
                    FourColor.RotationSystemGluing.IsFacialCycle U
                      ((FourColor.RotationSystemFan.addNodeGraphPathCycleAtNewIn
                          A₁ (insert P.t ({P.s} : Set V)) (by simp) (by simp)
                            a).mapLe le_sup_left)
                      ((FourColor.RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
                            (insert P.t ({P.s} : Set V)) (by simp) (by simp)
                              P.s_ne_t.symm a ha).mapLe le_sup_left) ∧
                    FourColor.RotationSystemGluing.IsFacialCycle U
                      ((FourColor.RotationSystemFan.addNodeGraphPathCycleAtNewIn
                          A₂ (insert P.s ({P.t} : Set V)) (by simp) (by simp)
                            b).mapLe le_sup_right)
                      ((FourColor.RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
                            (insert P.s ({P.t} : Set V)) (by simp) (by simp)
                              P.s_ne_t b hb).mapLe le_sup_right) := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A₁ := L.boundaryAugmentedGraphOfLength
    (C₁.n + 3) C₁.boundary_length
  let A₂ := R.boundaryAugmentedGraphOfLength
    (C₂.n + 3) C₂.boundary_length
  let c := L.boundaryCycleWalkOfLength C₁.n C₁.boundary_length
  let d := R.boundaryCycleWalkOfLength C₂.n C₂.boundary_length
  letI : DecidableRel A₁.Adj := Classical.decRel _
  letI : DecidableRel A₂.Adj := Classical.decRel _
  let H₁ := FourColor.RotationSystemFan.addNodeGraph A₁
    (insert P.t ({P.s} : Set V))
  let H₂ := FourColor.RotationSystemFan.addNodeGraph A₂
    (insert P.s ({P.t} : Set V))
  letI : DecidableRel H₁.Adj := Classical.decRel _
  letI : DecidableRel H₂.Adj := Classical.decRel _
  letI : DecidableRel (H₁ ⊔ H₂).Adj := inferInstance
  rcases C₁.exists_leftCutFaceSplit P hno_cross hleftArc with
    ⟨p, hp, hpSupport, hpProper, ⟨D₁⟩⟩
  rcases C₂.exists_rightCutFaceSplit P hno_cross hrightArc with
    ⟨q, hq, hqSupport, hqProper, ⟨D₂⟩⟩
  have hpLength : p.length = P.path.length := by
    have h := congrArg List.length hpSupport
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_support] at h
    omega
  have hqLength : q.length = P.path.reverse.length := by
    have h := congrArg List.length hqSupport
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_support] at h
    omega
  have hc : c.IsCycle :=
    L.boundaryCycleWalkOfLength_isCycle C₁.n C₁.boundary_length
  have hd : d.IsCycle :=
    R.boundaryCycleWalkOfLength_isCycle C₂.n C₂.boundary_length
  have hpSegment :
      p.support = ((c.drop 1).take p.length).support := by
    calc
      p.support = P.path.support := hpSupport
      _ = ((c.drop 1).take P.path.length).support := by
        symm
        calc
          ((c.drop 1).take P.path.length).support =
              (((L.boundary.cycleWalkOfLength C₁.n C₁.boundary_length).drop 1).take
                P.path.length).support :=
            L.boundaryCycleWalkOfLength_drop_take_support
              C₁.n C₁.boundary_length 1 P.path.length
          _ = P.path.support := by
            simpa [L, GMIX24Split.canonicalOfNoCross,
              GMIX24Split.ofCanonicalGraphsOfNoCross,
              GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical] using
              P.leftOrderedCutBoundary_cycle_segment_support
                C₁.n C₁.boundary_length
      _ = ((c.drop 1).take p.length).support := by rw [hpLength]
  have hqSegment :
      q.support = ((d.drop 1).take q.length).support := by
    calc
      q.support = P.path.reverse.support := hqSupport
      _ = ((d.drop 1).take P.path.reverse.length).support := by
        symm
        calc
          ((d.drop 1).take P.path.reverse.length).support =
              (((R.boundary.cycleWalkOfLength C₂.n C₂.boundary_length).drop 1).take
                P.path.reverse.length).support :=
            R.boundaryCycleWalkOfLength_drop_take_support
              C₂.n C₂.boundary_length 1 P.path.reverse.length
          _ = P.path.reverse.support := by
            simpa [R, GMIX24Split.canonicalOfNoCross,
              GMIX24Split.ofCanonicalGraphsOfNoCross,
              GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical] using
              P.rightOrderedCutBoundary_cycle_segment_support
                C₂.n C₂.boundary_length
      _ = ((d.drop 1).take q.length).support := by rw [hqLength]
  have hpProper' : p.length + 1 < c.length := by
    simpa [hpLength, c, L] using hpProper
  have hqProper' : q.length + 1 < d.length := by
    simpa [hqLength, d, R] using hqProper
  have hreverseSupport : q.support = p.reverse.support := by
    rw [hqSupport, SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_reverse, hpSupport]
  have hcommon : forall ⦃x y : Option V⦄,
      H₁.Adj x y -> H₂.Adj x y ->
        ((FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe).Adj
          x y := by
    exact C₁.freshSide_common_adj_selected
      P hno_cross C₂ p hpSupport hpProper
  have hmeet : forall ⦃v : Option V⦄,
      v ∈ H₁.support -> v ∈ H₂.support ->
        v ∈ (FourColor.RotationSystemFan.addNodeGraphPathCycleAtNew p).support := by
    exact C₁.freshSide_support_inter_subset_selected
      P hno_cross C₂ p hpSupport
  have hLthree : L.ThreeConnected := by
    simpa [L] using
      GMIX24Split.canonicalOfNoCross_left_three_connected
        P hno_cross hthree
  have hRthree : R.ThreeConnected := by
    simpa [R] using
      GMIX24Split.canonicalOfNoCross_right_three_connected
        P hno_cross hthree
  have hA₁Connected : (A₁.induce A₁.support).Preconnected := by
    simpa [A₁] using
      hLthree.boundaryAugmentedGraph_support_preconnected
        C₁.n C₁.boundary_length
  have hA₂Connected : (A₂.induce A₂.support).Preconnected := by
    simpa [A₂] using
      hRthree.boundaryAugmentedGraph_support_preconnected
        C₂.n C₂.boundary_length
  have hsL : P.s ∈ L.boundarySet := by
    rw [show L.boundarySet = P.leftCutBoundarySet by
      change
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet =
          P.leftCutBoundarySet
      exact GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
    exact Or.inr P.s_mem_pathSet
  have htL : P.t ∈ L.boundarySet := by
    rw [show L.boundarySet = P.leftCutBoundarySet by
      change
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet =
          P.leftCutBoundarySet
      exact GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
    exact Or.inr P.t_mem_pathSet
  have htR : P.t ∈ R.boundarySet := by
    rw [show R.boundarySet = P.rightCutBoundarySet by
      change
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet =
          P.rightCutBoundarySet
      exact GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet P hno_cross]
    exact Or.inr P.t_mem_pathSet
  have hsR : P.s ∈ R.boundarySet := by
    rw [show R.boundarySet = P.rightCutBoundarySet by
      change
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet =
          P.rightCutBoundarySet
      exact GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet P hno_cross]
    exact Or.inr P.s_mem_pathSet
  have hsA₁ : P.s ∈ A₁.support := by
    exact L.boundary_mem_boundaryAugmentedGraphOfLength_support
      C₁.n C₁.boundary_length hsL
  have htA₁ : P.t ∈ A₁.support := by
    exact L.boundary_mem_boundaryAugmentedGraphOfLength_support
      C₁.n C₁.boundary_length htL
  have htA₂ : P.t ∈ A₂.support := by
    exact R.boundary_mem_boundaryAugmentedGraphOfLength_support
      C₂.n C₂.boundary_length htR
  have hsA₂ : P.s ∈ A₂.support := by
    exact R.boundary_mem_boundaryAugmentedGraphOfLength_support
      C₂.n C₂.boundary_length hsR
  rcases
      FourColor.RotationSystemGluing.exists_cycleSum_preserving_complementary_faces
          D₁ D₂ hc hd hpSegment hpProper' hqSegment hqProper'
            hreverseSupport hcommon hmeet hA₁Connected hA₂Connected
              hsA₁ htA₁ htA₂ hsA₂ with
    ⟨a, ha, haDarts, _haOriented, b, hb, hbDarts, _hbOriented,
      hsectorsNodup, U, hU, haFacial, hbFacial⟩
  refine ⟨a, ha, ?_, b, hb, ?_, hsectorsNodup, U, hU, haFacial, hbFacial⟩
  · simpa [hpLength] using haDarts
  · simpa [hqLength] using hbDarts

end GeneralSociety

end Schematic.Math.GraphTheory
