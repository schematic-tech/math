import Schematic.Math.GraphTheory.Minors.Society.SplitTripods
import Schematic.Math.GraphTheory.Embedding.RotationSystemFan

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The marked boundary face of a left cut society contains the original cut
path as its first segment after the initial closing dart.  When the original
left boundary arc is nonempty, at least one further boundary dart remains,
so `RotationSystemFan.exists_addNodeGraph_facialPathSplit_after_first` applies
without a degenerate final-dart case. -/
theorem DiskRuralCertificate.exists_leftCutPathSegment
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (harc : P.leftBoundaryArc.Nonempty) :
    let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
    let A := L.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
    let c := L.boundaryCycleWalkOfLength C.n C.boundary_length
    let segment := (c.drop 1).take P.path.length
    Exists fun p : A.Walk P.s P.t =>
      p.IsPath ∧ p.support = P.path.support ∧
        p.darts = segment.darts ∧
          P.path.length + 1 < c.length := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let A := L.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
  let c := L.boundaryCycleWalkOfLength C.n C.boundary_length
  let segment := (c.drop 1).take P.path.length
  have hsegmentSupport : segment.support = P.path.support := by
    calc
      segment.support =
          ((((L.boundary.cycleWalkOfLength C.n C.boundary_length).drop 1).take
            P.path.length).support) := by
        exact L.boundaryCycleWalkOfLength_drop_take_support
          C.n C.boundary_length 1 P.path.length
      _ = P.path.support := by
        simpa [L, GMIX24Split.canonicalOfNoCross,
          GMIX24Split.ofCanonicalGraphsOfNoCross,
          GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical] using
          P.leftOrderedCutBoundary_cycle_segment_support
            C.n C.boundary_length
  have hsegmentPath : segment.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [hsegmentSupport]
    exact P.path_isPath.support_nodup
  have hcLength : c.length = L.boundary.length := by
    calc
      c.length =
          (L.boundary.cycleWalkOfLength C.n C.boundary_length).length :=
        L.boundaryCycleWalkOfLength_length C.n C.boundary_length
      _ = C.n + 3 := by
        change
          ((SimpleGraph.cycleGraph.cycle C.n).map
            (SimpleGraph.Embedding.map
              (L.boundary.embeddingOfLength (C.n + 3) C.boundary_length)
              (SimpleGraph.cycleGraph (C.n + 3))).toHom).length = C.n + 3
        rw [SimpleGraph.Walk.length_map,
          SimpleGraph.cycleGraph.length_cycle]
      _ = L.boundary.length := C.boundary_length.symm
  have hboundaryLength :
      L.boundary.length =
        P.leftBoundaryArcList.length + P.path.support.length := by
    simp [L, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross,
      GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical,
      GMIX24CutPath.leftOrderedCutBoundary,
      GMIX24CutPath.leftOrderedCutBoundaryVertices,
      CyclicBoundary.length]
  rcases harc with ⟨a, ha⟩
  have haList : a ∈ P.leftBoundaryArcList :=
    (GMIX24CutPath.mem_leftBoundaryArcList P).mpr ha
  have harcLength : 0 < P.leftBoundaryArcList.length :=
    List.length_pos_of_ne_nil (List.ne_nil_of_mem haList)
  have hk : P.path.length + 1 < c.length := by
    rw [hcLength, hboundaryLength, SimpleGraph.Walk.length_support]
    omega
  rcases SimpleGraph.Walk.exists_copy_of_support_eq
      (G := S.graph) (H := A) P.path segment hsegmentSupport with
    ⟨p, hpSupport, hpDarts, hpPath⟩
  exact ⟨p, hpPath.mpr hsegmentPath, hpSupport.trans hsegmentSupport,
    hpDarts, hk⟩

/-- Right-side version of `exists_leftCutPathSegment`.  The right marked
boundary traverses the common cut path from `P.t` back to `P.s`, so this
extracts the oppositely oriented path needed by cycle gluing. -/
theorem DiskRuralCertificate.exists_rightCutPathSegment
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (harc : P.rightBoundaryArc.Nonempty) :
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    let A := R.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
    let c := R.boundaryCycleWalkOfLength C.n C.boundary_length
    let segment := (c.drop 1).take P.path.reverse.length
    Exists fun p : A.Walk P.t P.s =>
      p.IsPath ∧ p.support = P.path.reverse.support ∧
        p.darts = segment.darts ∧
          P.path.reverse.length + 1 < c.length := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A := R.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
  let c := R.boundaryCycleWalkOfLength C.n C.boundary_length
  let segment := (c.drop 1).take P.path.reverse.length
  have hsegmentSupport : segment.support = P.path.reverse.support := by
    calc
      segment.support =
          ((((R.boundary.cycleWalkOfLength C.n C.boundary_length).drop 1).take
            P.path.reverse.length).support) := by
        exact R.boundaryCycleWalkOfLength_drop_take_support
          C.n C.boundary_length 1 P.path.reverse.length
      _ = P.path.reverse.support := by
        simpa [R, GMIX24Split.canonicalOfNoCross,
          GMIX24Split.ofCanonicalGraphsOfNoCross,
          GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical] using
          P.rightOrderedCutBoundary_cycle_segment_support
            C.n C.boundary_length
  have hsegmentPath : segment.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [hsegmentSupport]
    exact P.path_isPath.reverse.support_nodup
  have hcLength : c.length = R.boundary.length := by
    calc
      c.length =
          (R.boundary.cycleWalkOfLength C.n C.boundary_length).length :=
        R.boundaryCycleWalkOfLength_length C.n C.boundary_length
      _ = C.n + 3 := by
        change
          ((SimpleGraph.cycleGraph.cycle C.n).map
            (SimpleGraph.Embedding.map
              (R.boundary.embeddingOfLength (C.n + 3) C.boundary_length)
              (SimpleGraph.cycleGraph (C.n + 3))).toHom).length = C.n + 3
        rw [SimpleGraph.Walk.length_map,
          SimpleGraph.cycleGraph.length_cycle]
      _ = R.boundary.length := C.boundary_length.symm
  have hboundaryLength :
      R.boundary.length =
        P.rightBoundaryArcList.length + P.path.reverse.support.length := by
    simp [R, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross,
      GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical,
      GMIX24CutPath.rightOrderedCutBoundary,
      GMIX24CutPath.rightOrderedCutBoundaryVertices,
      CyclicBoundary.length, SimpleGraph.Walk.support_reverse]
  rcases harc with ⟨a, ha⟩
  have haList : a ∈ P.rightBoundaryArcList :=
    (GMIX24CutPath.mem_rightBoundaryArcList P).mpr ha
  have harcLength : 0 < P.rightBoundaryArcList.length :=
    List.length_pos_of_ne_nil (List.ne_nil_of_mem haList)
  have hk : P.path.reverse.length + 1 < c.length := by
    rw [hcLength, hboundaryLength, SimpleGraph.Walk.length_support]
    omega
  rcases SimpleGraph.Walk.exists_copy_of_support_eq
      (G := S.graph) (H := A) P.path.reverse segment hsegmentSupport with
    ⟨p, hpSupport, hpDarts, hpPath⟩
  exact ⟨p, hpPath.mpr hsegmentPath, hpSupport.trans hsegmentSupport,
    hpDarts, hk⟩

/-- Split the marked face of the left side certificate along the canonical
cut path, retaining both the selected fresh-node face and the complementary
outer face. -/
theorem DiskRuralCertificate.exists_leftCutFaceSplit
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
    (harc : P.leftBoundaryArc.Nonempty) :
    let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
    let A := L.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
    let c := L.boundaryCycleWalkOfLength C.n C.boundary_length
    Exists fun p : A.Walk P.s P.t =>
      Exists fun hp : p.IsPath =>
        p.support = P.path.support ∧
          P.path.length + 1 < c.length ∧
          letI : DecidableRel A.Adj := Classical.decRel _
          letI : DecidableRel
              (FourColor.RotationSystemFan.addNodeGraph A
                (insert P.t ({P.s} : Set V))).Adj := Classical.decRel _
          Nonempty
            (FourColor.RotationSystemFan.FacialPathSplitData
              C.rotation c p hp P.s_ne_t) := by
  classical
  let L := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety
  let A := L.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
  let c := L.boundaryCycleWalkOfLength C.n C.boundary_length
  rcases C.exists_leftCutPathSegment P hno_cross harc with
    ⟨p, hp, hsupport, hdarts, hk⟩
  letI : DecidableRel A.Adj := Classical.decRel _
  letI : DecidableRel
      (FourColor.RotationSystemFan.addNodeGraph A
        (insert P.t ({P.s} : Set V))).Adj := Classical.decRel _
  refine ⟨p, hp, hsupport, hk, ?_⟩
  exact
    FourColor.RotationSystemFan.exists_addNodeGraph_facialPathSplitData_after_first
        C.rotation C.dual_eulerPlanar c
        (L.boundaryCycleWalkOfLength_isCycle C.n C.boundary_length)
        C.boundary_facial p hp P.s_ne_t P.path.length hk hdarts

/-- Right-side counterpart of `exists_leftCutFaceSplit`; its selected path
runs from `P.t` to `P.s`, hence its fresh-node cycle has the orientation
opposite to the left selected cycle. -/
theorem DiskRuralCertificate.exists_rightCutFaceSplit
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (C : DiskRuralCertificate
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety)
    (harc : P.rightBoundaryArc.Nonempty) :
    let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
    let A := R.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
    let c := R.boundaryCycleWalkOfLength C.n C.boundary_length
    Exists fun p : A.Walk P.t P.s =>
      Exists fun hp : p.IsPath =>
        p.support = P.path.reverse.support ∧
          P.path.reverse.length + 1 < c.length ∧
          letI : DecidableRel A.Adj := Classical.decRel _
          letI : DecidableRel
              (FourColor.RotationSystemFan.addNodeGraph A
                (insert P.s ({P.t} : Set V))).Adj := Classical.decRel _
          Nonempty
            (FourColor.RotationSystemFan.FacialPathSplitData
              C.rotation c p hp P.s_ne_t.symm) := by
  classical
  let R := (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety
  let A := R.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
  let c := R.boundaryCycleWalkOfLength C.n C.boundary_length
  rcases C.exists_rightCutPathSegment P hno_cross harc with
    ⟨p, hp, hsupport, hdarts, hk⟩
  letI : DecidableRel A.Adj := Classical.decRel _
  letI : DecidableRel
      (FourColor.RotationSystemFan.addNodeGraph A
        (insert P.s ({P.t} : Set V))).Adj := Classical.decRel _
  refine ⟨p, hp, hsupport, hk, ?_⟩
  exact
    FourColor.RotationSystemFan.exists_addNodeGraph_facialPathSplitData_after_first
        C.rotation C.dual_eulerPlanar c
        (R.boundaryCycleWalkOfLength_isCycle C.n C.boundary_length)
        C.boundary_facial p hp P.s_ne_t.symm P.path.reverse.length hk hdarts

end GeneralSociety

end Schematic.Math.GraphTheory
