import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.CrossEndpointReplacements

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_cross_boundary_clean_tail_branch_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z : V}
    (hzX : z ∈ X.firstPath.support ∨ z ∈ X.secondPath.support)
    (hzLeft : z ∈ P.leftSide) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          x ∈ X.firstPath.support ∧
            a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ q.support ->
                        (w ∈ X.firstPath.support ∨
                          w ∈ X.secondPath.support) ->
                          w = x) ∨
      (Exists fun x : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk x a =>
            x ∈ X.secondPath.support ∧
              a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
                (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                    Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                      forall w : V,
                        w ∈ q.support ->
                          (w ∈ X.firstPath.support ∨
                            w ∈ X.secondPath.support) ->
                            w = x) := by
  classical
  obtain ⟨a, q, ha, hqPath, hqLeft, hqOutside, hqBoundaryClean⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside_boundary_clean
      hno_cross hzLeft
  let A : Set V := {w : V | w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support}
  have hzA : z ∈ A := by
    simpa [A] using hzX
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hzA
  let tail : S.graph.Walk x a := q.dropUntil x hxq
  have htail_boundary_clean :
      Walk.InternalVertices tail ∩ S.boundarySet = ∅ := by
    simpa [tail] using
      Walk.IsPath.dropUntil_internalVertices_disjoint_of_internalVertices_disjoint
        hqPath hxq S.boundarySet hqBoundaryClean
  have htail_side :
      forall w : V, w ∈ tail.support -> w ∈ P.leftSide := by
    intro w hw
    exact hqLeft w (htail_subset w (by simpa [tail] using hw))
  have htail_outside :
      forall w : V, w ∈ tail.support -> w ∈ P.outside := by
    intro w hw
    exact hqOutside w (htail_subset w (by simpa [tail] using hw))
  have htail_clean' :
      forall w : V,
        w ∈ tail.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x := by
    intro w hw hwA
    exact htail_clean w (by simpa [tail] using hw) (by simpa [A] using hwA)
  rcases hxA with hxFirst | hxSecond
  · exact Or.inl
      ⟨x, a, tail, hxFirst, ha, by simpa [tail] using htail_path,
        htail_side, htail_outside, htail_boundary_clean, htail_clean'⟩
  · exact Or.inr
      ⟨x, a, tail, hxSecond, ha, by simpa [tail] using htail_path,
        htail_side, htail_outside, htail_boundary_clean, htail_clean'⟩

theorem canonicalOfNoCross_right_cross_boundary_clean_tail_branch_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z : V}
    (hzX : z ∈ X.firstPath.support ∨ z ∈ X.secondPath.support)
    (hzRight : z ∈ P.rightSide) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          x ∈ X.firstPath.support ∧
            a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ q.support ->
                        (w ∈ X.firstPath.support ∨
                          w ∈ X.secondPath.support) ->
                          w = x) ∨
      (Exists fun x : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk x a =>
            x ∈ X.secondPath.support ∧
              a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
                (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                    Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                      forall w : V,
                        w ∈ q.support ->
                          (w ∈ X.firstPath.support ∨
                            w ∈ X.secondPath.support) ->
                            w = x) := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_boundary_clean_tail_branch_cases
      P.reverse hno_cross Xrev (by simpa [Xrev] using hzX)
        (by simpa using hzRight))

/-- Follow a clean path from the left side to the boundary and retain its last
contact with either of two distinguished vertex sets. -/
theorem exists_left_boundary_path_last_contact_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (contact : V -> Prop) (primary secondary : Set V) {z : V}
    (hzPrimary : z ∈ primary)
    (hprimary_contact : forall w : V, w ∈ primary -> contact w)
    (hcontact_cases : forall w : V, contact w -> w ∈ primary ∨ w ∈ secondary)
    (hzLeft : z ∈ P.leftSide) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ primary ∧ a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
            (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                  forall w : V, w ∈ tail.support -> contact w -> w = x) ∨
      (Exists fun y : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk z a =>
            Exists fun hyq : y ∈ q.support =>
              y ∈ secondary ∧ a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
                (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                    Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                      forall w : V, w ∈ (q.dropUntil y hyq).support ->
                        contact w -> w = y) := by
  classical
  obtain ⟨a, q, ha, hqPath, hqLeft, hqOutside, hqBoundaryClean⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside_boundary_clean
      hno_cross hzLeft
  let contacts : Set V := {w : V | contact w}
  have hzContacts : z ∈ contacts := hprimary_contact z hzPrimary
  obtain ⟨x, hxq, hxContacts, htailPath, htailClean, htailSubset,
      _htailCovers, _htailIndex⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath contacts hzContacts
  let tail : S.graph.Walk x a := q.dropUntil x hxq
  have htailBoundaryClean :
      Walk.InternalVertices tail ∩ S.boundarySet = ∅ := by
    simpa [tail] using
      Walk.IsPath.dropUntil_internalVertices_disjoint_of_internalVertices_disjoint
        hqPath hxq S.boundarySet hqBoundaryClean
  have htailSide :
      forall w : V, w ∈ tail.support -> w ∈ P.leftSide := by
    intro w hw
    exact hqLeft w (htailSubset w (by simpa [tail] using hw))
  have htailOutside :
      forall w : V, w ∈ tail.support -> w ∈ P.outside := by
    intro w hw
    exact hqOutside w (htailSubset w (by simpa [tail] using hw))
  have htailClean' : forall w : V, w ∈ tail.support -> contact w -> w = x := by
    intro w hw hwContact
    exact htailClean w (by simpa [tail] using hw)
      (by simpa [contacts] using hwContact)
  rcases hcontact_cases x (by simpa [contacts] using hxContacts) with
      hxPrimary | hxSecondary
  · exact Or.inl
      ⟨x, a, tail, hxPrimary, ha, by simpa [tail] using htailPath,
        htailSide, htailOutside, htailBoundaryClean, htailClean'⟩
  · exact Or.inr
      ⟨x, a, q, hxq, hxSecondary, ha, hqPath, hqLeft, hqOutside,
        hqBoundaryClean, by
          intro w hw hwContact
          exact htailClean w (by simpa [tail] using hw)
            (by simpa [contacts] using hwContact)⟩

theorem canonicalOfNoCross_left_cross_firstPath_boundary_path_last_contact_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z : V}
    (hzFirst : z ∈ X.firstPath.support)
    (hzLeft : z ∈ P.leftSide) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ X.firstPath.support ∧
            a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support ->
                        (w ∈ X.firstPath.support ∨
                          w ∈ X.secondPath.support) ->
                          w = x) ∨
      (Exists fun y : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk z a =>
            Exists fun hyq : y ∈ q.support =>
              y ∈ X.secondPath.support ∧
                a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                    (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                      Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                        forall w : V,
                          w ∈ (q.dropUntil y hyq).support ->
                            (w ∈ X.firstPath.support ∨
                              w ∈ X.secondPath.support) ->
                              w = y) := by
  exact exists_left_boundary_path_last_contact_cases P hno_cross
    (fun w => w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support)
    {w : V | w ∈ X.firstPath.support}
    {w : V | w ∈ X.secondPath.support} hzFirst
    (fun _ hw => Or.inl hw) (fun _ hw => hw) hzLeft

theorem canonicalOfNoCross_left_cross_secondPath_boundary_path_last_contact_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z : V}
    (hzSecond : z ∈ X.secondPath.support)
    (hzLeft : z ∈ P.leftSide) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ X.secondPath.support ∧
            a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support ->
                        (w ∈ X.firstPath.support ∨
                          w ∈ X.secondPath.support) ->
                          w = x) ∨
      (Exists fun y : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk z a =>
            Exists fun hyq : y ∈ q.support =>
              y ∈ X.firstPath.support ∧
                a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                    (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                      Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                        forall w : V,
                          w ∈ (q.dropUntil y hyq).support ->
                            (w ∈ X.firstPath.support ∨
                              w ∈ X.secondPath.support) ->
                              w = y) := by
  exact exists_left_boundary_path_last_contact_cases P hno_cross
    (fun w => w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support)
    {w : V | w ∈ X.secondPath.support}
    {w : V | w ∈ X.firstPath.support} hzSecond
    (fun _ hw => Or.inr hw)
    (fun _ hw => hw.elim Or.inr Or.inl) hzLeft

theorem canonicalOfNoCross_right_cross_firstPath_boundary_path_last_contact_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z : V}
    (hzFirst : z ∈ X.firstPath.support)
    (hzRight : z ∈ P.rightSide) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ X.firstPath.support ∧
            a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support ->
                        (w ∈ X.firstPath.support ∨
                          w ∈ X.secondPath.support) ->
                          w = x) ∨
      (Exists fun y : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk z a =>
            Exists fun hyq : y ∈ q.support =>
              y ∈ X.secondPath.support ∧
                a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                    (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                      Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                        forall w : V,
                          w ∈ (q.dropUntil y hyq).support ->
                            (w ∈ X.firstPath.support ∨
                              w ∈ X.secondPath.support) ->
                              w = y) := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_boundary_path_last_contact_cases
      P.reverse hno_cross Xrev (by simpa [Xrev] using hzFirst)
        (by simpa using hzRight))

theorem canonicalOfNoCross_right_cross_secondPath_boundary_path_last_contact_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z : V}
    (hzSecond : z ∈ X.secondPath.support)
    (hzRight : z ∈ P.rightSide) :
    (Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ X.secondPath.support ∧
            a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support ->
                        (w ∈ X.firstPath.support ∨
                          w ∈ X.secondPath.support) ->
                          w = x) ∨
      (Exists fun y : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk z a =>
            Exists fun hyq : y ∈ q.support =>
              y ∈ X.firstPath.support ∧
                a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                    (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                      Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                        forall w : V,
                          w ∈ (q.dropUntil y hyq).support ->
                            (w ∈ X.firstPath.support ∨
                              w ∈ X.secondPath.support) ->
                              w = y) := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_boundary_path_last_contact_cases
      P.reverse hno_cross Xrev (by simpa [Xrev] using hzSecond)
        (by simpa using hzRight))

/-- Transport a clean subpath supplied in the canonical left society back to
the original society graph. -/
theorem canonicalOfNoCross_left_clean_branch_path_between
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (startSet endSet : Set V) {z a y : V}
    (q : S.graph.Walk z a)
    (hbranch :
      forall qD :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Walk z a,
        y ∈ qD.support -> qD.IsPath ->
          Exists fun x : V =>
            Exists fun y' : V =>
              Exists fun rD :
                  (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Walk x y' =>
                x ∈ startSet ∧ y' ∈ endSet ∧ rD.IsPath ∧
                  (forall w : V, w ∈ rD.support -> w ∈ startSet -> w = x) ∧
                  (forall w : V, w ∈ rD.support -> w ∈ endSet -> w = y') ∧
                  forall w : V, w ∈ rD.support -> w ∈ qD.support)
    (hyq : y ∈ q.support)
    (hqPath : q.IsPath)
    (hqSide : forall w : V, w ∈ q.support -> w ∈ P.leftSide) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ startSet ∧ y' ∈ endSet ∧ r.IsPath ∧
            (forall w : V, w ∈ r.support -> w ∈ startSet -> w = x) ∧
            (forall w : V, w ∈ r.support -> w ∈ endSet -> w = y') ∧
            forall w : V, w ∈ r.support -> w ∈ q.support := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let hp : forall e : Sym2 V, e ∈ q.edges -> e ∈ P.leftGraph.edgeSet :=
    P.leftSide_walk_edges_subset_leftGraph hno_cross q hqSide
  let qLeft : P.leftGraph.Walk z a := q.transfer P.leftGraph hp
  let qD : D.leftSociety.graph.Walk z a := by
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using qLeft
  have hyqD : y ∈ qD.support := by
    have hyqLeft : y ∈ qLeft.support := by
      simpa [qLeft, SimpleGraph.Walk.support_transfer] using hyq
    simpa [qD, qLeft, D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using hyqLeft
  have hqDPath : qD.IsPath := by
    have hqLeftPath : qLeft.IsPath :=
      SimpleGraph.Walk.IsPath.transfer hp hqPath
    simpa [qD, qLeft, D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using hqLeftPath
  obtain ⟨x, y', rD, hxStart, hyEnd, hrDPath,
      hcleanStart, hcleanEnd, hrDSubset⟩ := hbranch qD hyqD hqDPath
  let r : S.graph.Walk x y' := rD.mapLe D.leftSociety_graph_le
  refine ⟨x, y', r, hxStart, hyEnd,
    SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le hrDPath,
    ?_, ?_, ?_⟩
  · intro w hw hwStart
    exact hcleanStart w
      (by simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hw) hwStart
  · intro w hw hwEnd
    exact hcleanEnd w
      (by simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hw) hwEnd
  · intro w hw
    have hwqD : w ∈ qD.support :=
      hrDSubset w
        (by simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hw)
    have hwqLeft : w ∈ qLeft.support := by
      simpa [qD, qLeft, D, GMIX24Split.canonicalOfNoCross,
        GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
        GMIX24Split.ofCanonical] using hwqD
    simpa [qLeft, SimpleGraph.Walk.support_transfer] using hwqLeft

theorem canonicalOfNoCross_left_cross_clean_branch_path_first_to_second
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzFirst : z ∈ X.firstPath.support)
    (hyq : y ∈ q.support)
    (hySecond : y ∈ X.secondPath.support)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.firstPath.support ∧ y' ∈ X.secondPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y') ∧
              forall w : V, w ∈ r.support -> w ∈ q.support := by
  exact canonicalOfNoCross_left_clean_branch_path_between P hno_cross
    {w : V | w ∈ X.firstPath.support}
    {w : V | w ∈ X.secondPath.support} q
    (fun qD hyqD hqDPath =>
      X.exists_clean_branch_path_first_to_second qD hzFirst hyqD
        hySecond hqDPath)
    hyq hq_path hq_side

theorem canonicalOfNoCross_left_cross_clean_branch_path_second_to_first
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzSecond : z ∈ X.secondPath.support)
    (hyq : y ∈ q.support)
    (hyFirst : y ∈ X.firstPath.support)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.secondPath.support ∧ y' ∈ X.firstPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y') ∧
              forall w : V, w ∈ r.support -> w ∈ q.support := by
  exact canonicalOfNoCross_left_clean_branch_path_between P hno_cross
    {w : V | w ∈ X.secondPath.support}
    {w : V | w ∈ X.firstPath.support} q
    (fun qD hyqD hqDPath =>
      X.exists_clean_branch_path_second_to_first qD hzSecond hyqD
        hyFirst hqDPath)
    hyq hq_path hq_side

theorem canonicalOfNoCross_right_cross_clean_branch_path_first_to_second
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzFirst : z ∈ X.firstPath.support)
    (hyq : y ∈ q.support)
    (hySecond : y ∈ X.secondPath.support)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.firstPath.support ∧ y' ∈ X.secondPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y') ∧
              forall w : V, w ∈ r.support -> w ∈ q.support := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_clean_branch_path_first_to_second
      P.reverse hno_cross Xrev q (by simpa [Xrev] using hzFirst) hyq
        (by simpa [Xrev] using hySecond) hq_path
        (by
          intro w hw
          simpa using hq_side w hw))

theorem canonicalOfNoCross_right_cross_clean_branch_path_second_to_first
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzSecond : z ∈ X.secondPath.support)
    (hyq : y ∈ q.support)
    (hyFirst : y ∈ X.firstPath.support)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.secondPath.support ∧ y' ∈ X.firstPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y') ∧
              forall w : V, w ∈ r.support -> w ∈ q.support := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_clean_branch_path_second_to_first
      P.reverse hno_cross Xrev q (by simpa [Xrev] using hzSecond) hyq
        (by simpa [Xrev] using hyFirst) hq_path
        (by
          intro w hw
          simpa using hq_side w hw))

theorem canonicalOfNoCross_left_cross_clean_branch_path_first_to_second_inside
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzFirst : z ∈ X.firstPath.support)
    (hyq : y ∈ q.support)
    (hySecond : y ∈ X.secondPath.support)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.firstPath.support ∧ y' ∈ X.secondPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y') ∧
              (forall w : V, w ∈ r.support -> w ∈ q.support) ∧
                (forall w : V, w ∈ r.support -> w ∈ P.leftSide) ∧
                  forall w : V, w ∈ r.support -> w ∈ P.outside := by
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_clean_branch_path_first_to_second
        P hno_cross X q hzFirst hyq hySecond hq_path hq_side with
    ⟨x, y', r, hx, hy, hr_path, hclean_first, hclean_second,
      hr_subset⟩
  exact ⟨x, y', r, hx, hy, hr_path, hclean_first, hclean_second,
    hr_subset, (fun w hw => hq_side w (hr_subset w hw)),
    fun w hw => hq_outside w (hr_subset w hw)⟩

theorem canonicalOfNoCross_left_cross_clean_branch_path_second_to_first_inside
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzSecond : z ∈ X.secondPath.support)
    (hyq : y ∈ q.support)
    (hyFirst : y ∈ X.firstPath.support)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.secondPath.support ∧ y' ∈ X.firstPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y') ∧
              (forall w : V, w ∈ r.support -> w ∈ q.support) ∧
                (forall w : V, w ∈ r.support -> w ∈ P.leftSide) ∧
                  forall w : V, w ∈ r.support -> w ∈ P.outside := by
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_clean_branch_path_second_to_first
        P hno_cross X q hzSecond hyq hyFirst hq_path hq_side with
    ⟨x, y', r, hx, hy, hr_path, hclean_second, hclean_first,
      hr_subset⟩
  exact ⟨x, y', r, hx, hy, hr_path, hclean_second, hclean_first,
    hr_subset, (fun w hw => hq_side w (hr_subset w hw)),
    fun w hw => hq_outside w (hr_subset w hw)⟩

theorem canonicalOfNoCross_right_cross_clean_branch_path_first_to_second_inside
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzFirst : z ∈ X.firstPath.support)
    (hyq : y ∈ q.support)
    (hySecond : y ∈ X.secondPath.support)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.firstPath.support ∧ y' ∈ X.secondPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y') ∧
              (forall w : V, w ∈ r.support -> w ∈ q.support) ∧
                (forall w : V, w ∈ r.support -> w ∈ P.rightSide) ∧
                  forall w : V, w ∈ r.support -> w ∈ P.outside := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_clean_branch_path_first_to_second_inside
      P.reverse hno_cross Xrev q (by simpa [Xrev] using hzFirst) hyq
        (by simpa [Xrev] using hySecond) hq_path
        (by
          intro w hw
          simpa using hq_side w hw)
        (by
          intro w hw
          simpa using hq_outside w hw))

theorem canonicalOfNoCross_right_cross_clean_branch_path_second_to_first_inside
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z a y : V}
    (q : S.graph.Walk z a)
    (hzSecond : z ∈ X.secondPath.support)
    (hyq : y ∈ q.support)
    (hyFirst : y ∈ X.firstPath.support)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside) :
    Exists fun x : V =>
      Exists fun y' : V =>
        Exists fun r : S.graph.Walk x y' =>
          x ∈ X.secondPath.support ∧ y' ∈ X.firstPath.support ∧
            r.IsPath ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ∧
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y') ∧
              (forall w : V, w ∈ r.support -> w ∈ q.support) ∧
                (forall w : V, w ∈ r.support -> w ∈ P.rightSide) ∧
                  forall w : V, w ∈ r.support -> w ∈ P.outside := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_clean_branch_path_second_to_first_inside
      P.reverse hno_cross Xrev q (by simpa [Xrev] using hzSecond) hyq
        (by simpa [Xrev] using hyFirst) hq_path
        (by
          intro w hw
          simpa using hq_side w hw)
        (by
          intro w hw
          simpa using hq_outside w hw))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
