import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.CrossTransport

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

/-- Right-side source-preserving version of
`canonicalOfNoCross_right_tripod_path_foot_side_to_boundary_path`. -/
theorem canonicalOfNoCross_right_tripod_path_foot_side_to_boundary_path_at
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3)
    (hi : T.boundary i ∈ P.pathSet) :
    Exists fun z : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk z a =>
          (z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ∧
            z ∈ P.rightSide ∧ a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                forall w : V, w ∈ q.support -> w ∈ P.outside := by
  obtain ⟨z, hzT, hzRight⟩ :=
    GMIX24Split.canonicalOfNoCross_right_tripod_boundary_path_meets_rightSide
      P hno_cross T i hi
  obtain ⟨a, q, ha, hqPath, hqRight, hqOutside⟩ :=
    P.exists_path_from_rightSide_to_rightBoundaryArc_inside hzRight
  exact ⟨z, a, q, hzT, hzRight, ha, hqPath, hqRight, hqOutside⟩

theorem canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath : Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          (Exists fun i : Fin 3 =>
            x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ∧
            a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                  forall w : V,
                    w ∈ q.support ->
                      (Exists fun i : Fin 3 =>
                        w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
                        w = x := by
  classical
  obtain ⟨z, a, q, hzT, _hzLeft, ha, hqPath, hqLeft, hqOutside⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_side_to_boundary_path
      P hno_cross T hpath
  let A : Set V := {w : V |
    Exists fun i : Fin 3 =>
      w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support}
  have hzA : z ∈ A := by
    simpa [A] using hzT
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hzA
  let tail : S.graph.Walk x a := q.dropUntil x hxq
  refine ⟨x, a, tail, ?_, ha, ?_, ?_, ?_, ?_⟩
  · simpa [A] using hxA
  · simpa [tail] using htail_path
  · intro w hw
    exact hqLeft w (htail_subset w (by simpa [tail] using hw))
  · intro w hw
    exact hqOutside w (htail_subset w (by simpa [tail] using hw))
  · intro w hw hwA
    exact htail_clean w (by simpa [tail] using hw) (by simpa [A] using hwA)

/-- Clean-tail extraction from a specified side-tripod foot.

The returned last contact is still the last contact with the whole side tripod;
the extra datum records that the original path into the side began on the
chosen branch.  This is the formal handle needed for the source argument that
if the last contact has moved to a different branch then the ambient society
already contains a forbidden tripod. -/
theorem canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3)
    (hi : T.boundary i ∈ P.pathSet) :
    Exists fun z0 : V =>
      Exists fun x : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk x a =>
            (z0 ∈ (T.rim i).support ∨ z0 ∈ (T.leg i).support) ∧
              z0 ∈ P.leftSide ∧
                (Exists fun r : Fin 3 =>
                  x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
                a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                    (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                      forall w : V,
                        w ∈ q.support ->
                          (Exists fun r : Fin 3 =>
                            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
                          w = x := by
  classical
  obtain ⟨z0, a, q0, hz0T, hz0Left, ha, hqPath, hqLeft, hqOutside⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_side_to_boundary_path_at
      P hno_cross T i hi
  let A : Set V := {w : V |
    Exists fun r : Fin 3 =>
      w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support}
  have hz0A : z0 ∈ A := by
    exact ⟨i, hz0T⟩
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hz0A
  let tail : S.graph.Walk x a := q0.dropUntil x hxq
  refine ⟨z0, x, a, tail, hz0T, hz0Left, ?_, ha, ?_, ?_, ?_, ?_⟩
  · simpa [A] using hxA
  · simpa [tail] using htail_path
  · intro w hw
    exact hqLeft w (htail_subset w (by simpa [tail] using hw))
  · intro w hw
    exact hqOutside w (htail_subset w (by simpa [tail] using hw))
  · intro w hw hwA
    exact htail_clean w (by simpa [tail] using hw) (by simpa [A] using hwA)

/-- Strong indexed clean-tail extraction retaining the original side path.

This is the data form needed for the literal GM IX `(2.4)` side-tripod
paragraph.  The point `z0` is the first contact produced from the chosen foot,
`q0` is the path from that contact to the boundary arc, and `q0.dropUntil x`
is the clean suffix starting at the final side-tripod contact. -/
theorem canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at_with_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3)
    (hi : T.boundary i ∈ P.pathSet) :
    Exists fun z0 : V =>
      Exists fun a : V =>
        Exists fun q0 : S.graph.Walk z0 a =>
          Exists fun x : V =>
            Exists fun hxq : x ∈ q0.support =>
              (z0 ∈ (T.rim i).support ∨ z0 ∈ (T.leg i).support) ∧
                z0 ∈ P.leftSide ∧
                  (Exists fun r : Fin 3 =>
                    x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
                  a ∈ P.leftBoundaryArc ∧ q0.IsPath ∧
                    (forall w : V, w ∈ q0.support -> w ∈ P.leftSide) ∧
                      (forall w : V, w ∈ q0.support -> w ∈ P.outside) ∧
                        (q0.dropUntil x hxq).IsPath ∧
                          (forall w : V,
                            w ∈ (q0.dropUntil x hxq).support ->
                              (Exists fun r : Fin 3 =>
                                w ∈ (T.rim r).support ∨
                                  w ∈ (T.leg r).support) ->
                              w = x) := by
  classical
  obtain ⟨z0, a, q0, hz0T, hz0Left, ha, hqPath, hqLeft, hqOutside⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_side_to_boundary_path_at
      P hno_cross T i hi
  let A : Set V := {w : V |
    Exists fun r : Fin 3 =>
      w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support}
  have hz0A : z0 ∈ A := by
    exact ⟨i, hz0T⟩
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, _htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hz0A
  refine ⟨z0, a, q0, x, hxq, hz0T, hz0Left, ?_, ha, hqPath,
    hqLeft, hqOutside, ?_, ?_⟩
  · simpa [A] using hxA
  · exact htail_path
  · intro w hw hwA
    exact htail_clean w hw (by simpa [A] using hwA)

/-- Strong indexed clean-tail extraction retaining both source pieces.

The source proof of GM IX `(2.4)` uses one auxiliary path `Q`: if the last
contact with the side tripod is not on the median branch, the prefix from the
chosen median foot to that last contact is the path used in the common-end
argument; the suffix from that last contact to the boundary arc is the clean
tail used in the direct median-branch constructor.  The earlier
`..._at_with_path` theorem kept the original path but forced every caller to
rebuild these prefix facts.  This package keeps the prefix explicitly and
records that it stays on the same side and outside the cut path. -/
theorem canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at_with_prefix
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3)
    (hi : T.boundary i ∈ P.pathSet) :
    Exists fun z0 : V =>
      Exists fun a : V =>
        Exists fun q0 : S.graph.Walk z0 a =>
          Exists fun x : V =>
            Exists fun hxq : x ∈ q0.support =>
              Exists fun pref : S.graph.Walk z0 x =>
                pref = q0.takeUntil x hxq ∧
                  (z0 ∈ (T.rim i).support ∨ z0 ∈ (T.leg i).support) ∧
                    z0 ∈ P.leftSide ∧
                      (Exists fun r : Fin 3 =>
                        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
                      a ∈ P.leftBoundaryArc ∧ q0.IsPath ∧ pref.IsPath ∧
                        (forall w : V, w ∈ pref.support -> w ∈ P.leftSide) ∧
                          (forall w : V, w ∈ pref.support -> w ∈ P.outside) ∧
                            (forall w : V, w ∈ q0.support -> w ∈ P.leftSide) ∧
                              (forall w : V, w ∈ q0.support -> w ∈ P.outside) ∧
                                (q0.dropUntil x hxq).IsPath ∧
                                  (forall w : V,
                                    w ∈ (q0.dropUntil x hxq).support ->
                                      (Exists fun r : Fin 3 =>
                                        w ∈ (T.rim r).support ∨
                                          w ∈ (T.leg r).support) ->
                                      w = x) := by
  classical
  obtain ⟨z0, a, q0, x, hxq, hz0T, hz0Left, hxT, ha, hqPath,
      hqLeft, hqOutside, htailPath, htailClean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at_with_path
      P hno_cross T i hi
  let pref : S.graph.Walk z0 x := q0.takeUntil x hxq
  refine ⟨z0, a, q0, x, hxq, pref, rfl, hz0T, hz0Left, hxT, ha,
    hqPath, ?_, ?_, ?_, hqLeft, hqOutside, htailPath, htailClean⟩
  · simpa [pref] using hqPath.takeUntil hxq
  · intro w hw
    exact hqLeft w
      (SimpleGraph.Walk.support_takeUntil_subset q0 hxq (by
        simpa [pref] using hw))
  · intro w hw
    exact hqOutside w
      (SimpleGraph.Walk.support_takeUntil_subset q0 hxq (by
        simpa [pref] using hw))

theorem canonicalOfNoCross_right_tripod_path_foot_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hpath : Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          (Exists fun i : Fin 3 =>
            x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ∧
            a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                  forall w : V,
                    w ∈ q.support ->
                      (Exists fun i : Fin 3 =>
                        w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
                        w = x := by
  classical
  obtain ⟨z, a, q, hzT, _hzRight, ha, hqPath, hqRight, hqOutside⟩ :=
    GMIX24Split.canonicalOfNoCross_right_tripod_path_foot_side_to_boundary_path
      P hno_cross T hpath
  let A : Set V := {w : V |
    Exists fun i : Fin 3 =>
      w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support}
  have hzA : z ∈ A := by
    simpa [A] using hzT
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hzA
  let tail : S.graph.Walk x a := q.dropUntil x hxq
  refine ⟨x, a, tail, ?_, ha, ?_, ?_, ?_, ?_⟩
  · simpa [A] using hxA
  · simpa [tail] using htail_path
  · intro w hw
    exact hqRight w (htail_subset w (by simpa [tail] using hw))
  · intro w hw
    exact hqOutside w (htail_subset w (by simpa [tail] using hw))
  · intro w hw hwA
    exact htail_clean w (by simpa [tail] using hw) (by simpa [A] using hwA)

/-- Right-side strong indexed clean-tail extraction retaining the original
side path. -/
theorem canonicalOfNoCross_right_tripod_path_foot_clean_tail_to_boundary_at_with_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3)
    (hi : T.boundary i ∈ P.pathSet) :
    Exists fun z0 : V =>
      Exists fun a : V =>
        Exists fun q0 : S.graph.Walk z0 a =>
          Exists fun x : V =>
            Exists fun hxq : x ∈ q0.support =>
              (z0 ∈ (T.rim i).support ∨ z0 ∈ (T.leg i).support) ∧
                z0 ∈ P.rightSide ∧
                  (Exists fun r : Fin 3 =>
                    x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
                  a ∈ P.rightBoundaryArc ∧ q0.IsPath ∧
                    (forall w : V, w ∈ q0.support -> w ∈ P.rightSide) ∧
                      (forall w : V, w ∈ q0.support -> w ∈ P.outside) ∧
                        (q0.dropUntil x hxq).IsPath ∧
                          (forall w : V,
                            w ∈ (q0.dropUntil x hxq).support ->
                              (Exists fun r : Fin 3 =>
                                w ∈ (T.rim r).support ∨
                                  w ∈ (T.leg r).support) ->
                              w = x) := by
  classical
  obtain ⟨z0, a, q0, hz0T, hz0Right, ha, hqPath, hqRight, hqOutside⟩ :=
    GMIX24Split.canonicalOfNoCross_right_tripod_path_foot_side_to_boundary_path_at
      P hno_cross T i hi
  let A : Set V := {w : V |
    Exists fun r : Fin 3 =>
      w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support}
  have hz0A : z0 ∈ A := by
    exact ⟨i, hz0T⟩
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, _htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hz0A
  refine ⟨z0, a, q0, x, hxq, hz0T, hz0Right, ?_, ha, hqPath,
    hqRight, hqOutside, ?_, ?_⟩
  · simpa [A] using hxA
  · exact htail_path
  · intro w hw hwA
    exact htail_clean w hw (by simpa [A] using hwA)

/-- Right-side companion to
`canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at_with_prefix`.

It retains the prefix of the original auxiliary path from the chosen side
tripod foot to the final side-tripod contact.  This is the symmetric data
needed when the GM IX `(2.4)` common-end side-tripod paragraph is applied to
the second canonical society. -/
theorem canonicalOfNoCross_right_tripod_path_foot_clean_tail_to_boundary_at_with_prefix
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3)
    (hi : T.boundary i ∈ P.pathSet) :
    Exists fun z0 : V =>
      Exists fun a : V =>
        Exists fun q0 : S.graph.Walk z0 a =>
          Exists fun x : V =>
            Exists fun hxq : x ∈ q0.support =>
              Exists fun pref : S.graph.Walk z0 x =>
                pref = q0.takeUntil x hxq ∧
                  (z0 ∈ (T.rim i).support ∨ z0 ∈ (T.leg i).support) ∧
                    z0 ∈ P.rightSide ∧
                      (Exists fun r : Fin 3 =>
                        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
                      a ∈ P.rightBoundaryArc ∧ q0.IsPath ∧ pref.IsPath ∧
                        (forall w : V, w ∈ pref.support -> w ∈ P.rightSide) ∧
                          (forall w : V, w ∈ pref.support -> w ∈ P.outside) ∧
                            (forall w : V, w ∈ q0.support -> w ∈ P.rightSide) ∧
                              (forall w : V, w ∈ q0.support -> w ∈ P.outside) ∧
                                (q0.dropUntil x hxq).IsPath ∧
                                  (forall w : V,
                                    w ∈ (q0.dropUntil x hxq).support ->
                                      (Exists fun r : Fin 3 =>
                                        w ∈ (T.rim r).support ∨
                                          w ∈ (T.leg r).support) ->
                                      w = x) := by
  classical
  obtain ⟨z0, a, q0, x, hxq, hz0T, hz0Right, hxT, ha, hqPath,
      hqRight, hqOutside, htailPath, htailClean⟩ :=
    GMIX24Split.canonicalOfNoCross_right_tripod_path_foot_clean_tail_to_boundary_at_with_path
      P hno_cross T i hi
  let pref : S.graph.Walk z0 x := q0.takeUntil x hxq
  refine ⟨z0, a, q0, x, hxq, pref, rfl, hz0T, hz0Right, hxT, ha,
    hqPath, ?_, ?_, ?_, hqRight, hqOutside, htailPath, htailClean⟩
  · simpa [pref] using hqPath.takeUntil hxq
  · intro w hw
    exact hqRight w
      (SimpleGraph.Walk.support_takeUntil_subset q0 hxq (by
        simpa [pref] using hw))
  · intro w hw
    exact hqOutside w
      (SimpleGraph.Walk.support_takeUntil_subset q0 hxq (by
        simpa [pref] using hw))

/-- Right-side clean-tail extraction from a specified side-tripod foot. -/
theorem canonicalOfNoCross_right_tripod_path_foot_clean_tail_to_boundary_at
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3)
    (hi : T.boundary i ∈ P.pathSet) :
    Exists fun z0 : V =>
      Exists fun x : V =>
        Exists fun a : V =>
          Exists fun q : S.graph.Walk x a =>
            (z0 ∈ (T.rim i).support ∨ z0 ∈ (T.leg i).support) ∧
              z0 ∈ P.rightSide ∧
                (Exists fun r : Fin 3 =>
                  x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
                a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
                  (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                    (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                      forall w : V,
                        w ∈ q.support ->
                          (Exists fun r : Fin 3 =>
                            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
                          w = x := by
  classical
  obtain ⟨z0, a, q0, hz0T, hz0Right, ha, hqPath, hqRight, hqOutside⟩ :=
    GMIX24Split.canonicalOfNoCross_right_tripod_path_foot_side_to_boundary_path_at
      P hno_cross T i hi
  let A : Set V := {w : V |
    Exists fun r : Fin 3 =>
      w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support}
  have hz0A : z0 ∈ A := by
    exact ⟨i, hz0T⟩
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hz0A
  let tail : S.graph.Walk x a := q0.dropUntil x hxq
  refine ⟨z0, x, a, tail, hz0T, hz0Right, ?_, ha, ?_, ?_, ?_, ?_⟩
  · simpa [A] using hxA
  · simpa [tail] using htail_path
  · intro w hw
    exact hqRight w (htail_subset w (by simpa [tail] using hw))
  · intro w hw
    exact hqOutside w (htail_subset w (by simpa [tail] using hw))
  · intro w hw hwA
    exact htail_clean w (by simpa [tail] using hw) (by simpa [A] using hwA)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

