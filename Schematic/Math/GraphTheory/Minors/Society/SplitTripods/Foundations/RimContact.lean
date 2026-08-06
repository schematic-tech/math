import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations.LegReplacement

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- A hidden left-side rim contact supplies a clean cut-path tail to `s`.

Starting from a cut-path vertex on one of the side-tripod rims, take the tail
of the induced path back to `s` and stop at the last contact with the old
side tripod.  The resulting suffix is a path to the ambient boundary vertex
`s`, every vertex of it still lies on the cut path, and its only contact with
the old side tripod is its start.  This is the source object used by the
hidden-contact eliminator: once the start contact is classified as a
nonendpoint leg/rim contact with the appropriate off-foot conditions, the
existing replacement constructors build the forbidden ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_hidden_rim_contact_tail_to_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support) :
    Exists fun x : V =>
      Exists fun hxTail : x ∈ (P.pathTailToStart hzPath).support =>
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
          let q : S.graph.Walk x P.s :=
            (P.pathTailToStart hzPath).dropUntil x hxTail
          q.IsPath ∧
            (forall w : V, w ∈ q.support ->
              (Exists fun r : Fin 3 =>
                w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
              w = x) ∧
            forall w : V, w ∈ q.support -> w ∈ P.pathSet := by
  classical
  let tail : S.graph.Walk z P.s := P.pathTailToStart hzPath
  let A : Set V := {w : V |
    Exists fun r : Fin 3 =>
      w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support}
  have hstartA : z ∈ A := by
    rcases hzRim with ⟨r, hzr⟩
    exact ⟨r, Or.inl hzr⟩
  obtain ⟨x, hxTail, hxA, hq_path, hq_clean, hq_subset_tail,
      _hq_covers, _hq_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) (P.pathTailToStart_isPath hzPath) A hstartA
  refine ⟨x, by simpa [tail] using hxTail, by simpa [A] using hxA, ?_, ?_⟩
  · simpa [tail] using hq_path
  · constructor
    · intro w hw hwT
      exact hq_clean w (by simpa [tail] using hw) (by simpa [A] using hwT)
    · intro w hw
      exact P.pathTailToStart_support_subset_pathSet hzPath w
        (hq_subset_tail w (by simpa [tail] using hw))

/-- A hidden left-side rim contact supplies a clean cut-path tail to `t`. -/
theorem canonicalOfNoCross_left_tripod_hidden_rim_contact_tail_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support) :
    Exists fun x : V =>
      Exists fun hxTail : x ∈ (P.pathTailToEnd hzPath).support =>
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
          let q : S.graph.Walk x P.t :=
            (P.pathTailToEnd hzPath).dropUntil x hxTail
          q.IsPath ∧
            (forall w : V, w ∈ q.support ->
              (Exists fun r : Fin 3 =>
                w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
              w = x) ∧
            forall w : V, w ∈ q.support -> w ∈ P.pathSet := by
  classical
  let tail : S.graph.Walk z P.t := P.pathTailToEnd hzPath
  let A : Set V := {w : V |
    Exists fun r : Fin 3 =>
      w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support}
  have hstartA : z ∈ A := by
    rcases hzRim with ⟨r, hzr⟩
    exact ⟨r, Or.inl hzr⟩
  obtain ⟨x, hxTail, hxA, hq_path, hq_clean, hq_subset_tail,
      _hq_covers, _hq_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) (P.pathTailToEnd_isPath hzPath) A hstartA
  refine ⟨x, by simpa [tail] using hxTail, by simpa [A] using hxA, ?_, ?_⟩
  · simpa [tail] using hq_path
  · constructor
    · intro w hw hwT
      exact hq_clean w (by simpa [tail] using hw) (by simpa [A] using hwT)
    · intro w hw
      exact P.pathTailToEnd_support_subset_pathSet hzPath w
        (hq_subset_tail w (by simpa [tail] using hw))

theorem canonicalOfNoCross_left_tripod_lift_of_rim_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx :
      Exists fun i : Fin 3 =>
        x ∈ Walk.InternalVertices (T.rim i) ∧
          (forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) ∧
            forall j : Fin 3, x ≠ T.attach j)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  rcases hx with ⟨i, hxi, hoff, hane⟩
  fin_cases i
  · have ha_ne := T.clean_tail_from_rim_hit_not_boundary_of_ne_attach
      hxi.1 q hane hq_clean_vertex
    refine ⟨T.liftReplaceBoundaryZeroOnRimWithTail
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hxi ?_ ?_ (P.leftBoundaryArc_subset ha)
      (ha_ne 1) (ha_ne 2) q hq_path
      hq_clean_vertex⟩
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 1).mp (hoff 1 (by decide)))
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 2).mp (hoff 2 (by decide)))
  · have ha_ne := T.clean_tail_from_rim_hit_not_boundary_of_ne_attach
      hxi.1 q hane hq_clean_vertex
    refine ⟨T.liftReplaceBoundaryOneOnRimWithTail
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hxi ?_ ?_ (P.leftBoundaryArc_subset ha)
      (ha_ne 0) (ha_ne 2) q hq_path
      hq_clean_vertex⟩
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 0).mp (hoff 0 (by decide)))
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 2).mp (hoff 2 (by decide)))
  · have ha_ne := T.clean_tail_from_rim_hit_not_boundary_of_ne_attach
      hxi.1 q hane hq_clean_vertex
    refine ⟨T.liftReplaceBoundaryTwoOnRimWithTail
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hxi ?_ ?_ (P.leftBoundaryArc_subset ha)
      (ha_ne 0) (ha_ne 1) q hq_path
      hq_clean_vertex⟩
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 0).mp (hoff 0 (by decide)))
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 1).mp (hoff 1 (by decide)))

theorem canonicalOfNoCross_right_tripod_lift_of_rim_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx :
      Exists fun i : Fin 3 =>
        x ∈ Walk.InternalVertices (T.rim i) ∧
          (forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) ∧
            forall j : Fin 3, x ≠ T.attach j)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  classical
  let Trev := canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_rim_clean_tail
      P.reverse hno_cross Trev q
      (by simpa [Trev] using hx)
      (by simpa using ha) hq_path
      (by
        intro w hw hwT
        exact hq_clean w hw
          (by simpa [Trev] using hwT))

theorem canonicalOfNoCross_left_tripod_lift_of_rim_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x y : V} (q : S.graph.Walk x y)
    (hx :
      Exists fun i : Fin 3 =>
        x ∈ Walk.InternalVertices (T.rim i) ∧
          (forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) ∧
            forall j : Fin 3, x ≠ T.attach j)
    (hy_boundary : y ∈ S.boundarySet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  rcases hx with ⟨i, hxi, hoff, hane⟩
  fin_cases i
  · have hy_ne := T.clean_tail_from_rim_hit_not_boundary_of_ne_attach
      hxi.1 q hane hq_clean_vertex
    refine ⟨T.liftReplaceBoundaryZeroOnRimWithTail
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hxi ?_ ?_ hy_boundary
      (hy_ne 1) (hy_ne 2) q hq_path
      hq_clean_vertex⟩
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 1).mp (hoff 1 (by decide)))
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 2).mp (hoff 2 (by decide)))
  · have hy_ne := T.clean_tail_from_rim_hit_not_boundary_of_ne_attach
      hxi.1 q hane hq_clean_vertex
    refine ⟨T.liftReplaceBoundaryOneOnRimWithTail
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hxi ?_ ?_ hy_boundary
      (hy_ne 0) (hy_ne 2) q hq_path
      hq_clean_vertex⟩
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 0).mp (hoff 0 (by decide)))
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 2).mp (hoff 2 (by decide)))
  · have hy_ne := T.clean_tail_from_rim_hit_not_boundary_of_ne_attach
      hxi.1 q hane hq_clean_vertex
    refine ⟨T.liftReplaceBoundaryTwoOnRimWithTail
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hxi ?_ ?_ hy_boundary
      (hy_ne 0) (hy_ne 1) q hq_path
      hq_clean_vertex⟩
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 0).mp (hoff 0 (by decide)))
    · exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T 1).mp (hoff 1 (by decide)))

theorem canonicalOfNoCross_right_tripod_lift_of_rim_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x y : V} (q : S.graph.Walk x y)
    (hx :
      Exists fun i : Fin 3 =>
        x ∈ Walk.InternalVertices (T.rim i) ∧
          (forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) ∧
            forall j : Fin 3, x ≠ T.attach j)
    (hy_boundary : y ∈ S.boundarySet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  classical
  let Trev := canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_rim_clean_tail_to_boundary
      P.reverse hno_cross Trev q
      (by simpa [Trev] using hx)
      hy_boundary hq_path
      (by
        intro w hw hwT
        exact hq_clean w hw
          (by simpa [Trev] using hwT))

theorem canonicalOfNoCross_left_tripod_lift_of_nonendpoint_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x y : V} (q : S.graph.Walk x y)
    (hxT :
      Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support)
    (hx_ne_left : x ≠ T.left)
    (hx_ne_right : x ≠ T.right)
    (hleg_off :
      forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hy_boundary : y ∈ S.boundarySet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  have hxVertex : x ∈ T.vertexSet := by
    rcases hxT with ⟨i, hxi⟩
    rcases hxi with hxr | hxl
    · exact T.rim_mem_vertexSet (i := i) hxr
    · exact T.leg_mem_vertexSet (i := i) hxl
  rcases T.vertexSet_leg_or_rim_internal_or_endpoint hxVertex with hleg | hrest
  · exact GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_to_boundary
      P hno_cross T q
      (by
        rcases hleg with ⟨i, hxi⟩
        exact ⟨i, hxi, hleg_off i hxi⟩)
      hy_boundary hq_path hq_clean
  · rcases hrest with hrim | hend
    · by_cases hattach : Exists fun j : Fin 3 => x = T.attach j
      · rcases hattach with ⟨j, hxj⟩
        have hxleg : x ∈ (T.leg j).support := by
          simp [hxj]
        exact GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_to_boundary
          P hno_cross T q ⟨j, hxleg, hleg_off j hxleg⟩
          hy_boundary hq_path hq_clean
      · have hnot_attach : forall j : Fin 3, x ≠ T.attach j := by
          intro j hxj
          exact hattach ⟨j, hxj⟩
        exact GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_rim_clean_tail_to_boundary
          P hno_cross T q
          (by
            rcases hrim with ⟨i, hxi⟩
            exact ⟨i, hxi, hrim_off i hxi hnot_attach, hnot_attach⟩)
          hy_boundary hq_path hq_clean
    · rcases hend with hleft | hright
      · exact False.elim (hx_ne_left hleft)
      · exact False.elim (hx_ne_right hright)

theorem canonicalOfNoCross_right_tripod_lift_of_nonendpoint_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x y : V} (q : S.graph.Walk x y)
    (hxT :
      Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support)
    (hx_ne_left : x ≠ T.left)
    (hx_ne_right : x ≠ T.right)
    (hleg_off :
      forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hy_boundary : y ∈ S.boundarySet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  have hxVertex : x ∈ T.vertexSet := by
    rcases hxT with ⟨i, hxi⟩
    rcases hxi with hxr | hxl
    · exact T.rim_mem_vertexSet (i := i) hxr
    · exact T.leg_mem_vertexSet (i := i) hxl
  rcases T.vertexSet_leg_or_rim_internal_or_endpoint hxVertex with hleg | hrest
  · exact GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_to_boundary
      P hno_cross T q
      (by
        rcases hleg with ⟨i, hxi⟩
        exact ⟨i, hxi, hleg_off i hxi⟩)
      hy_boundary hq_path hq_clean
  · rcases hrest with hrim | hend
    · by_cases hattach : Exists fun j : Fin 3 => x = T.attach j
      · rcases hattach with ⟨j, hxj⟩
        have hxleg : x ∈ (T.leg j).support := by
          simp [hxj]
        exact GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_to_boundary
          P hno_cross T q ⟨j, hxleg, hleg_off j hxleg⟩
          hy_boundary hq_path hq_clean
      · have hnot_attach : forall j : Fin 3, x ≠ T.attach j := by
          intro j hxj
          exact hattach ⟨j, hxj⟩
        exact GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_rim_clean_tail_to_boundary
          P hno_cross T q
          (by
            rcases hrim with ⟨i, hxi⟩
            exact ⟨i, hxi, hrim_off i hxi hnot_attach, hnot_attach⟩)
          hy_boundary hq_path hq_clean
    · rcases hend with hleft | hright
      · exact False.elim (hx_ne_left hleft)
      · exact False.elim (hx_ne_right hright)

theorem canonicalOfNoCross_left_tripod_hidden_rim_contact_start_tail_endpoint_of_off_feet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun x : V =>
      Exists fun hxTail : x ∈ (P.pathTailToStart hzPath).support =>
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
          let q : S.graph.Walk x P.s :=
            (P.pathTailToStart hzPath).dropUntil x hxTail
          q.IsPath ∧
            (forall w : V, w ∈ q.support ->
              (Exists fun r : Fin 3 =>
                w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
              w = x) ∧
            (forall w : V, w ∈ q.support -> w ∈ P.pathSet) ∧
            (x = T.left ∨ x = T.right) := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_hidden_rim_contact_tail_to_start
        P hno_cross T hzPath hzRim with
    ⟨x, hxTail, hxT, hq_path, hq_clean, hq_pathSet⟩
  refine ⟨x, hxTail, hxT, hq_path, hq_clean, hq_pathSet, ?_⟩
  by_cases hx_left : x = T.left
  · exact Or.inl hx_left
  by_cases hx_right : x = T.right
  · exact Or.inr hx_right
  exact False.elim
    (hno_tripod
      (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_nonendpoint_clean_tail_to_boundary
        P hno_cross T ((P.pathTailToStart hzPath).dropUntil x hxTail) hxT
        hx_left hx_right (hleg_off x) (hrim_off x) P.s_mem_boundary
        hq_path hq_clean))

theorem canonicalOfNoCross_left_tripod_hidden_rim_contact_end_tail_endpoint_of_off_feet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun x : V =>
      Exists fun hxTail : x ∈ (P.pathTailToEnd hzPath).support =>
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ∧
          let q : S.graph.Walk x P.t :=
            (P.pathTailToEnd hzPath).dropUntil x hxTail
          q.IsPath ∧
            (forall w : V, w ∈ q.support ->
              (Exists fun r : Fin 3 =>
                w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
              w = x) ∧
            (forall w : V, w ∈ q.support -> w ∈ P.pathSet) ∧
            (x = T.left ∨ x = T.right) := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_hidden_rim_contact_tail_to_end
        P hno_cross T hzPath hzRim with
    ⟨x, hxTail, hxT, hq_path, hq_clean, hq_pathSet⟩
  refine ⟨x, hxTail, hxT, hq_path, hq_clean, hq_pathSet, ?_⟩
  by_cases hx_left : x = T.left
  · exact Or.inl hx_left
  by_cases hx_right : x = T.right
  · exact Or.inr hx_right
  exact False.elim
    (hno_tripod
      (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_nonendpoint_clean_tail_to_boundary
        P hno_cross T ((P.pathTailToEnd hzPath).dropUntil x hxTail) hxT
        hx_left hx_right (hleg_off x) (hrim_off x) P.t_mem_boundary
        hq_path hq_clean))

theorem canonicalOfNoCross_left_tripod_same_branch_clean_tail_to_boundary_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3} {x y : V}
    (q : S.graph.Walk x y)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hx_same_branch :
      x ∈ (T.leg i).support ∨
        (x ∈ Walk.InternalVertices (T.rim i) ∧
          forall j : Fin 3, x ≠ T.attach j))
    (hy_boundary : y ∈ S.boundarySet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = x) :
    False := by
  rcases hx_same_branch with hxleg | hxrim
  · exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_to_boundary
        P hno_cross T q ⟨i, hxleg, hoff⟩ hy_boundary hq_path hq_clean)
  · exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_rim_clean_tail_to_boundary
        P hno_cross T q ⟨i, hxrim.1, hoff, hxrim.2⟩
        hy_boundary hq_path hq_clean)

theorem canonicalOfNoCross_right_tripod_same_branch_clean_tail_to_boundary_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3} {x y : V}
    (q : S.graph.Walk x y)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hx_same_branch :
      x ∈ (T.leg i).support ∨
        (x ∈ Walk.InternalVertices (T.rim i) ∧
          forall j : Fin 3, x ≠ T.attach j))
    (hy_boundary : y ∈ S.boundarySet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = x) :
    False := by
  rcases hx_same_branch with hxleg | hxrim
  · exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_to_boundary
        P hno_cross T q ⟨i, hxleg, hoff⟩ hy_boundary hq_path hq_clean)
  · exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_rim_clean_tail_to_boundary
        P hno_cross T q ⟨i, hxrim.1, hoff, hxrim.2⟩
        hy_boundary hq_path hq_clean)

end GMIX24Split

/-- A contact lies on the branch through the indexed boundary foot, away from
all rim attachments in the rim case. -/
def Tripod.SameBranchContact {S : GeneralSociety V}
    (T : S.Tripod) (i : Fin 3) (x : V) : Prop :=
  x ∈ (T.leg i).support ∨
    (x ∈ Walk.InternalVertices (T.rim i) ∧
      forall j : Fin 3, x ≠ T.attach j)

/-- Select the last tripod contact of a path tail.  If the tail has a contact
after its initial boundary foot and every clean same-branch suffix is
impossible, the selected contact is distinct from that foot and leaves its
branch. -/
theorem Tripod.exists_last_contact_outside_branch
    [DecidableEq V] {S : GeneralSociety V} (T : S.Tripod)
    {G : SimpleGraph V} {i : Fin 3} {y : V}
    (tail : G.Walk (T.boundary i) y)
    (htail_path : tail.IsPath)
    (hother :
      Exists fun w : V =>
        w ∈ tail.support ∧ w ∈ T.vertexSet ∧ w ≠ T.boundary i)
    (hsame_impossible :
      forall {x : V} (hx : x ∈ tail.support),
        T.SameBranchContact i x ->
          (tail.dropUntil x hx).IsPath ->
            (forall w : V, w ∈ (tail.dropUntil x hx).support ->
              w ∈ T.vertexSet -> w = x) ->
              False) :
    Exists fun x : V =>
      x ∈ tail.support ∧ x ∈ T.vertexSet ∧ x ≠ T.boundary i ∧
        Not (T.SameBranchContact i x) := by
  classical
  obtain ⟨x, hx_tail, hxT, hlast_path, hlast_clean, _hlast_subset,
      hlast_covers, _hlast_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := G) htail_path T.vertexSet
        (T.leg_mem_vertexSet (T.leg i).end_mem_support)
  have hx_ne_boundary : x ≠ T.boundary i := by
    rcases hother with ⟨w, hw_tail, hwT, hw_ne⟩
    intro hx_boundary
    have hidx : tail.support.idxOf x <= tail.support.idxOf w := by
      rw [hx_boundary, Walk.idxOf_start_support tail]
      omega
    have hw_drop : w ∈ (tail.dropUntil x hx_tail).support :=
      hlast_covers w hw_tail hidx
    have hw_eq_x : w = x := hlast_clean w hw_drop hwT
    exact hw_ne (hw_eq_x.trans hx_boundary)
  have hnot_same : Not (T.SameBranchContact i x) := by
    intro hx_same
    exact hsame_impossible hx_tail hx_same hlast_path hlast_clean
  exact ⟨x, hx_tail, hxT, hx_ne_boundary, hnot_same⟩

namespace GMIX24Split

theorem canonicalOfNoCross_left_tripod_pathTailToStart_last_contact_not_same_branch
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun x : V =>
      x ∈ (P.pathTailToStart hpath).support ∧
        (Exists fun k : Fin 3 =>
          x ∈ (T.rim k).support ∨ x ∈ (T.leg k).support) ∧
          x ≠ T.boundary i ∧
            Not
              (x ∈ (T.leg i).support ∨
                (x ∈ Walk.InternalVertices (T.rim i) ∧
                  forall j : Fin 3, x ≠ T.attach j)) := by
  let tail : S.graph.Walk (T.boundary i) P.s := P.pathTailToStart hpath
  have hother :
      Exists fun w : V =>
        w ∈ tail.support ∧ w ∈ T.vertexSet ∧ w ≠ T.boundary i := by
    simpa [tail] using
      GMIX24Split.canonicalOfNoCross_left_tripod_pathTailToStart_has_other_contact_of_no_tripod
        P hno_cross hno_tripod T hpath hoff
  obtain ⟨x, hx_tail, hxT, hx_ne_boundary, hnot_same⟩ :=
    T.exists_last_contact_outside_branch tail
      (P.pathTailToStart_isPath hpath) hother (by
        intro x hx_tail hx_same hq_path hq_clean
        exact
          GMIX24Split.canonicalOfNoCross_left_tripod_same_branch_clean_tail_to_boundary_impossible
            P hno_cross hno_tripod T (tail.dropUntil x hx_tail) hoff
            (by simpa [Tripod.SameBranchContact] using hx_same)
            P.s_mem_boundary hq_path
            (by
              intro w hw hT
              exact hq_clean w hw (by simpa using hT)))
  exact ⟨x, by simpa [tail] using hx_tail,
    by simpa using hxT, hx_ne_boundary,
    by simpa [Tripod.SameBranchContact] using hnot_same⟩


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
