import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_tripod_pathTailToEnd_last_contact_not_same_branch
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun x : V =>
      x ∈ (P.pathTailToEnd hpath).support ∧
        (Exists fun k : Fin 3 =>
          x ∈ (T.rim k).support ∨ x ∈ (T.leg k).support) ∧
          x ≠ T.boundary i ∧
            Not
              (x ∈ (T.leg i).support ∨
                (x ∈ Walk.InternalVertices (T.rim i) ∧
                  forall j : Fin 3, x ≠ T.attach j)) := by
  let tail : S.graph.Walk (T.boundary i) P.t := P.pathTailToEnd hpath
  have hother :
      Exists fun w : V =>
        w ∈ tail.support ∧ w ∈ T.vertexSet ∧ w ≠ T.boundary i := by
    simpa [tail] using
      GMIX24Split.canonicalOfNoCross_left_tripod_pathTailToEnd_has_other_contact_of_no_tripod
        P hno_cross hno_tripod T hpath hoff
  obtain ⟨x, hx_tail, hxT, hx_ne_boundary, hnot_same⟩ :=
    T.exists_last_contact_outside_branch tail
      (P.pathTailToEnd_isPath hpath) hother (by
        intro x hx_tail hx_same hq_path hq_clean
        exact
          GMIX24Split.canonicalOfNoCross_left_tripod_same_branch_clean_tail_to_boundary_impossible
            P hno_cross hno_tripod T (tail.dropUntil x hx_tail) hoff
            (by simpa [Tripod.SameBranchContact] using hx_same)
            P.t_mem_boundary hq_path
            (by
              intro w hw hT
              exact hq_clean w hw (by simpa using hT)))
  exact ⟨x, by simpa [tail] using hx_tail, by simpa using hxT,
    hx_ne_boundary, by simpa [Tripod.SameBranchContact] using hnot_same⟩

theorem canonicalOfNoCross_right_tripod_pathTailToStart_last_contact_not_same_branch
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
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
      GMIX24Split.canonicalOfNoCross_right_tripod_pathTailToStart_has_other_contact_of_no_tripod
        P hno_cross hno_tripod T hpath hoff
  obtain ⟨x, hx_tail, hxT, hx_ne_boundary, hnot_same⟩ :=
    T.exists_last_contact_outside_branch tail
      (P.pathTailToStart_isPath hpath) hother (by
        intro x hx_tail hx_same hq_path hq_clean
        exact
          GMIX24Split.canonicalOfNoCross_right_tripod_same_branch_clean_tail_to_boundary_impossible
            P hno_cross hno_tripod T (tail.dropUntil x hx_tail) hoff
            (by simpa [Tripod.SameBranchContact] using hx_same)
            P.s_mem_boundary hq_path
            (by
              intro w hw hT
              exact hq_clean w hw (by simpa using hT)))
  exact ⟨x, by simpa [tail] using hx_tail, by simpa using hxT,
    hx_ne_boundary, by simpa [Tripod.SameBranchContact] using hnot_same⟩

theorem canonicalOfNoCross_right_tripod_pathTailToEnd_last_contact_not_same_branch
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun x : V =>
      x ∈ (P.pathTailToEnd hpath).support ∧
        (Exists fun k : Fin 3 =>
          x ∈ (T.rim k).support ∨ x ∈ (T.leg k).support) ∧
          x ≠ T.boundary i ∧
            Not
              (x ∈ (T.leg i).support ∨
                (x ∈ Walk.InternalVertices (T.rim i) ∧
                  forall j : Fin 3, x ≠ T.attach j)) := by
  let tail : S.graph.Walk (T.boundary i) P.t := P.pathTailToEnd hpath
  have hother :
      Exists fun w : V =>
        w ∈ tail.support ∧ w ∈ T.vertexSet ∧ w ≠ T.boundary i := by
    simpa [tail] using
      GMIX24Split.canonicalOfNoCross_right_tripod_pathTailToEnd_has_other_contact_of_no_tripod
        P hno_cross hno_tripod T hpath hoff
  obtain ⟨x, hx_tail, hxT, hx_ne_boundary, hnot_same⟩ :=
    T.exists_last_contact_outside_branch tail
      (P.pathTailToEnd_isPath hpath) hother (by
        intro x hx_tail hx_same hq_path hq_clean
        exact
          GMIX24Split.canonicalOfNoCross_right_tripod_same_branch_clean_tail_to_boundary_impossible
            P hno_cross hno_tripod T (tail.dropUntil x hx_tail) hoff
            (by simpa [Tripod.SameBranchContact] using hx_same)
            P.t_mem_boundary hq_path
            (by
              intro w hw hT
              exact hq_clean w hw (by simpa using hT)))
  exact ⟨x, by simpa [tail] using hx_tail, by simpa using hxT,
    hx_ne_boundary, by simpa [Tripod.SameBranchContact] using hnot_same⟩

theorem canonicalOfNoCross_left_tripod_pathTailToStart_escape_branch_of_no_tripod
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
        x ≠ T.boundary i ∧
          (x = T.left ∨ x = T.right ∨
            Exists fun k : Fin 3 =>
              k ≠ i ∧
                (x ∈ (T.leg k).support ∨
                  x ∈ Walk.InternalVertices (T.rim k))) := by
  obtain ⟨x, hxTail, hxT, hxne, hnotSame⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_pathTailToStart_last_contact_not_same_branch
      P hno_cross hno_tripod T hpath hoff
  exact ⟨x, hxTail, hxne,
    T.contact_not_same_branch_escape hxT hnotSame⟩

theorem canonicalOfNoCross_left_tripod_pathTailToEnd_escape_branch_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun x : V =>
      x ∈ (P.pathTailToEnd hpath).support ∧
        x ≠ T.boundary i ∧
          (x = T.left ∨ x = T.right ∨
            Exists fun k : Fin 3 =>
              k ≠ i ∧
                (x ∈ (T.leg k).support ∨
                  x ∈ Walk.InternalVertices (T.rim k))) := by
  obtain ⟨x, hxTail, hxT, hxne, hnotSame⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_pathTailToEnd_last_contact_not_same_branch
      P hno_cross hno_tripod T hpath hoff
  exact ⟨x, hxTail, hxne,
    T.contact_not_same_branch_escape hxT hnotSame⟩

theorem canonicalOfNoCross_right_tripod_pathTailToStart_escape_branch_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun x : V =>
      x ∈ (P.pathTailToStart hpath).support ∧
        x ≠ T.boundary i ∧
          (x = T.left ∨ x = T.right ∨
            Exists fun k : Fin 3 =>
              k ≠ i ∧
                (x ∈ (T.leg k).support ∨
                  x ∈ Walk.InternalVertices (T.rim k))) := by
  obtain ⟨x, hxTail, hxT, hxne, hnotSame⟩ :=
    GMIX24Split.canonicalOfNoCross_right_tripod_pathTailToStart_last_contact_not_same_branch
      P hno_cross hno_tripod T hpath hoff
  exact ⟨x, hxTail, hxne,
    T.contact_not_same_branch_escape hxT hnotSame⟩

theorem canonicalOfNoCross_right_tripod_pathTailToEnd_escape_branch_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun x : V =>
      x ∈ (P.pathTailToEnd hpath).support ∧
        x ≠ T.boundary i ∧
          (x = T.left ∨ x = T.right ∨
            Exists fun k : Fin 3 =>
              k ≠ i ∧
                (x ∈ (T.leg k).support ∨
                  x ∈ Walk.InternalVertices (T.rim k))) := by
  obtain ⟨x, hxTail, hxT, hxne, hnotSame⟩ :=
    GMIX24Split.canonicalOfNoCross_right_tripod_pathTailToEnd_last_contact_not_same_branch
      P hno_cross hno_tripod T hpath hoff
  exact ⟨x, hxTail, hxne,
    T.contact_not_same_branch_escape hxT hnotSame⟩

/-- A left side-tripod with a unique cut-path foot must escape that branch on
both sides of the foot.

This is the cut-path form of the source argument just before the
`Q, P_1, P_2, P_3` common-end analysis: following the induced path from the
unique foot toward either endpoint, the next contact with the side tripod
cannot lie on the same branch, otherwise the corresponding clean tail already
lifts to an ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_single_path_foot_two_tail_escapes
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    (∃ x : V,
      x ∈ (P.pathTailToStart hpath).support ∧
        x ≠ T.boundary i ∧
          (x = T.left ∨ x = T.right ∨
            ∃ k : Fin 3,
              k ≠ i ∧
                (x ∈ (T.leg k).support ∨
                  x ∈ Walk.InternalVertices (T.rim k)))) ∧
      ∃ y : V,
        y ∈ (P.pathTailToEnd hpath).support ∧
          y ≠ T.boundary i ∧
            (y = T.left ∨ y = T.right ∨
              ∃ k : Fin 3,
                k ≠ i ∧
                  (y ∈ (T.leg k).support ∨
                    y ∈ Walk.InternalVertices (T.rim k))) := by
  exact
    ⟨GMIX24Split.canonicalOfNoCross_left_tripod_pathTailToStart_escape_branch_of_no_tripod
        P hno_cross hno_tripod T hpath hoff,
      GMIX24Split.canonicalOfNoCross_left_tripod_pathTailToEnd_escape_branch_of_no_tripod
        P hno_cross hno_tripod T hpath hoff⟩

/-- Right-side version of
`canonicalOfNoCross_left_tripod_single_path_foot_two_tail_escapes`. -/
theorem canonicalOfNoCross_right_tripod_single_path_foot_two_tail_escapes
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    (∃ x : V,
      x ∈ (P.pathTailToStart hpath).support ∧
        x ≠ T.boundary i ∧
          (x = T.left ∨ x = T.right ∨
            ∃ k : Fin 3,
              k ≠ i ∧
                (x ∈ (T.leg k).support ∨
                  x ∈ Walk.InternalVertices (T.rim k)))) ∧
      ∃ y : V,
        y ∈ (P.pathTailToEnd hpath).support ∧
          y ≠ T.boundary i ∧
            (y = T.left ∨ y = T.right ∨
              ∃ k : Fin 3,
                k ≠ i ∧
                  (y ∈ (T.leg k).support ∨
                    y ∈ Walk.InternalVertices (T.rim k))) := by
  exact
    ⟨GMIX24Split.canonicalOfNoCross_right_tripod_pathTailToStart_escape_branch_of_no_tripod
        P hno_cross hno_tripod T hpath hoff,
      GMIX24Split.canonicalOfNoCross_right_tripod_pathTailToEnd_escape_branch_of_no_tripod
        P hno_cross hno_tripod T hpath hoff⟩

theorem canonicalOfNoCross_left_tripod_same_branch_clean_tail_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3} {x a : V}
    (q : S.graph.Walk x a)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hx_same_branch :
      x ∈ (T.leg i).support ∨
        (x ∈ Walk.InternalVertices (T.rim i) ∧
          forall j : Fin 3, x ≠ T.attach j))
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = x) :
    False := by
  rcases hx_same_branch with hxleg | hxrim
  · exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail
        P hno_cross T q ⟨i, hxleg, hoff⟩ ha hq_path hq_clean)
  · exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_rim_clean_tail
        P hno_cross T q ⟨i, hxrim.1, hoff, hxrim.2⟩ ha hq_path hq_clean)

theorem canonicalOfNoCross_right_tripod_same_branch_clean_tail_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3} {x a : V}
    (q : S.graph.Walk x a)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hx_same_branch :
      x ∈ (T.leg i).support ∨
        (x ∈ Walk.InternalVertices (T.rim i) ∧
          forall j : Fin 3, x ≠ T.attach j))
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = x) :
    False := by
  rcases hx_same_branch with hxleg | hxrim
  · exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail
        P hno_cross T q ⟨i, hxleg, hoff⟩ ha hq_path hq_clean)
  · exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_rim_clean_tail
        P hno_cross T q ⟨i, hxrim.1, hoff, hxrim.2⟩ ha hq_path hq_clean)

theorem canonicalOfNoCross_left_tripod_lift_of_nonendpoint_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
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
    (ha : a ∈ P.leftBoundaryArc)
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
  · exact GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail
      P hno_cross T q
      (by
        rcases hleg with ⟨i, hxi⟩
        exact ⟨i, hxi, hleg_off i hxi⟩)
      ha hq_path hq_clean
  · rcases hrest with hrim | hend
    · by_cases hattach : Exists fun j : Fin 3 => x = T.attach j
      · rcases hattach with ⟨j, hxj⟩
        have hxleg : x ∈ (T.leg j).support := by
          simp [hxj]
        exact GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail
          P hno_cross T q ⟨j, hxleg, hleg_off j hxleg⟩ ha hq_path
          hq_clean
      · have hnot_attach : forall j : Fin 3, x ≠ T.attach j := by
          intro j hxj
          exact hattach ⟨j, hxj⟩
        exact GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_rim_clean_tail
          P hno_cross T q
            (by
              rcases hrim with ⟨i, hxi⟩
              exact ⟨i, hxi, hrim_off i hxi hnot_attach, hnot_attach⟩)
            ha hq_path hq_clean
    · rcases hend with hleft | hright
      · exact False.elim (hx_ne_left hleft)
      · exact False.elim (hx_ne_right hright)

theorem canonicalOfNoCross_right_tripod_lift_of_nonendpoint_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
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
    (ha : a ∈ P.rightBoundaryArc)
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
  · exact GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail
      P hno_cross T q
      (by
        rcases hleg with ⟨i, hxi⟩
        exact ⟨i, hxi, hleg_off i hxi⟩)
      ha hq_path hq_clean
  · rcases hrest with hrim | hend
    · by_cases hattach : Exists fun j : Fin 3 => x = T.attach j
      · rcases hattach with ⟨j, hxj⟩
        have hxleg : x ∈ (T.leg j).support := by
          simp [hxj]
        exact GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail
          P hno_cross T q ⟨j, hxleg, hleg_off j hxleg⟩ ha hq_path
          hq_clean
      · have hnot_attach : forall j : Fin 3, x ≠ T.attach j := by
          intro j hxj
          exact hattach ⟨j, hxj⟩
        exact GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_rim_clean_tail
          P hno_cross T q
          (by
            rcases hrim with ⟨i, hxi⟩
            exact ⟨i, hxi, hrim_off i hxi hnot_attach, hnot_attach⟩)
          ha hq_path hq_clean
    · rcases hend with hleft | hright
      · exact False.elim (hx_ne_left hleft)
      · exact False.elim (hx_ne_right hright)

theorem canonicalOfNoCross_left_tripod_clean_tail_contact_endpoint_of_off_feet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support)
    (hleg_off :
      forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    x = T.left ∨ x = T.right := by
  by_cases hx_left : x = T.left
  · exact Or.inl hx_left
  · by_cases hx_right : x = T.right
    · exact Or.inr hx_right
    · exact False.elim
        (hno_tripod
          (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_nonendpoint_clean_tail
            P hno_cross T q hxT hx_left hx_right hleg_off hrim_off ha
            hq_path hq_clean))

theorem canonicalOfNoCross_right_tripod_clean_tail_contact_endpoint_of_off_feet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support)
    (hleg_off :
      forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    x = T.left ∨ x = T.right := by
  by_cases hx_left : x = T.left
  · exact Or.inl hx_left
  · by_cases hx_right : x = T.right
    · exact Or.inr hx_right
    · exact False.elim
        (hno_tripod
          (GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_nonendpoint_clean_tail
            P hno_cross T q hxT hx_left hx_right hleg_off hrim_off ha
            hq_path hq_clean))

theorem canonicalOfNoCross_right_tripod_clean_tail_of_left_reverse
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hleft :
      forall
        (T :
          (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        (x a : V) (q : S.graph.Walk x a),
        (Exists fun i : Fin 3 =>
          x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ->
          a ∈ P.reverse.leftBoundaryArc ->
            q.IsPath ->
              (forall w : V, w ∈ q.support -> w ∈ P.reverse.leftSide) ->
                (forall w : V, w ∈ q.support -> w ∈ P.reverse.outside) ->
                  (forall w : V,
                    w ∈ q.support ->
                      (Exists fun i : Fin 3 =>
                        w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
                        w = x) ->
                    Nonempty S.Tripod) :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
      (x a : V) (q : S.graph.Walk x a),
      (Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ->
        a ∈ P.rightBoundaryArc ->
          q.IsPath ->
            (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ->
              (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
                (forall w : V,
                  w ∈ q.support ->
                    (Exists fun i : Fin 3 =>
                      w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
                      w = x) ->
                  Nonempty S.Tripod := by
  classical
  intro T x a q hxT ha hq_path hq_side hq_outside hq_clean
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
    hSoc.symm ▸ T
  exact
    hleft Trev x a q
      (by simpa [Trev] using hxT)
      (by simpa using ha)
      hq_path
      (by
        intro w hw
        simpa using hq_side w hw)
      (by
        intro w hw
        simpa using hq_outside w hw)
      (by
        intro w hw hwT
        exact hq_clean w hw (by simpa [Trev] using hwT))

theorem canonicalOfNoCross_left_tripod_clean_tail_of_right_reverse
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hright :
      forall
        (T :
          (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).rightSociety.Tripod)
        (x a : V) (q : S.graph.Walk x a),
        (Exists fun i : Fin 3 =>
          x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ->
          a ∈ P.reverse.rightBoundaryArc ->
            q.IsPath ->
              (forall w : V, w ∈ q.support -> w ∈ P.reverse.rightSide) ->
                (forall w : V, w ∈ q.support -> w ∈ P.reverse.outside) ->
                  (forall w : V,
                    w ∈ q.support ->
                      (Exists fun i : Fin 3 =>
                        w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
                        w = x) ->
                    Nonempty S.Tripod) :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (x a : V) (q : S.graph.Walk x a),
      (Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ->
        a ∈ P.leftBoundaryArc ->
          q.IsPath ->
            (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
              (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
                (forall w : V,
                  w ∈ q.support ->
                    (Exists fun i : Fin 3 =>
                      w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
                      w = x) ->
                  Nonempty S.Tripod := by
  classical
  intro T x a q hxT ha hq_path hq_side hq_outside hq_clean
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).rightSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_rightSociety P hno_cross
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).rightSociety.Tripod :=
    hSoc.symm ▸ T
  exact
    hright Trev x a q
      (by simpa [Trev] using hxT)
      (by simpa using ha)
      hq_path
      (by
        intro w hw
        simpa using hq_side w hw)
      (by
        intro w hw
        simpa using hq_outside w hw)
      (by
        intro w hw hwT
        exact hq_clean w hw (by simpa [Trev] using hwT))

theorem canonicalOfNoCross_left_tripod_has_path_foot
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :
    Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet := by
  by_contra hnone
  push Not at hnone
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_all_feet_off_path
      P hno_cross T hnone)

theorem canonicalOfNoCross_right_tripod_has_path_foot
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod) :
    Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet := by
  by_contra hnone
  push Not at hnone
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_all_feet_off_path
      P hno_cross T hnone)

/-- First path-contact normalization for a left side-tripod.

If only one of the three tripod feet lies on the cut path, then
tripod-freeness of the ambient society forces another, non-foot contact of
the side tripod with the cut path.  This is the formal local version of the
source proof's step that an attempted side tripod cannot meet the induced
cut path only at a single terminal foot. -/
theorem canonicalOfNoCross_left_tripod_two_path_feet_or_hidden_path_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :
    (∃ i j : Fin 3,
      i ≠ j ∧ T.boundary i ∈ P.pathSet ∧ T.boundary j ∈ P.pathSet) ∨
      ∃ z : V,
        z ∈ P.pathSet ∧ z ∈ T.vertexSet ∧
          forall m : Fin 3, z ≠ T.boundary m := by
  classical
  rcases GMIX24Split.canonicalOfNoCross_left_tripod_has_path_foot
      P hno_cross hno_tripod T with
    ⟨i, hi_path⟩
  by_cases hsecond :
      ∃ j : Fin 3, i ≠ j ∧ T.boundary j ∈ P.pathSet
  · rcases hsecond with ⟨j, hij, hj_path⟩
    exact Or.inl ⟨i, j, hij, hi_path, hj_path⟩
  · right
    have hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet := by
      intro j hji hj_path
      exact hsecond ⟨j, (fun hij => hji hij.symm), hj_path⟩
    rcases
        GMIX24Split.canonicalOfNoCross_left_tripod_nonisolated_path_contact_of_no_tripod
          P hno_cross hno_tripod T hi_path hoff with
      ⟨z, hz_path, hzPacked, hz_ne_i⟩
    have hz_vertex : z ∈ T.vertexSet := by
      rcases hzPacked with ⟨k, hzRim | hzLeg⟩
      · exact T.rim_mem_vertexSet (i := k) hzRim
      · exact T.leg_mem_vertexSet (i := k) hzLeg
    refine ⟨z, hz_path, hz_vertex, ?_⟩
    intro m hzm
    by_cases hmi : m = i
    · subst m
      exact hz_ne_i hzm
    · exact hoff m hmi (by simpa [hzm] using hz_path)

/-- Right-side version of
`canonicalOfNoCross_left_tripod_two_path_feet_or_hidden_path_contact`. -/
theorem canonicalOfNoCross_right_tripod_two_path_feet_or_hidden_path_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod) :
    (∃ i j : Fin 3,
      i ≠ j ∧ T.boundary i ∈ P.pathSet ∧ T.boundary j ∈ P.pathSet) ∨
      ∃ z : V,
        z ∈ P.pathSet ∧ z ∈ T.vertexSet ∧
          forall m : Fin 3, z ≠ T.boundary m := by
  classical
  rcases GMIX24Split.canonicalOfNoCross_right_tripod_has_path_foot
      P hno_cross hno_tripod T with
    ⟨i, hi_path⟩
  by_cases hsecond :
      ∃ j : Fin 3, i ≠ j ∧ T.boundary j ∈ P.pathSet
  · rcases hsecond with ⟨j, hij, hj_path⟩
    exact Or.inl ⟨i, j, hij, hi_path, hj_path⟩
  · right
    have hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet := by
      intro j hji hj_path
      exact hsecond ⟨j, (fun hij => hji hij.symm), hj_path⟩
    rcases
        GMIX24Split.canonicalOfNoCross_right_tripod_nonisolated_path_contact_of_no_tripod
          P hno_cross hno_tripod T hi_path hoff with
      ⟨z, hz_path, hzPacked, hz_ne_i⟩
    have hz_vertex : z ∈ T.vertexSet := by
      rcases hzPacked with ⟨k, hzRim | hzLeg⟩
      · exact T.rim_mem_vertexSet (i := k) hzRim
      · exact T.leg_mem_vertexSet (i := k) hzLeg
    refine ⟨z, hz_path, hz_vertex, ?_⟩
    intro m hzm
    by_cases hmi : m = i
    · subst m
      exact hz_ne_i hzm
    · exact hoff m hmi (by simpa [hzm] using hz_path)

/-- Source-clean one-foot side-tripod normalization.

If a left side tripod has the exact GM IX `X -> Ω` cleanliness on its legs,
then the hidden cut-path contact produced in the one-path-foot case is on a
rim, not on a leg.  This is the first formal reduction of the printed
sentence "the paths `Q_i` end on `V(P)`" in the source-clean interface. -/
theorem canonicalOfNoCross_left_tripod_two_path_feet_or_hidden_rim_contact_of_legBoundaryContactClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hclean : T.LegBoundaryContactClean) :
    (∃ i j : Fin 3,
      i ≠ j ∧ T.boundary i ∈ P.pathSet ∧ T.boundary j ∈ P.pathSet) ∨
      ∃ z : V,
        z ∈ P.pathSet ∧
          (∃ r : Fin 3, z ∈ (T.rim r).support) ∧
          forall m : Fin 3, z ≠ T.boundary m := by
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_two_path_feet_or_hidden_path_contact
        P hno_cross hno_tripod T with
    htwo | hhidden
  · exact Or.inl htwo
  · rcases hhidden with ⟨z, hzPath, hzT, hzNotBoundary⟩
    have hzSideBoundary :
        z ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
      rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
      exact Or.inr hzPath
    exact Or.inr
      ⟨z, hzPath,
        T.rim_contact_of_legBoundaryContactClean_of_not_boundary hclean
          hzSideBoundary hzT hzNotBoundary,
        hzNotBoundary⟩

/-- Right-side version of
`canonicalOfNoCross_left_tripod_two_path_feet_or_hidden_rim_contact_of_legBoundaryContactClean`. -/
theorem canonicalOfNoCross_right_tripod_two_path_feet_or_hidden_rim_contact_of_legBoundaryContactClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hclean : T.LegBoundaryContactClean) :
    (∃ i j : Fin 3,
      i ≠ j ∧ T.boundary i ∈ P.pathSet ∧ T.boundary j ∈ P.pathSet) ∨
      ∃ z : V,
        z ∈ P.pathSet ∧
          (∃ r : Fin 3, z ∈ (T.rim r).support) ∧
          forall m : Fin 3, z ≠ T.boundary m := by
  rcases
      GMIX24Split.canonicalOfNoCross_right_tripod_two_path_feet_or_hidden_path_contact
        P hno_cross hno_tripod T with
    htwo | hhidden
  · exact Or.inl htwo
  · rcases hhidden with ⟨z, hzPath, hzT, hzNotBoundary⟩
    have hzSideBoundary :
        z ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet := by
      rw [GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet P hno_cross]
      exact Or.inr hzPath
    exact Or.inr
      ⟨z, hzPath,
        T.rim_contact_of_legBoundaryContactClean_of_not_boundary hclean
          hzSideBoundary hzT hzNotBoundary,
        hzNotBoundary⟩

/-- Path-contact normalization for a source-clean left side tripod once the
remaining hidden rim-contact obstruction has been ruled out. -/
theorem canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m :=
  GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_rim_contacts
    P hno_cross T hclean
    (by
      intro z hzPath hzRim
      by_contra hnone
      exact hno_hidden z hzPath hzRim (by
        intro m hm
        exact hnone ⟨m, hm⟩))

/-- Right-side version of
`canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact`. -/
theorem canonicalOfNoCross_right_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m :=
  GMIX24Split.canonicalOfNoCross_right_tripod_path_contacts_of_legBoundaryContactClean_and_rim_contacts
    P hno_cross T hclean
    (by
      intro z hzPath hzRim
      by_contra hnone
      exact hno_hidden z hzPath hzRim (by
        intro m hm
        exact hnone ⟨m, hm⟩))

/-- Once hidden rim contacts are excluded, a source-clean left side tripod has
all three feet on the induced cut path. -/
theorem canonicalOfNoCross_left_tripod_all_feet_on_path_of_legBoundaryContactClean_and_no_hidden_rim_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    forall i : Fin 3, T.boundary i ∈ P.pathSet :=
  GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
    P hno_cross hno_tripod T
    (GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hclean hno_hidden)

/-- Right-side version of
`canonicalOfNoCross_left_tripod_all_feet_on_path_of_legBoundaryContactClean_and_no_hidden_rim_contact`. -/
theorem canonicalOfNoCross_right_tripod_all_feet_on_path_of_legBoundaryContactClean_and_no_hidden_rim_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    forall i : Fin 3, T.boundary i ∈ P.pathSet :=
  GMIX24Split.canonicalOfNoCross_right_tripod_all_feet_on_path_of_no_tripod_path_contacts
    P hno_cross hno_tripod T
    (GMIX24Split.canonicalOfNoCross_right_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hclean hno_hidden)

theorem canonicalOfNoCross_left_tripod_lift_or_has_path_foot
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :
    Nonempty S.Tripod ∨
      Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet := by
  by_cases hsome : Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet
  · exact Or.inr hsome
  · left
    push Not at hsome
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_all_feet_off_path
        P hno_cross T hsome

theorem canonicalOfNoCross_right_tripod_lift_or_has_path_foot
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod) :
    Nonempty S.Tripod ∨
      Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet := by
  by_cases hsome : Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet
  · exact Or.inr hsome
  · left
    push Not at hsome
    exact
      GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_all_feet_off_path
        P hno_cross T hsome


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
