import Schematic.Math.GraphTheory.Minors.Society.CutPath.CutSides

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Attachments for the ambient tripod produced in the source common-left-end
case.  The new rim endpoints are two old attachments.  The three new
attachments are: the first old path foot on the leg-segment rim, the old left
common end on the left-rim arm, and the old right common end on the
right-rim arm. -/
def commonLeftEndpointAttach {S : GeneralSociety V}
    (T : S.Tripod) (i : Fin 3) : Fin 3 -> V
  | 0 => T.boundary i
  | 1 => T.left
  | 2 => T.right

/-- Rims for the ambient tripod produced in the source common-left-end case. -/
def commonLeftEndpointRim {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j)) :
    Fin 3 -> S.graph.Walk (T.attach i) (T.attach j)
  | 0 =>
      T.liftAttachToAttachViaLegSegment hgraph i j
        (P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order))
  | 1 => (T.attachToAttachViaLeft i j).mapLe hgraph
  | 2 => (T.attachToAttachViaRight i j).mapLe hgraph

/-- Legs for the ambient tripod produced in the source common-left-end case. -/
def commonLeftEndpointLeg {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i k : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V}
    (q : S.graph.Walk T.left a) :
    forall r : Fin 3,
      S.graph.Walk (T.commonLeftEndpointAttach i r) (P.boundaryTriple a r)
  | 0 => P.pathTailToStart hi
  | 1 => q
  | 2 => T.rightToBoundaryViaLegTail hgraph k (P.pathTailToEnd hk)

/-- Core constructor for the source common-left-end tripod.

All non-disjoint fields are proved here from the ordered-foot normalization.
The three remaining structural conditions are passed as explicit hypotheses,
so the final source proof can close them one by one without re-elaborating the
large record construction. -/
def liftCommonLeftEndpointOrderedCore {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hrim_disjoint :
      forall r s : Fin 3, r ≠ s ->
        Disjoint
          (Walk.InternalVertices
            (T.commonLeftEndpointRim P hgraph hi hj hij_order r))
          (Walk.InternalVertices
            (T.commonLeftEndpointRim P hgraph hi hj hij_order s)))
    (hlegs_disjoint :
      forall r s : Fin 3, r ≠ s ->
        Disjoint
          {z : V | z ∈
            (T.commonLeftEndpointLeg P hgraph hi hk q r).support}
          {z : V | z ∈
            (T.commonLeftEndpointLeg P hgraph hi hk q s).support})
    (hlegs_meet_rims :
      forall r s : Fin 3, forall z : V,
        z ∈ (T.commonLeftEndpointLeg P hgraph hi hk q r).support ->
          z ∈ (T.commonLeftEndpointRim P hgraph hi hj hij_order s).support ->
            z = T.commonLeftEndpointAttach i r) :
    S.Tripod where
  left := T.attach i
  right := T.attach j
  left_ne_right := T.attach_ne_of_ne hij
  rim := T.commonLeftEndpointRim P hgraph hi hj hij_order
  rim_isPath := by
    intro r
    fin_cases r
    ·
      have hmiddle_clean :
          forall z : V,
            z ∈ (P.pathSegmentBetween hi hj
              (Nat.le_of_lt hij_order)).support ->
              z ∈ T.vertexSet ->
                z = T.boundary i ∨ z = T.boundary j := by
        intro z hz hzT
        exact
          P.pathSegmentBetween_clean_two_feet_of_path_contacts
            T hij hik hjk hi hj hij_order hjk_order
            hpath_contacts hz hzT
      simpa [Tripod.commonLeftEndpointRim] using
        T.liftAttachToAttachViaLegSegment_isPath hgraph hij
          (P.pathSegmentBetween_isPath hi hj (Nat.le_of_lt hij_order))
          hmiddle_clean
    ·
      simpa [Tripod.commonLeftEndpointRim] using
        SimpleGraph.Walk.IsPath.mapLe hgraph
          (T.attachToAttachViaLeft_isPath hij)
    ·
      simpa [Tripod.commonLeftEndpointRim] using
        SimpleGraph.Walk.IsPath.mapLe hgraph
          (T.attachToAttachViaRight_isPath hij)
  attach := T.commonLeftEndpointAttach i
  attach_mem_rim := by
    intro r
    fin_cases r
    ·
      have hbi_ne_ai : T.boundary i ≠ T.attach i :=
        by
          intro hboundary_attach
          exact hleg_i_not_nil
            ((T.boundary_eq_attach_iff_leg_nil i).mp hboundary_attach)
      have hbi_ne_aj : T.boundary i ≠ T.attach j := by
        intro h
        exact T.boundary_not_mem_rim_of_ne_index hij
          (by simpa [h] using (T.attach_mem_rim j).1)
      simpa [Tripod.commonLeftEndpointRim, Tripod.commonLeftEndpointAttach]
        using
          T.boundary_mem_internal_liftAttachToAttachViaLegSegment
            hgraph
            (P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order))
            hbi_ne_ai hbi_ne_aj
    ·
      simpa [Tripod.commonLeftEndpointRim, Tripod.commonLeftEndpointAttach,
        Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
        using T.left_mem_internal_attachToAttachViaLeft i j
    ·
      simpa [Tripod.commonLeftEndpointRim, Tripod.commonLeftEndpointAttach,
        Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
        using T.right_mem_internal_attachToAttachViaRight i j
  boundary := P.boundaryTriple a
  boundary_mem := P.boundaryTriple_mem_of_leftArc ha
  boundary_injective := P.boundaryTriple_injective_of_leftArc ha
  leg := T.commonLeftEndpointLeg P hgraph hi hk q
  leg_isPath := by
    intro r
    fin_cases r
    · simpa [Tripod.commonLeftEndpointLeg] using P.pathTailToStart_isPath hi
    · simpa [Tripod.commonLeftEndpointLeg] using hq_path
    ·
      have htail_clean :
          forall z : V, z ∈ (P.pathTailToEnd hk).support ->
            z ∈ T.vertexSet -> z = T.boundary k := by
        intro z hz hzT
        exact
          P.pathTailToEnd_clean_last_foot_of_path_contacts
            T hij hik hjk hk hij_order hjk_order hpath_contacts hz hzT
      simpa [Tripod.commonLeftEndpointLeg] using
        T.rightToBoundaryViaLegTail_isPath hgraph k
          (P.pathTailToEnd hk) (P.pathTailToEnd_isPath hk) htail_clean
  rim_internals_disjoint := hrim_disjoint
  legs_pairwise_disjoint := hlegs_disjoint
  legs_meet_rims_only_at_attach := hlegs_meet_rims

theorem commonLeftEndpointLegs_pairwise_disjoint {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (T.commonLeftEndpointLeg P hgraph hi hk q r).support}
        {z : V | z ∈
          (T.commonLeftEndpointLeg P hgraph hi hk q s).support} := by
  classical
  have hik' : k ≠ i := fun h => hik h.symm
  have h0q :
      Disjoint
        {z : V | z ∈ (P.pathTailToStart hi).support}
        {z : V | z ∈ q.support} := by
    rw [Set.disjoint_left]
    intro z hz0 hzq
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet hi z hz0
    exact (hq_outside z hzq).2 (by simpa [GMIX24CutPath.pathSet] using hzPath)
  have h02 :
      Disjoint
        {z : V | z ∈ (P.pathTailToStart hi).support}
        {z : V | z ∈
          (T.rightToBoundaryViaLegTail hgraph k
            (P.pathTailToEnd hk)).support} := by
    rw [Set.disjoint_left]
    intro z hz0 hz2
    rcases
        T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2
      with hzArm | hzRest
    · have hzRim : z ∈ (T.rim k).support :=
        T.rightToAttach_support_subset_rim k hzArm
      have hz0_clean :
          z = T.boundary i :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hz0
          (T.rim_mem_vertexSet (i := k) hzRim)
      exact T.boundary_not_mem_rim_of_ne_index hik
        (by simpa [hz0_clean] using hzRim)
    · rcases hzRest with hzLeg | hzTail
      · have hz0_clean :
            z = T.boundary i :=
          P.pathTailToStart_clean_first_foot_of_path_contacts
            T hij hik hjk hi hij_order hjk_order hpath_contacts hz0
            (T.leg_mem_vertexSet (i := k) hzLeg)
        exact
          T.boundary_not_mem_leg_of_ne (i := k) (j := i) hik'
            (by simpa [hz0_clean] using hzLeg)
      · exact
          Set.disjoint_left.mp
            (P.pathTailToStart_support_disjoint_pathTailToEnd
              hi hk (lt_trans hij_order hjk_order))
            hz0 hzTail
  have hq2 :
      Disjoint
        {z : V | z ∈ q.support}
        {z : V | z ∈
          (T.rightToBoundaryViaLegTail hgraph k
            (P.pathTailToEnd hk)).support} := by
    rw [Set.disjoint_left]
    intro z hzq hz2
    rcases
        T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2
      with hzArm | hzRest
    · have hzRim : z ∈ (T.rim k).support :=
        T.rightToAttach_support_subset_rim k hzArm
      have hzLeft : z = T.left :=
        hq_clean z hzq (T.rim_mem_vertexSet (i := k) hzRim)
      exact T.left_not_mem_rightToAttach k (by simpa [hzLeft] using hzArm)
    · rcases hzRest with hzLeg | hzTail
      · have hzLeft : z = T.left :=
          hq_clean z hzq (T.leg_mem_vertexSet (i := k) hzLeg)
        exact T.left_not_mem_leg k (by simpa [hzLeft] using hzLeg)
      · have hzPath : z ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet hk z hzTail
        exact (hq_outside z hzq).2
          (by simpa [GMIX24CutPath.pathSet] using hzPath)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · simpa [Tripod.commonLeftEndpointLeg] using h0q
  · simpa [Tripod.commonLeftEndpointLeg] using h02
  · simpa [Tripod.commonLeftEndpointLeg] using h0q.symm
  · exact False.elim (hrs rfl)
  · simpa [Tripod.commonLeftEndpointLeg] using hq2
  · simpa [Tripod.commonLeftEndpointLeg] using h02.symm
  · simpa [Tripod.commonLeftEndpointLeg] using hq2.symm
  · exact False.elim (hrs rfl)

/-- Pairwise disjointness for the common-left endpoint legs in the nil-residual
case where the old-left branch is replaced by a strict old-left-arm prefix plus
the clean outside tail. -/
theorem commonLeftEndpointLeftArmPrefixTail_legs_pairwise_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {x a : V}
    (hx_arm : x ∈ (T.leftToAttach k).support)
    (hx_ne_attach : x ≠ T.attach k)
    (q : S.graph.Walk x a)
    (hprefix_outside :
      forall z : V,
        z ∈ ((T.leftToAttach k).takeUntil x hx_arm).support ->
          z ∈ P.outside)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = x)
    (hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (T.commonLeftEndpointLeg P hgraph hi hk
            (T.leftArmPrefixTail hgraph hx_arm q) r).support}
        {z : V | z ∈
          (T.commonLeftEndpointLeg P hgraph hi hk
            (T.leftArmPrefixTail hgraph hx_arm q) s).support} := by
  classical
  have hik' : k ≠ i := fun h => hik h.symm
  have h0q :
      Disjoint
        {z : V | z ∈ (P.pathTailToStart hi).support}
        {z : V | z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support} := by
    rw [Set.disjoint_left]
    intro z hz0 hzqLeft
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet hi z hz0
    have hzCases :
        z ∈
            (((T.leftToAttach k).takeUntil x hx_arm).mapLe hgraph).support ∨
          z ∈ q.support := by
      simpa [Tripod.leftArmPrefixTail, SimpleGraph.Walk.mem_support_append_iff]
        using hzqLeft
    rcases hzCases with hzPrefixMap | hzq
    · have hzPrefix :
          z ∈ ((T.leftToAttach k).takeUntil x hx_arm).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
      exact (hprefix_outside z hzPrefix).2
        (by simpa [GMIX24CutPath.pathSet] using hzPath)
    · exact (hq_outside z hzq).2
        (by simpa [GMIX24CutPath.pathSet] using hzPath)
  have h02 :
      Disjoint
        {z : V | z ∈ (P.pathTailToStart hi).support}
        {z : V | z ∈
          (T.rightToBoundaryViaLegTail hgraph k
            (P.pathTailToEnd hk)).support} := by
    rw [Set.disjoint_left]
    intro z hz0 hz2
    rcases
        T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2
      with hzArm | hzRest
    · have hzRim : z ∈ (T.rim k).support :=
        T.rightToAttach_support_subset_rim k hzArm
      have hz0_clean :
          z = T.boundary i :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hz0
          (T.rim_mem_vertexSet (i := k) hzRim)
      exact T.boundary_not_mem_rim_of_ne_index hik
        (by simpa [hz0_clean] using hzRim)
    · rcases hzRest with hzLeg | hzTail
      · have hz0_clean :
            z = T.boundary i :=
          P.pathTailToStart_clean_first_foot_of_path_contacts
            T hij hik hjk hi hij_order hjk_order hpath_contacts hz0
            (T.leg_mem_vertexSet (i := k) hzLeg)
        exact
          T.boundary_not_mem_leg_of_ne (i := k) (j := i) hik'
            (by simpa [hz0_clean] using hzLeg)
      · exact
          Set.disjoint_left.mp
            (P.pathTailToStart_support_disjoint_pathTailToEnd
              hi hk (lt_trans hij_order hjk_order))
            hz0 hzTail
  have hq2 :
      Disjoint
        {z : V | z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support}
        {z : V | z ∈
          (T.rightToBoundaryViaLegTail hgraph k
            (P.pathTailToEnd hk)).support} := by
    rw [Set.disjoint_left]
    intro z hzqLeft hz2
    have hzLeftCases :
        z ∈
            (((T.leftToAttach k).takeUntil x hx_arm).mapLe hgraph).support ∨
          z ∈ q.support := by
      simpa [Tripod.leftArmPrefixTail, SimpleGraph.Walk.mem_support_append_iff]
        using hzqLeft
    rcases
        T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2
      with hzArm | hzRest
    · rcases hzLeftCases with hzPrefixMap | hzq
      · have hzPrefix :
            z ∈ ((T.leftToAttach k).takeUntil x hx_arm).support := by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
        exact
          Set.disjoint_left.mp
            (T.leftToAttach_takeUntil_support_disjoint_rightToAttach
              hx_arm hx_ne_attach)
            hzPrefix hzArm
      · have hzRim : z ∈ (T.rim k).support :=
          T.rightToAttach_support_subset_rim k hzArm
        have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := k) hzRim)
        have hx_attach : x = T.attach k :=
          T.leftToAttach_support_inter_rightToAttach_eq_attach k
            hx_arm (by simpa [hzx] using hzArm)
        exact hx_ne_attach hx_attach
    · rcases hzRest with hzLeg | hzTail
      · rcases hzLeftCases with hzPrefixMap | hzq
        · have hzPrefix :
              z ∈ ((T.leftToAttach k).takeUntil x hx_arm).support := by
            simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
          exact
            Set.disjoint_left.mp
              (T.leftToAttach_takeUntil_support_disjoint_leg
                hx_arm hx_ne_attach)
              hzPrefix hzLeg
        · have hzx : z = x :=
            hq_clean z hzq (T.leg_mem_vertexSet (i := k) hzLeg)
          exact hx_not_leg k (by simpa [hzx] using hzLeg)
      · have hzPath : z ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet hk z hzTail
        rcases hzLeftCases with hzPrefixMap | hzq
        · have hzPrefix :
              z ∈ ((T.leftToAttach k).takeUntil x hx_arm).support := by
            simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
          exact (hprefix_outside z hzPrefix).2
            (by simpa [GMIX24CutPath.pathSet] using hzPath)
        · exact (hq_outside z hzq).2
            (by simpa [GMIX24CutPath.pathSet] using hzPath)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · simpa [Tripod.commonLeftEndpointLeg] using h0q
  · simpa [Tripod.commonLeftEndpointLeg] using h02
  · simpa [Tripod.commonLeftEndpointLeg] using h0q.symm
  · exact False.elim (hrs rfl)
  · simpa [Tripod.commonLeftEndpointLeg] using hq2
  · simpa [Tripod.commonLeftEndpointLeg] using h02.symm
  · simpa [Tripod.commonLeftEndpointLeg] using hq2.symm
  · exact False.elim (hrs rfl)

theorem commonLeftEndpointLeg_zero_meets_rims {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall s : Fin 3, forall z : V,
      z ∈ (P.pathTailToStart hi).support ->
        z ∈ (T.commonLeftEndpointRim P hgraph hi hj hij_order s).support ->
          z = T.commonLeftEndpointAttach i 0 := by
  intro s z hzLeg hzRim
  have hclean_start :
      forall {w : V}, w ∈ (P.pathTailToStart hi).support ->
        w ∈ T.vertexSet -> w = T.boundary i := by
    intro w hw hwT
    exact
      P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hw hwT
  fin_cases s
  ·
    have hzRim0 :
        z ∈
          (T.liftAttachToAttachViaLegSegment hgraph i j
            (P.pathSegmentBetween hi hj
              (Nat.le_of_lt hij_order))).support := by
      simpa [Tripod.commonLeftEndpointRim] using hzRim
    rcases
        T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
      with hzOldI | hzRest
    · simpa [Tripod.commonLeftEndpointAttach] using
        hclean_start hzLeg (T.leg_mem_vertexSet (i := i) hzOldI)
    · rcases hzRest with hzMid | hzOldJ
      · have hzMidSegment :
            z ∈
              (Walk.segmentBetween P.path
                (by simpa [GMIX24CutPath.pathSet] using hi)
                (by simpa [GMIX24CutPath.pathSet] using hj)
                (Nat.le_of_lt hij_order)).support := by
          simpa [GMIX24CutPath.pathSegmentBetween] using hzMid
        simpa [Tripod.commonLeftEndpointAttach] using
          P.pathTailToStart_support_inter_segmentBetween_subset_left
            hi hj (Nat.le_of_lt hij_order) hzLeg hzMidSegment
      · simpa [Tripod.commonLeftEndpointAttach] using
          hclean_start hzLeg (T.leg_mem_vertexSet (i := j) hzOldJ)
  ·
    have hzOld :
        z ∈ (T.attachToAttachViaLeft i j).support := by
      simpa [Tripod.commonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
    rcases T.attachToAttachViaLeft_support_cases hzOld with hzi | hzj
    · simpa [Tripod.commonLeftEndpointAttach] using
        hclean_start hzLeg (T.rim_mem_vertexSet (i := i) hzi)
    · simpa [Tripod.commonLeftEndpointAttach] using
        hclean_start hzLeg (T.rim_mem_vertexSet (i := j) hzj)
  ·
    have hzOld :
        z ∈ (T.attachToAttachViaRight i j).support := by
      simpa [Tripod.commonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
    rcases T.attachToAttachViaRight_support_cases hzOld with hzi | hzj
    · simpa [Tripod.commonLeftEndpointAttach] using
        hclean_start hzLeg (T.rim_mem_vertexSet (i := i) hzi)
    · simpa [Tripod.commonLeftEndpointAttach] using
        hclean_start hzLeg (T.rim_mem_vertexSet (i := j) hzj)

theorem commonLeftEndpointLeg_one_meets_rims {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left) :
    forall s : Fin 3, forall z : V,
      z ∈ q.support ->
        z ∈ (T.commonLeftEndpointRim P hgraph hi hj hij_order s).support ->
          z = T.commonLeftEndpointAttach i 1 := by
  intro s z hzq hzRim
  fin_cases s
  ·
    have hzRim0 :
        z ∈
          (T.liftAttachToAttachViaLegSegment hgraph i j
            (P.pathSegmentBetween hi hj
              (Nat.le_of_lt hij_order))).support := by
      simpa [Tripod.commonLeftEndpointRim] using hzRim
    rcases
        T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
      with hzOldI | hzRest
    · simpa [Tripod.commonLeftEndpointAttach] using
        hq_clean z hzq (T.leg_mem_vertexSet (i := i) hzOldI)
    · rcases hzRest with hzMid | hzOldJ
      · have hzPath : z ∈ P.pathSet :=
          P.pathSegmentBetween_support_subset_pathSet
            hi hj (Nat.le_of_lt hij_order) z hzMid
        exact False.elim
          ((hq_outside z hzq).2
            (by simpa [GMIX24CutPath.pathSet] using hzPath))
      · simpa [Tripod.commonLeftEndpointAttach] using
          hq_clean z hzq (T.leg_mem_vertexSet (i := j) hzOldJ)
  ·
    have hzOld :
        z ∈ (T.attachToAttachViaLeft i j).support := by
      simpa [Tripod.commonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
    rcases T.attachToAttachViaLeft_support_cases hzOld with hzi | hzj
    · simpa [Tripod.commonLeftEndpointAttach] using
        hq_clean z hzq (T.rim_mem_vertexSet (i := i) hzi)
    · simpa [Tripod.commonLeftEndpointAttach] using
        hq_clean z hzq (T.rim_mem_vertexSet (i := j) hzj)
  ·
    have hzOld :
        z ∈ (T.attachToAttachViaRight i j).support := by
      simpa [Tripod.commonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
    rcases T.attachToAttachViaRight_support_cases hzOld with hzi | hzj
    · simpa [Tripod.commonLeftEndpointAttach] using
        hq_clean z hzq (T.rim_mem_vertexSet (i := i) hzi)
    · simpa [Tripod.commonLeftEndpointAttach] using
        hq_clean z hzq (T.rim_mem_vertexSet (i := j) hzj)

/-- Variant of `commonLeftEndpointLeg_one_meets_rims` for the nil-residual
case where the common-left branch first follows a strict old left arm to the
residual hit and then follows the clean outside tail.

This is one of the formal replacements for the old `BoundaryClean` shortcut in
the side-tripod paragraph of GM IX `(2.4)`. -/
theorem commonLeftEndpointLeftArmPrefixTail_meets_rims_only_at_left
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    {x a : V}
    (hx_arm : x ∈ (T.leftToAttach k).support)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (q : S.graph.Walk x a)
    (hprefix_outside :
      forall z : V,
        z ∈ ((T.leftToAttach k).takeUntil x hx_arm).support ->
          z ∈ P.outside)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = x)
    (hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support) :
    forall s : Fin 3, forall z : V,
      z ∈
        (T.leftArmPrefixTail hgraph hx_arm q).support ->
        z ∈ (T.commonLeftEndpointRim P hgraph hi hj hij_order s).support ->
          z = T.left := by
  classical
  have hki : k ≠ i := fun h => hik h.symm
  have hkj : k ≠ j := fun h => hjk h.symm
  have hx_not_rim_i : x ∉ (T.rim i).support := by
    intro hxi
    rcases T.rim_support_internal_or_endpoint hxi with hxiInt | hxiEnd
    · exact
        Set.disjoint_left.mp (T.rim_internals_disjoint k i hki)
          hx_internal hxiInt
    · rcases hxiEnd with hxLeft | hxRight
      · exact hx_internal.2.1 hxLeft
      · exact hx_internal.2.2 hxRight
  have hx_not_rim_j : x ∉ (T.rim j).support := by
    intro hxj
    rcases T.rim_support_internal_or_endpoint hxj with hxjInt | hxjEnd
    · exact
        Set.disjoint_left.mp (T.rim_internals_disjoint k j hkj)
          hx_internal hxjInt
    · rcases hxjEnd with hxLeft | hxRight
      · exact hx_internal.2.1 hxLeft
      · exact hx_internal.2.2 hxRight
  intro s z hzLeg hzRim
  have hzCases :
      z ∈
          (((T.leftToAttach k).takeUntil x hx_arm).mapLe hgraph).support ∨
        z ∈ q.support := by
    simpa [Tripod.leftArmPrefixTail, SimpleGraph.Walk.mem_support_append_iff]
      using hzLeg
  rcases hzCases with hzPrefixMap | hzq
  · have hzPrefix :
        z ∈ ((T.leftToAttach k).takeUntil x hx_arm).support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
    have hzPrefixRimK : z ∈ (T.rim k).support :=
      T.leftToAttach_support_subset_rim k
        (SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach k)
          hx_arm hzPrefix)
    fin_cases s
    ·
      have hzRim0 :
          z ∈
            (T.liftAttachToAttachViaLegSegment hgraph i j
              (P.pathSegmentBetween hi hj
                (Nat.le_of_lt hij_order))).support := by
        simpa [Tripod.commonLeftEndpointRim] using hzRim
      rcases T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
        with hzOldI | hzRest
      · have hzAttachI : z = T.attach i :=
          T.legs_meet_rims_only_at_attach i k z hzOldI hzPrefixRimK
        exact False.elim
          (T.attach_not_mem_rim_of_ne hik
            (by simpa [hzAttachI] using hzPrefixRimK))
      · rcases hzRest with hzMid | hzOldJ
        · have hzPath : z ∈ P.pathSet :=
            P.pathSegmentBetween_support_subset_pathSet
              hi hj (Nat.le_of_lt hij_order) z hzMid
          exact False.elim
            ((hprefix_outside z hzPrefix).2
              (by simpa [GMIX24CutPath.pathSet] using hzPath))
        · have hzAttachJ : z = T.attach j :=
            T.legs_meet_rims_only_at_attach j k z hzOldJ hzPrefixRimK
          exact False.elim
            (T.attach_not_mem_rim_of_ne hjk
              (by simpa [hzAttachJ] using hzPrefixRimK))
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaLeft i j).support := by
        simpa [Tripod.commonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaLeft_support_cases hzOld with hzi | hzj
      · exact
          T.leftToAttach_takeUntil_support_inter_rim_eq_left hki
            hx_arm hzPrefix hzi
      · exact
          T.leftToAttach_takeUntil_support_inter_rim_eq_left hkj
            hx_arm hzPrefix hzj
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaRight i j).support := by
        simpa [Tripod.commonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaRight_support_cases hzOld with hzi | hzj
      · exact
          T.leftToAttach_takeUntil_support_inter_rim_eq_left hki
            hx_arm hzPrefix hzi
      · exact
          T.leftToAttach_takeUntil_support_inter_rim_eq_left hkj
            hx_arm hzPrefix hzj
  · fin_cases s
    ·
      have hzRim0 :
          z ∈
            (T.liftAttachToAttachViaLegSegment hgraph i j
              (P.pathSegmentBetween hi hj
                (Nat.le_of_lt hij_order))).support := by
        simpa [Tripod.commonLeftEndpointRim] using hzRim
      rcases T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
        with hzOldI | hzRest
      · have hzx : z = x :=
          hq_clean z hzq (T.leg_mem_vertexSet (i := i) hzOldI)
        exact False.elim (hx_not_leg i (by simpa [hzx] using hzOldI))
      · rcases hzRest with hzMid | hzOldJ
        · have hzPath : z ∈ P.pathSet :=
            P.pathSegmentBetween_support_subset_pathSet
              hi hj (Nat.le_of_lt hij_order) z hzMid
          exact False.elim
            ((hq_outside z hzq).2
              (by simpa [GMIX24CutPath.pathSet] using hzPath))
        · have hzx : z = x :=
            hq_clean z hzq (T.leg_mem_vertexSet (i := j) hzOldJ)
          exact False.elim (hx_not_leg j (by simpa [hzx] using hzOldJ))
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaLeft i j).support := by
        simpa [Tripod.commonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaLeft_support_cases hzOld with hzi | hzj
      · have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := i) hzi)
        exact False.elim (hx_not_rim_i (by simpa [hzx] using hzi))
      · have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := j) hzj)
        exact False.elim (hx_not_rim_j (by simpa [hzx] using hzj))
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaRight i j).support := by
        simpa [Tripod.commonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaRight_support_cases hzOld with hzi | hzj
      · have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := i) hzi)
        exact False.elim (hx_not_rim_i (by simpa [hzx] using hzi))
      · have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := j) hzj)
        exact False.elim (hx_not_rim_j (by simpa [hzx] using hzj))

theorem commonLeftEndpointLegs_meet_rims_only_at_attach_of_right_branch
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hright_branch :
      forall s : Fin 3, forall z : V,
        z ∈
          (T.rightToBoundaryViaLegTail hgraph k
            (P.pathTailToEnd hk)).support ->
          z ∈ (T.commonLeftEndpointRim P hgraph hi hj hij_order s).support ->
            z = T.right) :
    forall r s : Fin 3, forall z : V,
      z ∈ (T.commonLeftEndpointLeg P hgraph hi hk q r).support ->
        z ∈ (T.commonLeftEndpointRim P hgraph hi hj hij_order s).support ->
          z = T.commonLeftEndpointAttach i r := by
  intro r s z hzLeg hzRim
  fin_cases r
  ·
    exact
      T.commonLeftEndpointLeg_zero_meets_rims
        P hgraph hij hik hjk hi hj hij_order hjk_order hpath_contacts
        s z (by simpa [Tripod.commonLeftEndpointLeg] using hzLeg) hzRim
  ·
    exact
      T.commonLeftEndpointLeg_one_meets_rims
        P hgraph hi hj hij_order q hq_outside hq_clean
        s z (by simpa [Tripod.commonLeftEndpointLeg] using hzLeg) hzRim
  ·
    simpa [Tripod.commonLeftEndpointAttach] using
      hright_branch s z
        (by simpa [Tripod.commonLeftEndpointLeg] using hzLeg) hzRim

theorem commonLeftEndpointRightBranch_meets_rims {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall s : Fin 3, forall z : V,
      z ∈
        (T.rightToBoundaryViaLegTail hgraph k
          (P.pathTailToEnd hk)).support ->
        z ∈ (T.commonLeftEndpointRim P hgraph hi hj hij_order s).support ->
          z = T.right := by
  classical
  have hki : k ≠ i := fun h => hik h.symm
  have hkj : k ≠ j := fun h => hjk h.symm
  have hmiddle_clean :
      forall z : V,
        z ∈ (P.pathSegmentBetween hi hj
          (Nat.le_of_lt hij_order)).support ->
          z ∈ T.vertexSet ->
            z = T.boundary i ∨ z = T.boundary j := by
    intro z hz hzT
    exact
      P.pathSegmentBetween_clean_two_feet_of_path_contacts
        T hij hik hjk hi hj hij_order hjk_order hpath_contacts hz hzT
  have htail_clean :
      forall z : V, z ∈ (P.pathTailToEnd hk).support ->
        z ∈ T.vertexSet -> z = T.boundary k := by
    intro z hz hzT
    exact
      P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hz hzT
  intro s z hzBranch hzRim
  rcases
      T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzBranch
    with hzArm | hzBranchRest
  · have hzRimK : z ∈ (T.rim k).support :=
      T.rightToAttach_support_subset_rim k hzArm
    fin_cases s
    ·
      have hzRim0 :
          z ∈
            (T.liftAttachToAttachViaLegSegment hgraph i j
              (P.pathSegmentBetween hi hj
                (Nat.le_of_lt hij_order))).support := by
        simpa [Tripod.commonLeftEndpointRim] using hzRim
      rcases
          T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
        with hzOldI | hzRest
      · have hzAttachI : z = T.attach i :=
          T.legs_meet_rims_only_at_attach i k z hzOldI hzRimK
        exact False.elim
          (T.attach_not_mem_rim_of_ne hik
            (by simpa [hzAttachI] using hzRimK))
      · rcases hzRest with hzMid | hzOldJ
        · rcases hmiddle_clean z hzMid (T.rim_mem_vertexSet (i := k) hzRimK)
            with hzi | hzj
          · exact False.elim
              (T.boundary_not_mem_rim_of_ne_index hik
                (by simpa [hzi] using hzRimK))
          · exact False.elim
              (T.boundary_not_mem_rim_of_ne_index hjk
                (by simpa [hzj] using hzRimK))
        · have hzAttachJ : z = T.attach j :=
            T.legs_meet_rims_only_at_attach j k z hzOldJ hzRimK
          exact False.elim
            (T.attach_not_mem_rim_of_ne hjk
              (by simpa [hzAttachJ] using hzRimK))
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaLeft i j).support := by
        simpa [Tripod.commonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaLeft_support_cases hzOld with hzi | hzj
      · exact T.rightToAttach_support_inter_rim_eq_right hki hzArm hzi
      · exact T.rightToAttach_support_inter_rim_eq_right hkj hzArm hzj
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaRight i j).support := by
        simpa [Tripod.commonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaRight_support_cases hzOld with hzi | hzj
      · exact T.rightToAttach_support_inter_rim_eq_right hki hzArm hzi
      · exact T.rightToAttach_support_inter_rim_eq_right hkj hzArm hzj
  · rcases hzBranchRest with hzLegK | hzTail
    · fin_cases s
      ·
        have hzRim0 :
            z ∈
              (T.liftAttachToAttachViaLegSegment hgraph i j
                (P.pathSegmentBetween hi hj
                  (Nat.le_of_lt hij_order))).support := by
          simpa [Tripod.commonLeftEndpointRim] using hzRim
        rcases
            T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
          with hzOldI | hzRest
        · exact False.elim
            (Set.disjoint_left.mp
              (T.legs_pairwise_disjoint k i hki) hzLegK hzOldI)
        · rcases hzRest with hzMid | hzOldJ
          · rcases hmiddle_clean z hzMid
                (T.leg_mem_vertexSet (i := k) hzLegK) with hzi | hzj
            · exact False.elim
                (T.boundary_not_mem_leg_of_ne (i := k) (j := i) hki
                  (by simpa [hzi] using hzLegK))
            · exact False.elim
                (T.boundary_not_mem_leg_of_ne (i := k) (j := j) hkj
                  (by simpa [hzj] using hzLegK))
          · exact False.elim
              (Set.disjoint_left.mp
                (T.legs_pairwise_disjoint k j hkj) hzLegK hzOldJ)
      ·
        have hzOld :
            z ∈ (T.attachToAttachViaLeft i j).support := by
          simpa [Tripod.commonLeftEndpointRim,
            SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
        rcases T.attachToAttachViaLeft_support_cases hzOld with hzi | hzj
        · have hzAttachK : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k i z hzLegK hzi
          exact False.elim
            (T.attach_not_mem_rim_of_ne hki
              (by simpa [hzAttachK] using hzi))
        · have hzAttachK : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k j z hzLegK hzj
          exact False.elim
            (T.attach_not_mem_rim_of_ne hkj
              (by simpa [hzAttachK] using hzj))
      ·
        have hzOld :
            z ∈ (T.attachToAttachViaRight i j).support := by
          simpa [Tripod.commonLeftEndpointRim,
            SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
        rcases T.attachToAttachViaRight_support_cases hzOld with hzi | hzj
        · have hzAttachK : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k i z hzLegK hzi
          exact False.elim
            (T.attach_not_mem_rim_of_ne hki
              (by simpa [hzAttachK] using hzi))
        · have hzAttachK : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k j z hzLegK hzj
          exact False.elim
            (T.attach_not_mem_rim_of_ne hkj
              (by simpa [hzAttachK] using hzj))
    · fin_cases s
      ·
        have hzRim0 :
            z ∈
              (T.liftAttachToAttachViaLegSegment hgraph i j
                (P.pathSegmentBetween hi hj
                  (Nat.le_of_lt hij_order))).support := by
          simpa [Tripod.commonLeftEndpointRim] using hzRim
        rcases
            T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
          with hzOldI | hzRest
        · have hzBoundaryK : z = T.boundary k :=
            htail_clean z hzTail (T.leg_mem_vertexSet (i := i) hzOldI)
          exact False.elim
            (T.boundary_not_mem_leg_of_ne (i := i) (j := k) hik
              (by simpa [hzBoundaryK] using hzOldI))
        · rcases hzRest with hzMid | hzOldJ
          · exact False.elim
              (Set.disjoint_left.mp
                (P.segmentBetween_support_disjoint_pathTailToEnd_of_lt
                  hi hj hk (Nat.le_of_lt hij_order) hjk_order)
                (by simpa [GMIX24CutPath.pathSegmentBetween] using hzMid)
                hzTail)
          · have hzBoundaryK : z = T.boundary k :=
              htail_clean z hzTail (T.leg_mem_vertexSet (i := j) hzOldJ)
            exact False.elim
              (T.boundary_not_mem_leg_of_ne (i := j) (j := k) hjk
                (by simpa [hzBoundaryK] using hzOldJ))
      ·
          have hzOld :
              z ∈ (T.attachToAttachViaLeft i j).support := by
            simpa [Tripod.commonLeftEndpointRim,
              SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
          rcases T.attachToAttachViaLeft_support_cases hzOld with hzi | hzj
          · have hzBoundaryK : z = T.boundary k :=
              htail_clean z hzTail (T.rim_mem_vertexSet (i := i) hzi)
            exact False.elim
              (T.boundary_not_mem_rim_of_ne_index (fun hki => hik hki.symm)
                (by simpa [hzBoundaryK] using hzi))
          · have hzBoundaryK : z = T.boundary k :=
              htail_clean z hzTail (T.rim_mem_vertexSet (i := j) hzj)
            exact False.elim
              (T.boundary_not_mem_rim_of_ne_index (fun hkj => hjk hkj.symm)
                (by simpa [hzBoundaryK] using hzj))
      ·
          have hzOld :
              z ∈ (T.attachToAttachViaRight i j).support := by
            simpa [Tripod.commonLeftEndpointRim,
              SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
          rcases T.attachToAttachViaRight_support_cases hzOld with hzi | hzj
          · have hzBoundaryK : z = T.boundary k :=
              htail_clean z hzTail (T.rim_mem_vertexSet (i := i) hzi)
            exact False.elim
              (T.boundary_not_mem_rim_of_ne_index (fun hki => hik hki.symm)
                (by simpa [hzBoundaryK] using hzi))
          · have hzBoundaryK : z = T.boundary k :=
              htail_clean z hzTail (T.rim_mem_vertexSet (i := j) hzj)
            exact False.elim
              (T.boundary_not_mem_rim_of_ne_index (fun hkj => hjk hkj.symm)
                (by simpa [hzBoundaryK] using hzj))

theorem commonLeftEndpointLegs_meet_rims_only_at_attach
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, forall z : V,
      z ∈ (T.commonLeftEndpointLeg P hgraph hi hk q r).support ->
        z ∈ (T.commonLeftEndpointRim P hgraph hi hj hij_order s).support ->
          z = T.commonLeftEndpointAttach i r :=
  T.commonLeftEndpointLegs_meet_rims_only_at_attach_of_right_branch
    P hgraph hij hik hjk hi hj hk hij_order hjk_order q hq_outside
      hq_clean hpath_contacts
      (T.commonLeftEndpointRightBranch_meets_rims
        P hgraph hij hik hjk hi hj hk hij_order hjk_order
        hpath_contacts)

theorem commonLeftEndpoint_left_right_rims_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j : Fin 3}
    (hij : i ≠ j)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j)) :
    Disjoint
      (Walk.InternalVertices
        (T.commonLeftEndpointRim P hgraph hi hj hij_order 1))
      (Walk.InternalVertices
        (T.commonLeftEndpointRim P hgraph hi hj hij_order 2)) := by
  rw [Set.disjoint_left]
  intro z hzLeft hzRight
  have hzLeftOld :
      z ∈ (T.attachToAttachViaLeft i j).support := by
    simpa [Tripod.commonLeftEndpointRim,
      Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using hzLeft.1
  have hzRightOld :
      z ∈ (T.attachToAttachViaRight i j).support := by
    simpa [Tripod.commonLeftEndpointRim,
      Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using hzRight.1
  rcases T.attachToAttachViaLeft_support_precise_cases hzLeftOld
    with hzLeftI | hzLeftJ
  · rcases T.attachToAttachViaRight_support_precise_cases hzRightOld
      with hzRightI | hzRightJ
    · have hzAttachI :
          z = T.attach i :=
        T.attachToLeft_support_inter_attachToRight_eq_attach i
          hzLeftI hzRightI
      exact hzLeft.2.1 hzAttachI
    · have hzRightEnd :
          z = T.right :=
        T.rightToAttach_support_inter_rim_eq_right
          (i := j) (j := i) (fun h => hij h.symm)
          hzRightJ (T.attachToLeft_support_subset_rim i hzLeftI)
      exact T.right_not_mem_attachToLeft i
        (by simpa [hzRightEnd] using hzLeftI)
  · rcases T.attachToAttachViaRight_support_precise_cases hzRightOld
      with hzRightI | hzRightJ
    · have hzLeftEnd :
          z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left
          (i := j) (j := i) (fun h => hij h.symm)
          hzLeftJ (T.attachToRight_support_subset_rim i hzRightI)
      exact T.left_not_mem_attachToRight i
        (by simpa [hzLeftEnd] using hzRightI)
    · have hzAttachJ :
          z = T.attach j :=
        T.leftToAttach_support_inter_rightToAttach_eq_attach j
          hzLeftJ hzRightJ
      exact hzLeft.2.2 hzAttachJ

private theorem commonLeftEndpoint_legSegment_rim_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (oldRim : H.graph.Walk (T.attach i) (T.attach j))
    (oldRim_support_cases :
      forall z : V, z ∈ oldRim.support ->
        z ∈ (T.rim i).support ∨ z ∈ (T.rim j).support) :
    Disjoint
      (Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j
          (P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order))))
      (Walk.InternalVertices (oldRim.mapLe hgraph)) := by
  rw [Set.disjoint_left]
  intro z hz0 hz1
  have hmiddle_clean :
      forall z : V,
        z ∈ (P.pathSegmentBetween hi hj
          (Nat.le_of_lt hij_order)).support ->
          z ∈ T.vertexSet ->
            z = T.boundary i ∨ z = T.boundary j := by
    intro w hw hwT
    exact
      P.pathSegmentBetween_clean_two_feet_of_path_contacts
        T hij hik hjk hi hj hij_order hjk_order hpath_contacts hw hwT
  have hz0Support :
      z ∈
        (T.liftAttachToAttachViaLegSegment hgraph i j
          (P.pathSegmentBetween hi hj
            (Nat.le_of_lt hij_order))).support := by
    exact hz0.1
  have hzOld : z ∈ oldRim.support := by
    simpa [Walk.InternalVertices,
      SimpleGraph.Walk.support_mapLe_eq_support] using hz1.1
  rcases T.liftAttachToAttachViaLegSegment_support_cases hgraph hz0Support
    with hzLegI | hzRest
  · rcases oldRim_support_cases z hzOld with hzRimI | hzRimJ
    · have hzAttachI : z = T.attach i :=
        T.legs_meet_rims_only_at_attach i i z hzLegI hzRimI
      exact hz0.2.1 hzAttachI
    · have hzAttachI : z = T.attach i :=
        T.legs_meet_rims_only_at_attach i j z hzLegI hzRimJ
      exact hz0.2.1 hzAttachI
  · rcases hzRest with hzMid | hzLegJ
    ·
      rcases oldRim_support_cases z hzOld with hzRimI | hzRimJ
      ·
        rcases hmiddle_clean z hzMid (T.rim_mem_vertexSet (i := i) hzRimI) with hzi | hzj
        · exact
            T.boundary_not_mem_own_rim_of_leg_not_nil hleg_i_not_nil
              (by simpa [hzi] using hzRimI)
        · exact
            T.boundary_not_mem_rim_of_ne_index (fun hji => hij hji.symm)
              (by simpa [hzj] using hzRimI)
      ·
        rcases hmiddle_clean z hzMid (T.rim_mem_vertexSet (i := j) hzRimJ) with hzi | hzj
        · exact
            T.boundary_not_mem_rim_of_ne_index hij
              (by simpa [hzi] using hzRimJ)
        · exact
            T.boundary_not_mem_own_rim_of_leg_not_nil hleg_j_not_nil
              (by simpa [hzj] using hzRimJ)
    · rcases oldRim_support_cases z hzOld with hzRimI | hzRimJ
      · have hzAttachJ : z = T.attach j :=
          T.legs_meet_rims_only_at_attach j i z hzLegJ hzRimI
        exact hz0.2.2 hzAttachJ
      · have hzAttachJ : z = T.attach j :=
          T.legs_meet_rims_only_at_attach j j z hzLegJ hzRimJ
        exact hz0.2.2 hzAttachJ

theorem commonLeftEndpoint_legSegment_left_rim_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Disjoint
      (Walk.InternalVertices
        (T.commonLeftEndpointRim P hgraph hi hj hij_order 0))
      (Walk.InternalVertices
        (T.commonLeftEndpointRim P hgraph hi hj hij_order 1)) := by
  simpa [Tripod.commonLeftEndpointRim] using
    T.commonLeftEndpoint_legSegment_rim_internal_disjoint
      P hgraph hij hik hjk hleg_i_not_nil hleg_j_not_nil hi hj
      hij_order hjk_order hpath_contacts (T.attachToAttachViaLeft i j)
      (fun z hz => T.attachToAttachViaLeft_support_cases hz)

theorem commonLeftEndpoint_legSegment_right_rim_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Disjoint
      (Walk.InternalVertices
        (T.commonLeftEndpointRim P hgraph hi hj hij_order 0))
      (Walk.InternalVertices
        (T.commonLeftEndpointRim P hgraph hi hj hij_order 2)) := by
  simpa [Tripod.commonLeftEndpointRim] using
    T.commonLeftEndpoint_legSegment_rim_internal_disjoint
      P hgraph hij hik hjk hleg_i_not_nil hleg_j_not_nil hi hj
      hij_order hjk_order hpath_contacts (T.attachToAttachViaRight i j)
      (fun z hz => T.attachToAttachViaRight_support_cases hz)

theorem commonLeftEndpointRims_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (T.commonLeftEndpointRim P hgraph hi hj hij_order r))
        (Walk.InternalVertices
          (T.commonLeftEndpointRim P hgraph hi hj hij_order s)) := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact
      T.commonLeftEndpoint_legSegment_left_rim_internal_disjoint
        P hgraph hij hik hjk hleg_i_not_nil hleg_j_not_nil
        hi hj hij_order hjk_order hpath_contacts
  · exact
      T.commonLeftEndpoint_legSegment_right_rim_internal_disjoint
        P hgraph hij hik hjk hleg_i_not_nil hleg_j_not_nil
        hi hj hij_order hjk_order hpath_contacts
  · exact
      (T.commonLeftEndpoint_legSegment_left_rim_internal_disjoint
        P hgraph hij hik hjk hleg_i_not_nil hleg_j_not_nil
        hi hj hij_order hjk_order hpath_contacts).symm
  · exact False.elim (hrs rfl)
  · exact
      T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hij hi hj hij_order
  · exact
      (T.commonLeftEndpoint_legSegment_right_rim_internal_disjoint
        P hgraph hij hik hjk hleg_i_not_nil hleg_j_not_nil
        hi hj hij_order hjk_order hpath_contacts).symm
  · exact
      (T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hij hi hj hij_order).symm
  · exact False.elim (hrs rfl)

/-- Common-left endpoint rim disjointness with no nontriviality assumption on
the second ordered old leg.

This is the source common-end case in its sharper form: only the first ordered
foot has to be separated from its attachment.  If the second foot has already
collapsed to its attachment, the rebuilt leg-segment rim uses that point as an
endpoint, so it cannot be an internal intersection. -/
theorem commonLeftEndpointRims_internal_disjoint_first_not_nil
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (T.commonLeftEndpointRim P hgraph hi hj hij_order r))
        (Walk.InternalVertices
          (T.commonLeftEndpointRim P hgraph hi hj hij_order s)) := by
  have hmiddle_clean :
      forall z : V,
        z ∈ (P.pathSegmentBetween hi hj
          (Nat.le_of_lt hij_order)).support ->
          z ∈ T.vertexSet ->
            z = T.boundary i ∨ z = T.boundary j := by
    intro z hz hzT
    exact
      P.pathSegmentBetween_clean_two_feet_of_path_contacts
        T hij hik hjk hi hj hij_order hjk_order hpath_contacts hz hzT
  have hleft :
      Disjoint
        (Walk.InternalVertices
          (T.commonLeftEndpointRim P hgraph hi hj hij_order 0))
        (Walk.InternalVertices
          (T.commonLeftEndpointRim P hgraph hi hj hij_order 1)) := by
    simpa [Tripod.commonLeftEndpointRim] using
      T.liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean_left_non_nil
        hgraph hij hmiddle_clean
  have hright :
      Disjoint
        (Walk.InternalVertices
          (T.commonLeftEndpointRim P hgraph hi hj hij_order 0))
        (Walk.InternalVertices
          (T.commonLeftEndpointRim P hgraph hi hj hij_order 2)) := by
    simpa [Tripod.commonLeftEndpointRim] using
      T.liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean_left_non_nil
        hgraph hij hmiddle_clean
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact hleft
  · exact hright
  · exact hleft.symm
  · exact False.elim (hrs rfl)
  · exact
      T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hij hi hj hij_order
  · exact hright.symm
  · exact
      (T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hij hi hj hij_order).symm
  · exact False.elim (hrs rfl)

theorem liftCommonLeftEndpointOrdered
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
      Nonempty S.Tripod :=
  ⟨T.liftCommonLeftEndpointOrderedCore
    P hgraph hij hik hjk hleg_i_not_nil hi hj hk hij_order hjk_order ha q hq_path
    hpath_contacts
    (T.commonLeftEndpointRims_internal_disjoint
      P hgraph hij hik hjk hleg_i_not_nil hleg_j_not_nil hi hj
      hij_order hjk_order hpath_contacts)
    (T.commonLeftEndpointLegs_pairwise_disjoint
      P hgraph hij hik hjk hi hk hij_order hjk_order q
      hq_outside hq_clean hpath_contacts)
    (T.commonLeftEndpointLegs_meet_rims_only_at_attach
      P hgraph hij hik hjk hi hj hk hij_order hjk_order q
      hq_outside hq_clean hpath_contacts)⟩

/-- Sharper common-left endpoint lift for the source side-tripod paragraph:
the second ordered old leg may be trivial. -/
theorem liftCommonLeftEndpointOrdered_first_not_nil
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
      Nonempty S.Tripod :=
  ⟨T.liftCommonLeftEndpointOrderedCore
    P hgraph hij hik hjk hleg_i_not_nil hi hj hk hij_order hjk_order ha q hq_path
    hpath_contacts
    (T.commonLeftEndpointRims_internal_disjoint_first_not_nil
      P hgraph hij hik hjk hi hj
      hij_order hjk_order hpath_contacts)
    (T.commonLeftEndpointLegs_pairwise_disjoint
      P hgraph hij hik hjk hi hk hij_order hjk_order q
      hq_outside hq_clean hpath_contacts)
    (T.commonLeftEndpointLegs_meet_rims_only_at_attach
      P hgraph hij hik hjk hi hj hk hij_order hjk_order q
      hq_outside hq_clean hpath_contacts)⟩

end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
