import Schematic.Math.GraphTheory.Minors.Society.CutPath.CommonEndpoint

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Attachments for the source common-end construction when the two outer
ordered side legs have collapsed to their cut-path feet.

The new rim endpoints are the two collapsed outer attachments.  The full
cut-path segment from the first to the last foot becomes one rim, with the
middle foot as its attachment.  The old left and right common endpoints are
the attachments on the two old side-rim routes. -/
def outerNilCommonLeftEndpointAttach {S : GeneralSociety V}
    (T : S.Tripod) (j : Fin 3) : Fin 3 -> V
  | 0 => T.boundary j
  | 1 => T.left
  | 2 => T.right

theorem outerNilCommonLeftEndpointAttach_injective {S : GeneralSociety V}
    (T : S.Tripod) (j : Fin 3) :
    Function.Injective (T.outerNilCommonLeftEndpointAttach j) := by
  intro r s hrs
  fin_cases r <;> fin_cases s <;>
    simp [Tripod.outerNilCommonLeftEndpointAttach] at hrs ⊢
  · exact False.elim
      (T.left_not_mem_leg j (by
        simpa [hrs] using (T.leg j).end_mem_support))
  · exact False.elim
      (T.right_not_mem_leg j (by
        simpa [hrs] using (T.leg j).end_mem_support))
  · exact False.elim
      (T.left_not_mem_leg j (by
        simpa [hrs.symm] using (T.leg j).end_mem_support))
  · exact False.elim (T.left_ne_right hrs)
  · exact False.elim
      (T.right_not_mem_leg j (by
        simpa [hrs.symm] using (T.leg j).end_mem_support))
  · exact False.elim (T.left_ne_right hrs.symm)

/-- Each rebuilt attachment in the double-outer-collapsed common-left
construction is an active vertex of the ambient society.

The median attachment is the middle side-tripod foot, which lies on the induced
cut path.  The other two attachments are the old common rim endpoints, and are
active through either old rim after mapping the side graph into the ambient
graph. -/
theorem outerNilCommonLeftEndpointAttach_mem_activeSet {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {j : Fin 3}
    (hj : T.boundary j ∈ P.pathSet) :
    forall r : Fin 3, T.outerNilCommonLeftEndpointAttach j r ∈ S.activeSet := by
  classical
  intro r
  fin_cases r
  · have hjSupport : T.boundary j ∈ S.graph.support :=
      SimpleGraph.mem_support_of_mem_walk_support P.path
        (by
          intro hnil
          exact P.s_ne_t (SimpleGraph.Walk.Nil.eq hnil))
        hj
    exact Or.inl (by
      simpa [Tripod.outerNilCommonLeftEndpointAttach] using hjSupport)
  · let rim : S.graph.Walk T.left T.right := (T.rim 0).mapLe hgraph
    have hleftMem : T.left ∈ rim.support := by
      simp [rim, SimpleGraph.Walk.support_mapLe_eq_support]
    have hleftSupport : T.left ∈ S.graph.support :=
      SimpleGraph.mem_support_of_mem_walk_support rim
        (by
          intro hnil
          exact T.left_ne_right (SimpleGraph.Walk.Nil.eq hnil))
        hleftMem
    exact Or.inl (by
      simpa [Tripod.outerNilCommonLeftEndpointAttach] using hleftSupport)
  · let rim : S.graph.Walk T.left T.right := (T.rim 0).mapLe hgraph
    have hrightMem : T.right ∈ rim.support := by
      simp [rim, SimpleGraph.Walk.support_mapLe_eq_support]
    have hrightSupport : T.right ∈ S.graph.support :=
      SimpleGraph.mem_support_of_mem_walk_support rim
        (by
          intro hnil
          exact T.left_ne_right (SimpleGraph.Walk.Nil.eq hnil))
        hrightMem
    exact Or.inl (by
      simpa [Tripod.outerNilCommonLeftEndpointAttach] using hrightSupport)

/-- Ambient boundary triple for the double-outer-collapsed common-left
endpoint construction: the median cut-path foot is routed to the side boundary
arc, while the old left and right common endpoints are routed to the two ends
of the cut path. -/
def outerNilCommonLeftEndpointBoundary {S : GeneralSociety V}
    (P : GMIX24CutPath S) (a : V) : Fin 3 -> V
  | 0 => a
  | 1 => P.s
  | 2 => P.t

theorem outerNilCommonLeftEndpointBoundary_mem_of_leftArc
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a : V} (ha : a ∈ P.leftBoundaryArc) :
    forall i : Fin 3,
      outerNilCommonLeftEndpointBoundary P a i ∈ S.boundarySet := by
  intro i
  fin_cases i
  · exact P.leftBoundaryArc_subset ha
  · exact P.s_mem_boundary
  · exact P.t_mem_boundary

theorem outerNilCommonLeftEndpointBoundary_injective_of_leftArc
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a : V} (ha : a ∈ P.leftBoundaryArc) :
    Function.Injective (outerNilCommonLeftEndpointBoundary P a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [outerNilCommonLeftEndpointBoundary] at hij ⊢
  · exact False.elim (P.leftBoundaryArc_ne_s ha hij)
  · exact False.elim (P.leftBoundaryArc_ne_t ha hij)
  · exact False.elim (P.leftBoundaryArc_ne_s ha hij.symm)
  · exact False.elim (P.s_ne_t hij)
  · exact False.elim (P.leftBoundaryArc_ne_t ha hij.symm)
  · exact False.elim (P.s_ne_t hij.symm)

/-- Rims for the double-outer-collapsed common-left endpoint constructor.

The first rim is the full induced cut-path segment between the two collapsed
outer feet.  The other two rims are the old side-tripod left and right routes
between the same outer attachments. -/
def outerNilCommonLeftEndpointRim {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    Fin 3 -> S.graph.Walk (T.attach i) (T.attach k)
  | 0 =>
      (P.pathSegmentBetween hi hk
        (Nat.le_of_lt (lt_trans hij_order hjk_order))).copy
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
  | 1 => (T.attachToAttachViaLeft i k).mapLe hgraph
  | 2 => (T.attachToAttachViaRight i k).mapLe hgraph

/-- The leg from the middle cut-path foot to the old left common endpoint and
then along the clean source path to the boundary arc. -/
def boundaryToLeftViaLegTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (j : Fin 3)
    {a : V}
    (q : S.graph.Walk T.left a) :
    S.graph.Walk (T.boundary j) a :=
  (((T.leg j).reverse.mapLe hgraph).append
    ((T.leftToAttach j).reverse.mapLe hgraph)).append q

/-- The middle-foot leg in the double-outer-collapsed common-left endpoint
constructor is a path when the outgoing source path is clean with respect to
the old side tripod. -/
theorem boundaryToLeftViaLegTail_isPath {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (j : Fin 3)
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left) :
    (T.boundaryToLeftViaLegTail hgraph j q).IsPath := by
  let oldLegRev : S.graph.Walk (T.boundary j) (T.attach j) :=
    (T.leg j).reverse.mapLe hgraph
  let armRev : S.graph.Walk (T.attach j) T.left :=
    (T.leftToAttach j).reverse.mapLe hgraph
  have holdLeg_path : oldLegRev.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath j).reverse
  have harm_path : armRev.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.leftToAttach_isPath j).reverse
  have hfirst : (oldLegRev.append armRev).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      holdLeg_path harm_path ?_
    intro z hzLeg hzArm
    have hzLegOld : z ∈ (T.leg j).support := by
      have hzLegMap : z ∈ ((T.leg j).reverse.mapLe hgraph).support := by
        simpa [oldLegRev] using hzLeg
      have hzLegRev : z ∈ (T.leg j).reverse.support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLegMap
      rw [SimpleGraph.Walk.support_reverse] at hzLegRev
      exact List.mem_reverse.mp hzLegRev
    have hzArmOld : z ∈ (T.leftToAttach j).support := by
      have hzArmMap : z ∈ ((T.leftToAttach j).reverse.mapLe hgraph).support := by
        simpa [armRev] using hzArm
      have hzArmRev : z ∈ (T.leftToAttach j).reverse.support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArmMap
      rw [SimpleGraph.Walk.support_reverse] at hzArmRev
      exact List.mem_reverse.mp hzArmRev
    have hzRim : z ∈ (T.rim j).support :=
      T.leftToAttach_support_subset_rim j hzArmOld
    exact T.legs_meet_rims_only_at_attach j j z hzLegOld hzRim
  change ((oldLegRev.append armRev).append q).IsPath
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    hfirst hq_path ?_
  intro z hzFirst hzq
  have hzFirstT : z ∈ T.vertexSet := by
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzFirst
    rcases hzFirst with hzLeg | hzArm
    · have hzLegOld : z ∈ (T.leg j).support := by
        have hzLegRev : z ∈ (T.leg j).reverse.support := by
          simpa [oldLegRev, SimpleGraph.Walk.support_mapLe_eq_support] using
            hzLeg
        rw [SimpleGraph.Walk.support_reverse] at hzLegRev
        exact List.mem_reverse.mp hzLegRev
      exact T.leg_mem_vertexSet (i := j) hzLegOld
    · have hzArmOld : z ∈ (T.leftToAttach j).support := by
        have hzArmRev : z ∈ (T.leftToAttach j).reverse.support := by
          simpa [armRev, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
        rw [SimpleGraph.Walk.support_reverse] at hzArmRev
        exact List.mem_reverse.mp hzArmRev
      exact T.rim_mem_vertexSet (i := j)
        (T.leftToAttach_support_subset_rim j hzArmOld)
  exact hq_clean z hzq hzFirstT

/-- Support decomposition for the middle leg in the double-outer-collapsed
common-left construction. -/
theorem boundaryToLeftViaLegTail_support_precise_cases {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (j : Fin 3)
    {a z : V}
    {q : S.graph.Walk T.left a}
    (hz : z ∈ (T.boundaryToLeftViaLegTail hgraph j q).support) :
    z ∈ (T.leg j).support ∨
      z ∈ (T.leftToAttach j).support ∨ z ∈ q.support := by
  rw [Tripod.boundaryToLeftViaLegTail,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzFirst | hzq
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzFirst
    rcases hzFirst with hzLeg | hzArm
    · have hzLegRev : z ∈ (T.leg j).reverse.support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg
      rw [SimpleGraph.Walk.support_reverse] at hzLegRev
      exact Or.inl (List.mem_reverse.mp hzLegRev)
    · have hzArmRev : z ∈ (T.leftToAttach j).reverse.support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
      rw [SimpleGraph.Walk.support_reverse] at hzArmRev
      exact Or.inr (Or.inl (List.mem_reverse.mp hzArmRev))
  · exact Or.inr (Or.inr hzq)

/-- Coarser support decomposition for the middle leg in the
double-outer-collapsed common-left construction. -/
theorem boundaryToLeftViaLegTail_support_cases {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (j : Fin 3)
    {a z : V}
    {q : S.graph.Walk T.left a}
    (hz : z ∈ (T.boundaryToLeftViaLegTail hgraph j q).support) :
    z ∈ (T.rim j).support ∨
      z ∈ (T.leg j).support ∨ z ∈ q.support := by
  rcases T.boundaryToLeftViaLegTail_support_precise_cases hgraph j hz with
    hzLeg | hzRest
  · exact Or.inr (Or.inl hzLeg)
  · rcases hzRest with hzArm | hzq
    · exact Or.inl (T.leftToAttach_support_subset_rim j hzArm)
    · exact Or.inr (Or.inr hzq)

/-- Legs for the double-outer-collapsed common-left endpoint constructor. -/
def outerNilCommonLeftEndpointLeg {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V}
    (q : S.graph.Walk T.left a) :
    forall r : Fin 3,
      S.graph.Walk (T.outerNilCommonLeftEndpointAttach j r)
        (outerNilCommonLeftEndpointBoundary P a r)
  | 0 => T.boundaryToLeftViaLegTail hgraph j q
  | 1 => T.leftToBoundaryViaLegTail hgraph i (P.pathTailToStart hi)
  | 2 => T.rightToBoundaryViaLegTail hgraph k (P.pathTailToEnd hk)

/-- The three legs in the double-outer-collapsed common-left endpoint
constructor are paths. -/
theorem outerNilCommonLeftEndpointLeg_isPath {S H : GeneralSociety V}
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
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r : Fin 3,
      (T.outerNilCommonLeftEndpointLeg P hgraph (j := j) hi hk q r).IsPath := by
  intro r
  fin_cases r
  ·
    simpa [Tripod.outerNilCommonLeftEndpointLeg] using
      T.boundaryToLeftViaLegTail_isPath hgraph j q hq_path hq_clean
  ·
    have htail_clean :
        forall z : V, z ∈ (P.pathTailToStart hi).support ->
          z ∈ T.vertexSet -> z = T.boundary i := by
      intro z hz hzT
      exact
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hz hzT
    simpa [Tripod.outerNilCommonLeftEndpointLeg] using
      T.leftToBoundaryViaLegTail_isPath hgraph i
        (P.pathTailToStart hi) (P.pathTailToStart_isPath hi) htail_clean
  ·
    have htail_clean :
        forall z : V, z ∈ (P.pathTailToEnd hk).support ->
          z ∈ T.vertexSet -> z = T.boundary k := by
      intro z hz hzT
      exact
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hz hzT
    simpa [Tripod.outerNilCommonLeftEndpointLeg] using
      T.rightToBoundaryViaLegTail_isPath hgraph k
        (P.pathTailToEnd hk) (P.pathTailToEnd_isPath hk) htail_clean

/-- The three rebuilt rims in the double-outer-collapsed common-left endpoint
constructor are paths. -/
theorem outerNilCommonLeftEndpointRim_isPath {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hik : i ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    forall r : Fin 3,
      (T.outerNilCommonLeftEndpointRim P hgraph hleg_i_nil hleg_k_nil hi hk
        hij_order hjk_order r).IsPath := by
  intro r
  fin_cases r
  ·
    have hmiddle :
        (P.pathSegmentBetween hi hk
          (Nat.le_of_lt (lt_trans hij_order hjk_order))).IsPath :=
      P.pathSegmentBetween_isPath hi hk
        (Nat.le_of_lt (lt_trans hij_order hjk_order))
    simpa [Tripod.outerNilCommonLeftEndpointRim,
      Tripod.liftAttachToAttachViaLegSegment] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathSegmentBetween hi hk
          (Nat.le_of_lt (lt_trans hij_order hjk_order)))
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).mpr
        hmiddle
  ·
    simpa [Tripod.outerNilCommonLeftEndpointRim] using
      SimpleGraph.Walk.IsPath.mapLe hgraph (T.attachToAttachViaLeft_isPath hik)
  ·
    simpa [Tripod.outerNilCommonLeftEndpointRim] using
      SimpleGraph.Walk.IsPath.mapLe hgraph (T.attachToAttachViaRight_isPath hik)

/-- In the double-outer-collapsed common-left endpoint construction, each new
attachment lies internally on its corresponding rim. -/
theorem outerNilCommonLeftEndpointAttach_mem_rim {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    forall r : Fin 3,
      T.outerNilCommonLeftEndpointAttach j r ∈
        Walk.InternalVertices
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r) := by
  intro r
  fin_cases r
  ·
    have hmiddle :
        T.boundary j ∈
          Walk.InternalVertices
            (P.pathSegmentBetween hi hk
              (Nat.le_of_lt (lt_trans hij_order hjk_order))) :=
      P.pathSegmentBetween_middle_boundary_mem_internal
        T hi hj hk hij_order hjk_order
    simpa [Tripod.outerNilCommonLeftEndpointAttach,
      Tripod.outerNilCommonLeftEndpointRim, Walk.internalVertices_copy] using
      hmiddle
  ·
    simpa [Tripod.outerNilCommonLeftEndpointAttach,
      Tripod.outerNilCommonLeftEndpointRim, Walk.InternalVertices,
      SimpleGraph.Walk.support_mapLe_eq_support] using
      T.left_mem_internal_attachToAttachViaLeft i k
  ·
    simpa [Tripod.outerNilCommonLeftEndpointAttach,
      Tripod.outerNilCommonLeftEndpointRim, Walk.InternalVertices,
      SimpleGraph.Walk.support_mapLe_eq_support] using
      T.right_mem_internal_attachToAttachViaRight i k

private theorem outerNilCommonLeftEndpoint_cut_rim_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (oldRim : H.graph.Walk (T.attach i) (T.attach k))
    (oldRim_support_cases :
      forall z : V, z ∈ oldRim.support ->
        z ∈ (T.rim i).support ∨ z ∈ (T.rim k).support) :
    Disjoint
      (Walk.InternalVertices
        ((P.pathSegmentBetween hi hk
          (Nat.le_of_lt (lt_trans hij_order hjk_order))).copy
            ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
            ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)))
      (Walk.InternalVertices (oldRim.mapLe hgraph)) := by
  rw [Set.disjoint_left]
  intro z hz0 hz1
  have hbi : T.boundary i = T.attach i :=
    (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil
  have hbk : T.boundary k = T.attach k :=
    (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil
  have hzSegment :
      z ∈
        (P.pathSegmentBetween hi hk
          (Nat.le_of_lt (lt_trans hij_order hjk_order))).support := by
    simpa [Walk.InternalVertices, Walk.internalVertices_copy] using hz0.1
  have hzOld :
      z ∈ oldRim.support := by
    simpa [Walk.InternalVertices,
      SimpleGraph.Walk.support_mapLe_eq_support] using hz1.1
  rcases oldRim_support_cases z hzOld with hzRimI | hzRimK
  · rcases
      P.pathSegmentBetween_clean_three_feet_of_path_contacts
        T hij hik hjk hi hk hij_order hjk_order hpath_contacts
        hzSegment (T.rim_mem_vertexSet (i := i) hzRimI)
      with hzi | hzjk
    · exact hz0.2.1 (hzi.trans hbi)
    · rcases hzjk with hzj | hzk
      · exact
          T.boundary_not_mem_rim_of_ne_index
            (i := j) (s := i) (fun hji => hij hji.symm)
            (by simpa [hzj] using hzRimI)
      · exact hz0.2.2 (hzk.trans hbk)
  · rcases
      P.pathSegmentBetween_clean_three_feet_of_path_contacts
        T hij hik hjk hi hk hij_order hjk_order hpath_contacts
        hzSegment (T.rim_mem_vertexSet (i := k) hzRimK)
      with hzi | hzjk
    · exact hz0.2.1 (hzi.trans hbi)
    · rcases hzjk with hzj | hzk
      · exact
          T.boundary_not_mem_rim_of_ne_index
            (i := j) (s := k) hjk
            (by simpa [hzj] using hzRimK)
      · exact hz0.2.2 (hzk.trans hbk)

/-- The full cut-path rim is internally disjoint from the old left side rim in
the double-outer-collapsed common-left endpoint construction. -/
theorem outerNilCommonLeftEndpoint_cut_left_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
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
    Disjoint
      (Walk.InternalVertices
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 0))
      (Walk.InternalVertices
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 1)) := by
  simpa [Tripod.outerNilCommonLeftEndpointRim] using
    T.outerNilCommonLeftEndpoint_cut_rim_internal_disjoint
      P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      hpath_contacts (T.attachToAttachViaLeft i k)
      (fun z hz => T.attachToAttachViaLeft_support_cases hz)

/-- Right-rim analogue of
`outerNilCommonLeftEndpoint_cut_left_internal_disjoint`. -/
theorem outerNilCommonLeftEndpoint_cut_right_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
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
    Disjoint
      (Walk.InternalVertices
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 0))
      (Walk.InternalVertices
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order 2)) := by
  simpa [Tripod.outerNilCommonLeftEndpointRim] using
    T.outerNilCommonLeftEndpoint_cut_rim_internal_disjoint
      P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      hpath_contacts (T.attachToAttachViaRight i k)
      (fun z hz => T.attachToAttachViaRight_support_cases hz)

/-- Internal disjointness of the three rims in the double-outer-collapsed
common-left endpoint construction. -/
theorem outerNilCommonLeftEndpointRims_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
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
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r))
        (Walk.InternalVertices
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s)) := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact
      T.outerNilCommonLeftEndpoint_cut_left_internal_disjoint
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
        hij_order hjk_order hpath_contacts
  · exact
      T.outerNilCommonLeftEndpoint_cut_right_internal_disjoint
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
        hij_order hjk_order hpath_contacts
  · exact
      (T.outerNilCommonLeftEndpoint_cut_left_internal_disjoint
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
        hij_order hjk_order hpath_contacts).symm
  · exact False.elim (hrs rfl)
  ·
    simpa [Tripod.outerNilCommonLeftEndpointRim,
      Tripod.commonLeftEndpointRim] using
      T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hik hi hk (lt_trans hij_order hjk_order)
  · exact
      (T.outerNilCommonLeftEndpoint_cut_right_internal_disjoint
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
        hij_order hjk_order hpath_contacts).symm
  ·
    simpa [Tripod.outerNilCommonLeftEndpointRim,
      Tripod.commonLeftEndpointRim] using
      (T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hik hi hk (lt_trans hij_order hjk_order)).symm
  · exact False.elim (hrs rfl)

/-- Source-correct double-outer-collapsed constructor from a GM IX `(2.2)`
linkage.

When both outer ordered side-tripod legs have collapsed, the naive legs through
the old common endpoint are not pairwise disjoint.  The paper instead invokes
the set-to-set linkage augmentation implicit in GM IX `(2.2)`.  This
constructor is the exact formal target for that step: once such a
vertex-disjoint linkage has been produced from the three rebuilt attachments to
the ambient boundary triple, the already-checked rim facts give the forbidden
ambient tripod immediately. -/
theorem liftOuterNilCommonLeftEndpointOfLinkage
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
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (L :
      ThreeVertexLinkage S.graph
        (T.outerNilCommonLeftEndpointAttach j)
        (Tripod.outerNilCommonLeftEndpointBoundary P a))
    (hlink_meet_rims :
      forall r s : Fin 3, forall z : V,
        z ∈ (L.path r).support ->
          z ∈
            (T.outerNilCommonLeftEndpointRim P hgraph
              hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
            z = T.outerNilCommonLeftEndpointAttach j r) :
    Nonempty S.Tripod :=
  ⟨Tripod.ofThreeVertexLinkage
    (S := S)
    (T.attach i)
    (T.attach k)
    (T.attach_ne_of_ne hik)
    (T.outerNilCommonLeftEndpointRim P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order)
    (T.outerNilCommonLeftEndpointRim_isPath P hgraph hik
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order)
    (T.outerNilCommonLeftEndpointAttach j)
    (T.outerNilCommonLeftEndpointAttach_mem_rim P hgraph
      hleg_i_nil hleg_k_nil hi hj hk hij_order hjk_order)
    (outerNilCommonLeftEndpointBoundary P a)
    (outerNilCommonLeftEndpointBoundary_mem_of_leftArc P ha)
    (outerNilCommonLeftEndpointBoundary_injective_of_leftArc P ha)
    L
    (T.outerNilCommonLeftEndpointRims_internal_disjoint P hgraph hij hik hjk
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hpath_contacts)
    hlink_meet_rims⟩

/-- Variant of `liftOuterNilCommonLeftEndpointOfLinkage` with an arbitrary
ambient boundary triple.

This is the form that matches the GM IX `(2.2)` set-to-boundary linkage
argument: the augmenting paths need only end at three distinct society-boundary
vertices, not at the later-specialized triple `(a,s,t)`.  The fixed-boundary
constructor above is recovered by taking `boundary =
Tripod.outerNilCommonLeftEndpointBoundary P a`. -/
theorem liftOuterNilCommonLeftEndpointOfBoundaryLinkage
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
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (boundary : Fin 3 -> V)
    (hboundary_mem : forall r : Fin 3, boundary r ∈ S.boundarySet)
    (hboundary_injective : Function.Injective boundary)
    (L :
      ThreeVertexLinkage S.graph
        (T.outerNilCommonLeftEndpointAttach j)
        boundary)
    (hlink_meet_rims :
      forall r s : Fin 3, forall z : V,
        z ∈ (L.path r).support ->
          z ∈
            (T.outerNilCommonLeftEndpointRim P hgraph
              hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
            z = T.outerNilCommonLeftEndpointAttach j r) :
    Nonempty S.Tripod :=
  ⟨Tripod.ofThreeVertexLinkage
    (S := S)
    (T.attach i)
    (T.attach k)
    (T.attach_ne_of_ne hik)
    (T.outerNilCommonLeftEndpointRim P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order)
    (T.outerNilCommonLeftEndpointRim_isPath P hgraph hik
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order)
    (T.outerNilCommonLeftEndpointAttach j)
    (T.outerNilCommonLeftEndpointAttach_mem_rim P hgraph
      hleg_i_nil hleg_k_nil hi hj hk hij_order hjk_order)
    boundary
    hboundary_mem
    hboundary_injective
    L
    (T.outerNilCommonLeftEndpointRims_internal_disjoint P hgraph hij hik hjk
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hpath_contacts)
    hlink_meet_rims⟩

/-- Source-correct double-outer-collapsed constructor from a linkage found in
a rim-avoiding subgraph.

This is the form in which the GM IX `(2.2)` augmenting-path argument should be
used.  Delete the forbidden rim vertices except for the three new attachments,
find the three disjoint paths in that subgraph, and this theorem transports the
linkage to the ambient graph and proves the required rim-intersection side
condition. -/
theorem liftOuterNilCommonLeftEndpointOfSubgraphLinkage
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
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (K : S.graph.Subgraph)
    (hattachK :
      forall r : Fin 3, T.outerNilCommonLeftEndpointAttach j r ∈ K.verts)
    (hboundaryK :
      forall r : Fin 3, outerNilCommonLeftEndpointBoundary P a r ∈ K.verts)
    (L :
      ThreeVertexLinkage K.coe
        (fun r : Fin 3 =>
          (⟨T.outerNilCommonLeftEndpointAttach j r, hattachK r⟩ : K.verts))
        (fun r : Fin 3 =>
          (⟨outerNilCommonLeftEndpointBoundary P a r, hboundaryK r⟩ : K.verts)))
    (hK_meets_rims_only_at_attach :
      forall (v : K.verts) (s : Fin 3),
        (v : V) ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun r : Fin 3 =>
            (v : V) = T.outerNilCommonLeftEndpointAttach j r) :
    Nonempty S.Tripod := by
  let L' :
      ThreeVertexLinkage S.graph
        (T.outerNilCommonLeftEndpointAttach j)
        (outerNilCommonLeftEndpointBoundary P a) :=
    L.mapSubgraph
  refine
    T.liftOuterNilCommonLeftEndpointOfLinkage
      P hgraph hij hik hjk hi hj hk hleg_i_nil hleg_k_nil
      hij_order hjk_order hpath_contacts ha L' ?_
  intro r s z hzL hzR
  exact
    L.mapSubgraph_meets_sets_only_at_left
      (fun s : Fin 3 =>
        {z : V |
          z ∈
            (T.outerNilCommonLeftEndpointRim P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support})
      hK_meets_rims_only_at_attach r s z hzL hzR

/-- Arbitrary-boundary version of
`liftOuterNilCommonLeftEndpointOfSubgraphLinkage`.

It transports a linkage found in any rim-avoiding induced subgraph to the
ambient society and then applies
`liftOuterNilCommonLeftEndpointOfBoundaryLinkage`. -/
theorem liftOuterNilCommonLeftEndpointOfBoundarySubgraphLinkage
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
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (boundary : Fin 3 -> V)
    (hboundary_mem : forall r : Fin 3, boundary r ∈ S.boundarySet)
    (hboundary_injective : Function.Injective boundary)
    (K : S.graph.Subgraph)
    (hattachK :
      forall r : Fin 3, T.outerNilCommonLeftEndpointAttach j r ∈ K.verts)
    (hboundaryK :
      forall r : Fin 3, boundary r ∈ K.verts)
    (L :
      ThreeVertexLinkage K.coe
        (fun r : Fin 3 =>
          (⟨T.outerNilCommonLeftEndpointAttach j r, hattachK r⟩ : K.verts))
        (fun r : Fin 3 =>
          (⟨boundary r, hboundaryK r⟩ : K.verts)))
    (hK_meets_rims_only_at_attach :
      forall (v : K.verts) (s : Fin 3),
        (v : V) ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun r : Fin 3 =>
            (v : V) = T.outerNilCommonLeftEndpointAttach j r) :
    Nonempty S.Tripod := by
  let L' :
      ThreeVertexLinkage S.graph
        (T.outerNilCommonLeftEndpointAttach j)
        boundary :=
    L.mapSubgraph
  refine
    T.liftOuterNilCommonLeftEndpointOfBoundaryLinkage
      P hgraph hij hik hjk hi hj hk hleg_i_nil hleg_k_nil
      hij_order hjk_order hpath_contacts boundary hboundary_mem
      hboundary_injective L' ?_
  intro r s z hzL hzR
  exact
    L.mapSubgraph_meets_sets_only_at_left
      (fun s : Fin 3 =>
        {z : V |
          z ∈
            (T.outerNilCommonLeftEndpointRim P hgraph
              hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support})
      hK_meets_rims_only_at_attach r s z hzL hzR

end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
