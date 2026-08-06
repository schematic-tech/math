import Schematic.Math.GraphTheory.Minors.Society.Basic.RimReconstruction

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- A branch leg from the old left common end through branch `k`, followed by
an ambient tail from the old boundary foot. -/
def leftToBoundaryViaLegTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (k : Fin 3)
    {y : V}
    (tail : S.graph.Walk (T.boundary k) y) :
    S.graph.Walk T.left y :=
  ((T.leftToAttach k).mapLe hgraph).append
    (((T.leg k).mapLe hgraph).append tail)

/-- A branch leg from the old right common end through branch `k`, followed by
an ambient tail from the old boundary foot. -/
def rightToBoundaryViaLegTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (k : Fin 3)
    {y : V}
    (tail : S.graph.Walk (T.boundary k) y) :
    S.graph.Walk T.right y :=
  ((T.rightToAttach k).mapLe hgraph).append
    (((T.leg k).mapLe hgraph).append tail)

theorem leftToBoundaryViaLegTail_isPath
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (k : Fin 3)
    {y : V}
    (tail : S.graph.Walk (T.boundary k) y)
    (htail_path : tail.IsPath)
    (htail_clean :
      forall z : V, z ∈ tail.support -> z ∈ T.vertexSet ->
        z = T.boundary k) :
    (T.leftToBoundaryViaLegTail hgraph k tail).IsPath := by
  let arm : S.graph.Walk T.left (T.attach k) :=
    (T.leftToAttach k).mapLe hgraph
  let oldLeg : S.graph.Walk (T.attach k) (T.boundary k) :=
    (T.leg k).mapLe hgraph
  have harm_path : arm.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.leftToAttach_isPath k)
  have holdLeg_path : oldLeg.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath k)
  have hfirst : (arm.append oldLeg).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      harm_path holdLeg_path ?_
    intro z hzArm hzLeg
    have hzRim : z ∈ (T.rim k).support := by
      have hzArmOld : z ∈ (T.leftToAttach k).support := by
        simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
      exact T.leftToAttach_support_subset_rim k hzArmOld
    have hzLegOld : z ∈ (T.leg k).support := by
      simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg
    exact T.legs_meet_rims_only_at_attach k k z hzLegOld hzRim
  change (arm.append (oldLeg.append tail)).IsPath
  rw [SimpleGraph.Walk.append_assoc]
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    hfirst htail_path ?_
  intro z hzFirst hzTail
  have hzFirstT : z ∈ T.vertexSet := by
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzFirst
    rcases hzFirst with hzArm | hzLeg
    · have hzArmOld : z ∈ (T.leftToAttach k).support := by
        simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
      exact T.rim_mem_vertexSet (i := k)
        (T.leftToAttach_support_subset_rim k hzArmOld)
    · have hzLegOld : z ∈ (T.leg k).support := by
        simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg
      exact T.leg_mem_vertexSet (i := k) hzLegOld
  exact htail_clean z hzTail hzFirstT

theorem rightToBoundaryViaLegTail_isPath
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (k : Fin 3)
    {y : V}
    (tail : S.graph.Walk (T.boundary k) y)
    (htail_path : tail.IsPath)
    (htail_clean :
      forall z : V, z ∈ tail.support -> z ∈ T.vertexSet ->
        z = T.boundary k) :
    (T.rightToBoundaryViaLegTail hgraph k tail).IsPath := by
  let arm : S.graph.Walk T.right (T.attach k) :=
    (T.rightToAttach k).mapLe hgraph
  let oldLeg : S.graph.Walk (T.attach k) (T.boundary k) :=
    (T.leg k).mapLe hgraph
  have harm_path : arm.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.rightToAttach_isPath k)
  have holdLeg_path : oldLeg.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath k)
  have hfirst : (arm.append oldLeg).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      harm_path holdLeg_path ?_
    intro z hzArm hzLeg
    have hzRim : z ∈ (T.rim k).support := by
      have hzArmOld : z ∈ (T.rightToAttach k).support := by
        simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
      exact T.rightToAttach_support_subset_rim k hzArmOld
    have hzLegOld : z ∈ (T.leg k).support := by
      simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg
    exact T.legs_meet_rims_only_at_attach k k z hzLegOld hzRim
  change (arm.append (oldLeg.append tail)).IsPath
  rw [SimpleGraph.Walk.append_assoc]
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    hfirst htail_path ?_
  intro z hzFirst hzTail
  have hzFirstT : z ∈ T.vertexSet := by
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzFirst
    rcases hzFirst with hzArm | hzLeg
    · have hzArmOld : z ∈ (T.rightToAttach k).support := by
        simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
      exact T.rim_mem_vertexSet (i := k)
        (T.rightToAttach_support_subset_rim k hzArmOld)
    · have hzLegOld : z ∈ (T.leg k).support := by
        simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg
      exact T.leg_mem_vertexSet (i := k) hzLegOld
  exact htail_clean z hzTail hzFirstT

theorem leftToBoundaryViaLegTail_support_cases
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (k : Fin 3)
    {y : V}
    {tail : S.graph.Walk (T.boundary k) y}
    {z : V}
    (hz : z ∈ (T.leftToBoundaryViaLegTail hgraph k tail).support) :
    z ∈ (T.rim k).support ∨
      z ∈ (T.leg k).support ∨ z ∈ tail.support := by
  rw [Tripod.leftToBoundaryViaLegTail,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzArm | hzRest
  · have hzArmOld : z ∈ (T.leftToAttach k).support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    exact Or.inl (T.leftToAttach_support_subset_rim k hzArmOld)
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzRest
    rcases hzRest with hzLeg | hzTail
    · exact Or.inr (Or.inl
        (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg))
    · exact Or.inr (Or.inr hzTail)

theorem leftToBoundaryViaLegTail_support_precise_cases
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (k : Fin 3)
    {y : V}
    {tail : S.graph.Walk (T.boundary k) y}
    {z : V}
    (hz : z ∈ (T.leftToBoundaryViaLegTail hgraph k tail).support) :
    z ∈ (T.leftToAttach k).support ∨
      z ∈ (T.leg k).support ∨ z ∈ tail.support := by
  rw [Tripod.leftToBoundaryViaLegTail,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzArm | hzRest
  · exact Or.inl
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzRest
    rcases hzRest with hzLeg | hzTail
    · exact Or.inr (Or.inl
        (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg))
    · exact Or.inr (Or.inr hzTail)

theorem rightToBoundaryViaLegTail_support_cases
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (k : Fin 3)
    {y : V}
    {tail : S.graph.Walk (T.boundary k) y}
    {z : V}
    (hz : z ∈ (T.rightToBoundaryViaLegTail hgraph k tail).support) :
    z ∈ (T.rim k).support ∨
      z ∈ (T.leg k).support ∨ z ∈ tail.support := by
  rw [Tripod.rightToBoundaryViaLegTail,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzArm | hzRest
  · have hzArmOld : z ∈ (T.rightToAttach k).support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    exact Or.inl (T.rightToAttach_support_subset_rim k hzArmOld)
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzRest
    rcases hzRest with hzLeg | hzTail
    · exact Or.inr (Or.inl
        (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg))
    · exact Or.inr (Or.inr hzTail)

theorem rightToBoundaryViaLegTail_support_precise_cases
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (k : Fin 3)
    {y : V}
    {tail : S.graph.Walk (T.boundary k) y}
    {z : V}
    (hz : z ∈ (T.rightToBoundaryViaLegTail hgraph k tail).support) :
    z ∈ (T.rightToAttach k).support ∨
      z ∈ (T.leg k).support ∨ z ∈ tail.support := by
  rw [Tripod.rightToBoundaryViaLegTail,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzArm | hzRest
  · exact Or.inl
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzRest
    rcases hzRest with hzLeg | hzTail
    · exact Or.inr (Or.inl
        (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg))
    · exact Or.inr (Or.inr hzTail)

def replaceBoundaryTwoOnLegWithTail {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {x y : V}
    (hx : x ∈ (T.leg 2).support)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary0 : y ≠ T.boundary 0)
    (hy_ne_boundary1 : y ≠ T.boundary 1)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod where
  left := T.left
  right := T.right
  left_ne_right := T.left_ne_right
  rim := T.rim
  rim_isPath := T.rim_isPath
  attach := T.attach
  attach_mem_rim := T.attach_mem_rim
  boundary := fun i : Fin 3 => if i = 2 then y else T.boundary i
  boundary_mem := by
    intro i
    fin_cases i
    · simpa using T.boundary_mem 0
    · simpa using T.boundary_mem 1
    · simpa using hy_boundary
  boundary_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp at hij ⊢
    · have h := T.boundary_injective hij
      simp at h
    · exact hy_ne_boundary0 hij.symm
    · have h := T.boundary_injective hij
      simp at h
    · exact hy_ne_boundary1 hij.symm
    · exact hy_ne_boundary0 hij
    · exact hy_ne_boundary1 hij
  leg := fun
    | 0 => by simpa using T.leg 0
    | 1 => by simpa using T.leg 1
    | 2 => by
        simpa using (((T.leg 2).takeUntil x hx).append q)
  leg_isPath := by
    intro i
    fin_cases i
    · simpa using T.leg_isPath 0
    · simpa using T.leg_isPath 1
    ·
      have hprefix_path : ((T.leg 2).takeUntil x hx).IsPath := by
        simpa using (T.leg_isPath 2).takeUntil hx
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hprefix_path hq_path ?_
      intro z hzPrefix hzq
      have hzT : z ∈ T.vertexSet :=
        T.leg_mem_vertexSet (i := 2)
          (SimpleGraph.Walk.support_takeUntil_subset (T.leg 2) hx hzPrefix)
      exact hq_clean z hzq hzT
  rim_internals_disjoint := T.rim_internals_disjoint
  legs_pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa using T.legs_pairwise_disjoint 0 1 (by decide)
    ·
      rw [Set.disjoint_left]
      intro v hv0 hv2
      change v ∈ (((T.leg 2).takeUntil x hx).append q).support at hv2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv2
      rcases hv2 with hvPrefix | hvq
      · exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 0 2 (by decide))
            hv0
            (SimpleGraph.Walk.support_takeUntil_subset (T.leg 2) hx hvPrefix)
      · have hvT : v ∈ T.vertexSet := T.leg_mem_vertexSet (i := 0) hv0
        have hvx : v = x := hq_clean v hvq hvT
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 0 2 (by decide))
            hv0 (by simpa [hvx] using hx)
    · simpa using T.legs_pairwise_disjoint 1 0 (by decide)
    · exact False.elim (hij rfl)
    ·
      rw [Set.disjoint_left]
      intro v hv1 hv2
      change v ∈ (((T.leg 2).takeUntil x hx).append q).support at hv2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv2
      rcases hv2 with hvPrefix | hvq
      · exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 1 2 (by decide))
            hv1
            (SimpleGraph.Walk.support_takeUntil_subset (T.leg 2) hx hvPrefix)
      · have hvT : v ∈ T.vertexSet := T.leg_mem_vertexSet (i := 1) hv1
        have hvx : v = x := hq_clean v hvq hvT
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 1 2 (by decide))
            hv1 (by simpa [hvx] using hx)
    ·
      rw [Set.disjoint_left]
      intro v hv2 hv0
      change v ∈ (((T.leg 2).takeUntil x hx).append q).support at hv2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv2
      rcases hv2 with hvPrefix | hvq
      · exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 2 0 (by decide))
            (SimpleGraph.Walk.support_takeUntil_subset (T.leg 2) hx hvPrefix)
            hv0
      · have hvT : v ∈ T.vertexSet := T.leg_mem_vertexSet (i := 0) hv0
        have hvx : v = x := hq_clean v hvq hvT
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 2 0 (by decide))
            (by simpa [hvx] using hx) hv0
    ·
      rw [Set.disjoint_left]
      intro v hv2 hv1
      change v ∈ (((T.leg 2).takeUntil x hx).append q).support at hv2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv2
      rcases hv2 with hvPrefix | hvq
      · exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 2 1 (by decide))
            (SimpleGraph.Walk.support_takeUntil_subset (T.leg 2) hx hvPrefix)
            hv1
      · have hvT : v ∈ T.vertexSet := T.leg_mem_vertexSet (i := 1) hv1
        have hvx : v = x := hq_clean v hvq hvT
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 2 1 (by decide))
            (by simpa [hvx] using hx) hv1
    · exact False.elim (hij rfl)
  legs_meet_rims_only_at_attach := by
    intro i j v hvleg hvrim
    fin_cases i
    · exact T.legs_meet_rims_only_at_attach 0 j v (by simpa using hvleg) hvrim
    · exact T.legs_meet_rims_only_at_attach 1 j v (by simpa using hvleg) hvrim
    ·
      change v ∈ (((T.leg 2).takeUntil x hx).append q).support at hvleg
      rw [SimpleGraph.Walk.mem_support_append_iff] at hvleg
      rcases hvleg with hvPrefix | hvq
      · exact T.legs_meet_rims_only_at_attach 2 j v
          (SimpleGraph.Walk.support_takeUntil_subset (T.leg 2) hx hvPrefix)
          hvrim
      · have hvT : v ∈ T.vertexSet := T.rim_mem_vertexSet (i := j) hvrim
        have hvx : v = x := hq_clean v hvq hvT
        exact T.legs_meet_rims_only_at_attach 2 j v
          (by simpa [hvx] using hx) hvrim

def replaceBoundaryZeroOnLegWithTail {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {x y : V}
    (hx : x ∈ (T.leg 0).support)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary1 : y ≠ T.boundary 1)
    (hy_ne_boundary2 : y ≠ T.boundary 2)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod := by
  let e : Fin 3 -> Fin 3 := fin3Order 1 2 0
  have he : Function.Injective e :=
    fin3Order_injective (by decide) (by decide) (by decide)
  let Tre := T.reindex e he
  have hxre : x ∈ (Tre.leg 2).support := by
    simpa [Tre, reindex, e, fin3Order] using hx
  have hy_ne0 : y ≠ Tre.boundary 0 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary1
  have hy_ne1 : y ≠ Tre.boundary 1 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary2
  have hq_clean_re :
      forall z : V, z ∈ q.support -> z ∈ Tre.vertexSet -> z = x := by
    intro z hzq hzTre
    exact hq_clean z hzq (T.reindex_vertexSet_subset e he hzTre)
  let Trep :=
    Tre.replaceBoundaryTwoOnLegWithTail hxre hy_boundary hy_ne0 hy_ne1
      q hq_path hq_clean_re
  let inv : Fin 3 -> Fin 3 := fin3Order 2 0 1
  have hinv : Function.Injective inv :=
    fin3Order_injective (by decide) (by decide) (by decide)
  exact Trep.reindex inv hinv

def replaceBoundaryOneOnLegWithTail {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {x y : V}
    (hx : x ∈ (T.leg 1).support)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary0 : y ≠ T.boundary 0)
    (hy_ne_boundary2 : y ≠ T.boundary 2)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod := by
  let e : Fin 3 -> Fin 3 := fin3Order 0 2 1
  have he : Function.Injective e :=
    fin3Order_injective (by decide) (by decide) (by decide)
  let Tre := T.reindex e he
  have hxre : x ∈ (Tre.leg 2).support := by
    simpa [Tre, reindex, e, fin3Order] using hx
  have hy_ne0 : y ≠ Tre.boundary 0 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary0
  have hy_ne1 : y ≠ Tre.boundary 1 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary2
  have hq_clean_re :
      forall z : V, z ∈ q.support -> z ∈ Tre.vertexSet -> z = x := by
    intro z hzq hzTre
    exact hq_clean z hzq (T.reindex_vertexSet_subset e he hzTre)
  let Trep :=
    Tre.replaceBoundaryTwoOnLegWithTail hxre hy_boundary hy_ne0 hy_ne1
      q hq_path hq_clean_re
  exact Trep.reindex e he

def liftReplaceBoundaryTwoOnLegWithTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {x y : V}
    (hx : x ∈ (T.leg 2).support)
    (hboundary0 : T.boundary 0 ∈ S.boundarySet)
    (hboundary1 : T.boundary 1 ∈ S.boundarySet)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary0 : y ≠ T.boundary 0)
    (hy_ne_boundary1 : y ≠ T.boundary 1)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod := by
  let leg2Lift : S.graph.Walk (T.attach 2) (T.boundary 2) :=
    (T.leg 2).mapLe hgraph
  have hxLift : x ∈ leg2Lift.support := by
    simpa [leg2Lift, SimpleGraph.Walk.support_mapLe_eq_support] using hx
  refine {
    left := T.left
    right := T.right
    left_ne_right := T.left_ne_right
    rim := fun i => (T.rim i).mapLe hgraph
    rim_isPath := by
      intro i
      exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.rim_isPath i)
    attach := T.attach
    attach_mem_rim := by
      intro i
      simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
        using T.attach_mem_rim i
    boundary := fun i : Fin 3 => if i = 2 then y else T.boundary i
    boundary_mem := ?_
    boundary_injective := ?_
    leg := ?_
    leg_isPath := ?_
    rim_internals_disjoint := ?_
    legs_pairwise_disjoint := ?_
    legs_meet_rims_only_at_attach := ?_
  }
  · intro i
    fin_cases i
    · simpa using hboundary0
    · simpa using hboundary1
    · simpa using hy_boundary
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp at hij ⊢
    · have h := T.boundary_injective hij
      simp at h
    · exact hy_ne_boundary0 hij.symm
    · have h := T.boundary_injective hij
      simp at h
    · exact hy_ne_boundary1 hij.symm
    · exact hy_ne_boundary0 hij
    · exact hy_ne_boundary1 hij
  · exact fun
      | 0 => by simpa using (T.leg 0).mapLe hgraph
      | 1 => by simpa using (T.leg 1).mapLe hgraph
      | 2 => by
          simpa [leg2Lift] using (leg2Lift.takeUntil x hxLift).append q
  · intro i
    fin_cases i
    · exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 0)
    · exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 1)
    ·
      have hprefix_path : (leg2Lift.takeUntil x hxLift).IsPath := by
        simpa using
          (SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 2)).takeUntil
            hxLift
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hprefix_path hq_path ?_
      intro z hzPrefix hzq
      have hzTleg : z ∈ (T.leg 2).support := by
        have hzLift : z ∈ leg2Lift.support :=
          SimpleGraph.Walk.support_takeUntil_subset leg2Lift hxLift hzPrefix
        simpa [leg2Lift, SimpleGraph.Walk.support_mapLe_eq_support] using hzLift
      have hzT : z ∈ T.vertexSet :=
        T.leg_mem_vertexSet (i := 2) hzTleg
      exact hq_clean z hzq hzT
  · intro i j hij
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.rim_internals_disjoint i j hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
        T.legs_pairwise_disjoint 0 1 (by decide)
    ·
      rw [Set.disjoint_left]
      intro v hv0 hv2
      change v ∈ ((leg2Lift.takeUntil x hxLift).append q).support at hv2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv2
      rcases hv2 with hvPrefix | hvq
      · have hv2old : v ∈ (T.leg 2).support := by
          have hvLift : v ∈ leg2Lift.support :=
            SimpleGraph.Walk.support_takeUntil_subset leg2Lift hxLift hvPrefix
          simpa [leg2Lift, SimpleGraph.Walk.support_mapLe_eq_support] using hvLift
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 0 2 (by decide))
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv0)
            hv2old
      · have hv0old : v ∈ (T.leg 0).support := by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv0
        have hvT : v ∈ T.vertexSet := T.leg_mem_vertexSet (i := 0) hv0old
        have hvx : v = x := hq_clean v hvq hvT
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 0 2 (by decide))
            hv0old (by simpa [hvx] using hx)
    · simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
        T.legs_pairwise_disjoint 1 0 (by decide)
    · exact False.elim (hij rfl)
    ·
      rw [Set.disjoint_left]
      intro v hv1 hv2
      change v ∈ ((leg2Lift.takeUntil x hxLift).append q).support at hv2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv2
      rcases hv2 with hvPrefix | hvq
      · have hv2old : v ∈ (T.leg 2).support := by
          have hvLift : v ∈ leg2Lift.support :=
            SimpleGraph.Walk.support_takeUntil_subset leg2Lift hxLift hvPrefix
          simpa [leg2Lift, SimpleGraph.Walk.support_mapLe_eq_support] using hvLift
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 1 2 (by decide))
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv1)
            hv2old
      · have hv1old : v ∈ (T.leg 1).support := by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv1
        have hvT : v ∈ T.vertexSet := T.leg_mem_vertexSet (i := 1) hv1old
        have hvx : v = x := hq_clean v hvq hvT
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 1 2 (by decide))
            hv1old (by simpa [hvx] using hx)
    ·
      rw [Set.disjoint_left]
      intro v hv2 hv0
      change v ∈ ((leg2Lift.takeUntil x hxLift).append q).support at hv2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv2
      rcases hv2 with hvPrefix | hvq
      · have hv2old : v ∈ (T.leg 2).support := by
          have hvLift : v ∈ leg2Lift.support :=
            SimpleGraph.Walk.support_takeUntil_subset leg2Lift hxLift hvPrefix
          simpa [leg2Lift, SimpleGraph.Walk.support_mapLe_eq_support] using hvLift
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 2 0 (by decide))
            hv2old
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv0)
      · have hv0old : v ∈ (T.leg 0).support := by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv0
        have hvT : v ∈ T.vertexSet := T.leg_mem_vertexSet (i := 0) hv0old
        have hvx : v = x := hq_clean v hvq hvT
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 2 0 (by decide))
            (by simpa [hvx] using hx) hv0old
    ·
      rw [Set.disjoint_left]
      intro v hv2 hv1
      change v ∈ ((leg2Lift.takeUntil x hxLift).append q).support at hv2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv2
      rcases hv2 with hvPrefix | hvq
      · have hv2old : v ∈ (T.leg 2).support := by
          have hvLift : v ∈ leg2Lift.support :=
            SimpleGraph.Walk.support_takeUntil_subset leg2Lift hxLift hvPrefix
          simpa [leg2Lift, SimpleGraph.Walk.support_mapLe_eq_support] using hvLift
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 2 1 (by decide))
            hv2old
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv1)
      · have hv1old : v ∈ (T.leg 1).support := by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv1
        have hvT : v ∈ T.vertexSet := T.leg_mem_vertexSet (i := 1) hv1old
        have hvx : v = x := hq_clean v hvq hvT
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint 2 1 (by decide))
            (by simpa [hvx] using hx) hv1old
    · exact False.elim (hij rfl)
  · intro i j v hvleg hvrim
    fin_cases i
    ·
      exact T.legs_meet_rims_only_at_attach 0 j v
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hvleg)
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hvrim)
    ·
      exact T.legs_meet_rims_only_at_attach 1 j v
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hvleg)
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hvrim)
    ·
      change v ∈ ((leg2Lift.takeUntil x hxLift).append q).support at hvleg
      rw [SimpleGraph.Walk.mem_support_append_iff] at hvleg
      rcases hvleg with hvPrefix | hvq
      · have hv2old : v ∈ (T.leg 2).support := by
          have hvLift : v ∈ leg2Lift.support :=
            SimpleGraph.Walk.support_takeUntil_subset leg2Lift hxLift hvPrefix
          simpa [leg2Lift, SimpleGraph.Walk.support_mapLe_eq_support] using hvLift
        exact T.legs_meet_rims_only_at_attach 2 j v hv2old
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hvrim)
      · have hvRimOld : v ∈ (T.rim j).support := by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hvrim
        have hvT : v ∈ T.vertexSet := T.rim_mem_vertexSet (i := j) hvRimOld
        have hvx : v = x := hq_clean v hvq hvT
        exact T.legs_meet_rims_only_at_attach 2 j v
          (by simpa [hvx] using hx) hvRimOld

def liftReplaceBoundaryZeroOnLegWithTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {x y : V}
    (hx : x ∈ (T.leg 0).support)
    (hboundary1 : T.boundary 1 ∈ S.boundarySet)
    (hboundary2 : T.boundary 2 ∈ S.boundarySet)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary1 : y ≠ T.boundary 1)
    (hy_ne_boundary2 : y ≠ T.boundary 2)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod := by
  let e : Fin 3 -> Fin 3 := fin3Order 1 2 0
  have he : Function.Injective e :=
    fin3Order_injective (by decide) (by decide) (by decide)
  let Tre := T.reindex e he
  have hxre : x ∈ (Tre.leg 2).support := by
    simpa [Tre, reindex, e, fin3Order] using hx
  have hb0 : Tre.boundary 0 ∈ S.boundarySet := by
    simpa [Tre, reindex, e, fin3Order] using hboundary1
  have hb1 : Tre.boundary 1 ∈ S.boundarySet := by
    simpa [Tre, reindex, e, fin3Order] using hboundary2
  have hy_ne0 : y ≠ Tre.boundary 0 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary1
  have hy_ne1 : y ≠ Tre.boundary 1 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary2
  have hq_clean_re :
      forall z : V, z ∈ q.support -> z ∈ Tre.vertexSet -> z = x := by
    intro z hzq hzTre
    exact hq_clean z hzq (T.reindex_vertexSet_subset e he hzTre)
  exact Tre.liftReplaceBoundaryTwoOnLegWithTail hgraph hxre
    hb0 hb1 hy_boundary hy_ne0 hy_ne1 q hq_path hq_clean_re

def liftReplaceBoundaryOneOnLegWithTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {x y : V}
    (hx : x ∈ (T.leg 1).support)
    (hboundary0 : T.boundary 0 ∈ S.boundarySet)
    (hboundary2 : T.boundary 2 ∈ S.boundarySet)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary0 : y ≠ T.boundary 0)
    (hy_ne_boundary2 : y ≠ T.boundary 2)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod := by
  let e : Fin 3 -> Fin 3 := fin3Order 0 2 1
  have he : Function.Injective e :=
    fin3Order_injective (by decide) (by decide) (by decide)
  let Tre := T.reindex e he
  have hxre : x ∈ (Tre.leg 2).support := by
    simpa [Tre, reindex, e, fin3Order] using hx
  have hb0 : Tre.boundary 0 ∈ S.boundarySet := by
    simpa [Tre, reindex, e, fin3Order] using hboundary0
  have hb1 : Tre.boundary 1 ∈ S.boundarySet := by
    simpa [Tre, reindex, e, fin3Order] using hboundary2
  have hy_ne0 : y ≠ Tre.boundary 0 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary0
  have hy_ne1 : y ≠ Tre.boundary 1 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary2
  have hq_clean_re :
      forall z : V, z ∈ q.support -> z ∈ Tre.vertexSet -> z = x := by
    intro z hzq hzTre
    exact hq_clean z hzq (T.reindex_vertexSet_subset e he hzTre)
  exact Tre.liftReplaceBoundaryTwoOnLegWithTail hgraph hxre
    hb0 hb1 hy_boundary hy_ne0 hy_ne1 q hq_path hq_clean_re

/-- Replace an arbitrary tripod boundary vertex along its leg.  The numbered
constructions remain available for compatibility; this invariant interface
prevents clients from repeating the same `Fin 3` case split. -/
def liftReplaceBoundaryOnLegWithTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i : Fin 3} {x y : V}
    (hx : x ∈ (T.leg i).support)
    (hboundary : ∀ j : Fin 3, j ≠ i → T.boundary j ∈ S.boundarySet)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary : ∀ j : Fin 3, j ≠ i → y ≠ T.boundary j)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      ∀ z : V, z ∈ q.support → z ∈ T.vertexSet → z = x) :
    S.Tripod := by
  revert hx hboundary hy_ne_boundary
  refine Fin.cases ?_ (fun i => ?_) i
  · intro hx hboundary hy_ne_boundary
    exact T.liftReplaceBoundaryZeroOnLegWithTail hgraph hx
      (hboundary 1 (by decide)) (hboundary 2 (by decide)) hy_boundary
      (hy_ne_boundary 1 (by decide)) (hy_ne_boundary 2 (by decide))
      q hq_path hq_clean
  · refine Fin.cases ?_ (fun i => ?_) i
    · intro hx hboundary hy_ne_boundary
      exact T.liftReplaceBoundaryOneOnLegWithTail hgraph hx
        (hboundary 0 (by decide)) (hboundary 2 (by decide)) hy_boundary
        (hy_ne_boundary 0 (by decide)) (hy_ne_boundary 2 (by decide))
        q hq_path hq_clean
    · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
      intro hx hboundary hy_ne_boundary
      exact T.liftReplaceBoundaryTwoOnLegWithTail hgraph hx
        (hboundary 0 (by decide)) (hboundary 1 (by decide)) hy_boundary
        (hy_ne_boundary 0 (by decide)) (hy_ne_boundary 1 (by decide))
        q hq_path hq_clean

def liftReplaceBoundaryTwoOnRimWithTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {x y : V}
    (hx : x ∈ Walk.InternalVertices (T.rim 2))
    (hboundary0 : T.boundary 0 ∈ S.boundarySet)
    (hboundary1 : T.boundary 1 ∈ S.boundarySet)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary0 : y ≠ T.boundary 0)
    (hy_ne_boundary1 : y ≠ T.boundary 1)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod := by
  have hx_not_leg0 : x ∉ (T.leg 0).support := by
    intro hx0
    have hx_attach0 : x = T.attach 0 :=
      T.legs_meet_rims_only_at_attach 0 2 x hx0 hx.1
    have hx_rim0 : x ∈ Walk.InternalVertices (T.rim 0) := by
      simpa [hx_attach0] using T.attach_mem_rim 0
    exact Set.disjoint_left.mp (T.rim_internals_disjoint 0 2 (by decide))
      hx_rim0 hx
  have hx_not_leg1 : x ∉ (T.leg 1).support := by
    intro hx1
    have hx_attach1 : x = T.attach 1 :=
      T.legs_meet_rims_only_at_attach 1 2 x hx1 hx.1
    have hx_rim1 : x ∈ Walk.InternalVertices (T.rim 1) := by
      simpa [hx_attach1] using T.attach_mem_rim 1
    exact Set.disjoint_left.mp (T.rim_internals_disjoint 1 2 (by decide))
      hx_rim1 hx
  refine {
    left := T.left
    right := T.right
    left_ne_right := T.left_ne_right
    rim := fun i => (T.rim i).mapLe hgraph
    rim_isPath := by
      intro i
      exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.rim_isPath i)
    attach := fun i : Fin 3 => if i = 2 then x else T.attach i
    attach_mem_rim := ?_
    boundary := fun i : Fin 3 => if i = 2 then y else T.boundary i
    boundary_mem := ?_
    boundary_injective := ?_
    leg := ?_
    leg_isPath := ?_
    rim_internals_disjoint := ?_
    legs_pairwise_disjoint := ?_
    legs_meet_rims_only_at_attach := ?_
  }
  · intro i
    fin_cases i
    · simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support] using
        T.attach_mem_rim 0
    · simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support] using
        T.attach_mem_rim 1
    · simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support] using hx
  · intro i
    fin_cases i
    · simpa using hboundary0
    · simpa using hboundary1
    · simpa using hy_boundary
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp at hij ⊢
    · have h := T.boundary_injective hij
      simp at h
    · exact hy_ne_boundary0 hij.symm
    · have h := T.boundary_injective hij
      simp at h
    · exact hy_ne_boundary1 hij.symm
    · exact hy_ne_boundary0 hij
    · exact hy_ne_boundary1 hij
  · exact fun
      | 0 => by simpa using (T.leg 0).mapLe hgraph
      | 1 => by simpa using (T.leg 1).mapLe hgraph
      | 2 => by simpa using q
  · intro i
    fin_cases i
    · exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 0)
    · exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 1)
    · simpa using hq_path
  · intro i j hij
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.rim_internals_disjoint i j hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
        T.legs_pairwise_disjoint 0 1 (by decide)
    ·
      rw [Set.disjoint_left]
      intro z hz0 hzq
      have hz0old : z ∈ (T.leg 0).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hz0
      have hz_eq_x : z = x :=
        hq_clean z hzq (T.leg_mem_vertexSet (i := 0) hz0old)
      exact hx_not_leg0 (by simpa [hz_eq_x] using hz0old)
    · simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
        T.legs_pairwise_disjoint 1 0 (by decide)
    · exact False.elim (hij rfl)
    ·
      rw [Set.disjoint_left]
      intro z hz1 hzq
      have hz1old : z ∈ (T.leg 1).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hz1
      have hz_eq_x : z = x :=
        hq_clean z hzq (T.leg_mem_vertexSet (i := 1) hz1old)
      exact hx_not_leg1 (by simpa [hz_eq_x] using hz1old)
    ·
      rw [Set.disjoint_left]
      intro z hzq hz0
      have hz0old : z ∈ (T.leg 0).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hz0
      have hz_eq_x : z = x :=
        hq_clean z hzq (T.leg_mem_vertexSet (i := 0) hz0old)
      exact hx_not_leg0 (by simpa [hz_eq_x] using hz0old)
    ·
      rw [Set.disjoint_left]
      intro z hzq hz1
      have hz1old : z ∈ (T.leg 1).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hz1
      have hz_eq_x : z = x :=
        hq_clean z hzq (T.leg_mem_vertexSet (i := 1) hz1old)
      exact hx_not_leg1 (by simpa [hz_eq_x] using hz1old)
    · exact False.elim (hij rfl)
  · intro i j z hzleg hzr
    fin_cases i
    ·
      exact T.legs_meet_rims_only_at_attach 0 j z
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzleg)
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzr)
    ·
      exact T.legs_meet_rims_only_at_attach 1 j z
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzleg)
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzr)
    ·
      have hzRimOld : z ∈ (T.rim j).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzr
      have hz_eq_x : z = x :=
        hq_clean z (by simpa using hzleg)
          (T.rim_mem_vertexSet (i := j) hzRimOld)
      simp [hz_eq_x]

def liftReplaceBoundaryZeroOnRimWithTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {x y : V}
    (hx : x ∈ Walk.InternalVertices (T.rim 0))
    (hboundary1 : T.boundary 1 ∈ S.boundarySet)
    (hboundary2 : T.boundary 2 ∈ S.boundarySet)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary1 : y ≠ T.boundary 1)
    (hy_ne_boundary2 : y ≠ T.boundary 2)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod := by
  let e : Fin 3 -> Fin 3 := fin3Order 1 2 0
  have he : Function.Injective e :=
    fin3Order_injective (by decide) (by decide) (by decide)
  let Tre := T.reindex e he
  have hxre : x ∈ Walk.InternalVertices (Tre.rim 2) := by
    simpa [Tre, reindex, e, fin3Order] using hx
  have hb0 : Tre.boundary 0 ∈ S.boundarySet := by
    simpa [Tre, reindex, e, fin3Order] using hboundary1
  have hb1 : Tre.boundary 1 ∈ S.boundarySet := by
    simpa [Tre, reindex, e, fin3Order] using hboundary2
  have hy_ne0 : y ≠ Tre.boundary 0 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary1
  have hy_ne1 : y ≠ Tre.boundary 1 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary2
  have hq_clean_re :
      forall z : V, z ∈ q.support -> z ∈ Tre.vertexSet -> z = x := by
    intro z hzq hzTre
    exact hq_clean z hzq (T.reindex_vertexSet_subset e he hzTre)
  exact Tre.liftReplaceBoundaryTwoOnRimWithTail hgraph hxre
    hb0 hb1 hy_boundary hy_ne0 hy_ne1 q hq_path hq_clean_re

def liftReplaceBoundaryOneOnRimWithTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {x y : V}
    (hx : x ∈ Walk.InternalVertices (T.rim 1))
    (hboundary0 : T.boundary 0 ∈ S.boundarySet)
    (hboundary2 : T.boundary 2 ∈ S.boundarySet)
    (hy_boundary : y ∈ S.boundarySet)
    (hy_ne_boundary0 : y ≠ T.boundary 0)
    (hy_ne_boundary2 : y ≠ T.boundary 2)
    (q : S.graph.Walk x y)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    S.Tripod := by
  let e : Fin 3 -> Fin 3 := fin3Order 0 2 1
  have he : Function.Injective e :=
    fin3Order_injective (by decide) (by decide) (by decide)
  let Tre := T.reindex e he
  have hxre : x ∈ Walk.InternalVertices (Tre.rim 2) := by
    simpa [Tre, reindex, e, fin3Order] using hx
  have hb0 : Tre.boundary 0 ∈ S.boundarySet := by
    simpa [Tre, reindex, e, fin3Order] using hboundary0
  have hb1 : Tre.boundary 1 ∈ S.boundarySet := by
    simpa [Tre, reindex, e, fin3Order] using hboundary2
  have hy_ne0 : y ≠ Tre.boundary 0 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary0
  have hy_ne1 : y ≠ Tre.boundary 1 := by
    simpa [Tre, reindex, e, fin3Order] using hy_ne_boundary2
  have hq_clean_re :
      forall z : V, z ∈ q.support -> z ∈ Tre.vertexSet -> z = x := by
    intro z hzq hzTre
    exact hq_clean z hzq (T.reindex_vertexSet_subset e he hzTre)
  exact Tre.liftReplaceBoundaryTwoOnRimWithTail hgraph hxre
    hb0 hb1 hy_boundary hy_ne0 hy_ne1 q hq_path hq_clean_re


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
