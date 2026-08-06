import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.TripodLegNormalization

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Boundary-clean tripod, in the sense used implicitly in the source proof.

The raw `Tripod` structure only records the three boundary feet.  In the
GM IX `(2.4)` side-tripod paragraph, however, a contact with the cut path is
treated as a contact with one of those feet; this requires excluding hidden
boundary contacts from the common rim endpoints and from the interiors of the
rims and legs. -/
def BoundaryClean {S : GeneralSociety V} (T : S.Tripod) : Prop :=
  T.left ∉ S.boundarySet ∧
    T.right ∉ S.boundarySet ∧
      (forall i : Fin 3,
        Disjoint (Walk.InternalVertices (T.rim i)) S.boundarySet) ∧
        forall i : Fin 3,
          Disjoint (Walk.InternalVertices (T.leg i)) S.boundarySet

theorem boundaryClean_legBoundaryClean {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.BoundaryClean) :
    T.LegBoundaryClean :=
  hclean.2.2.2

theorem cast_boundaryClean {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) (hclean : X.BoundaryClean) :
    (h ▸ X : T.Tripod).BoundaryClean := by
  cases h
  exact hclean

theorem boundaryClean_vertexSet_boundary_eq_boundary
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.BoundaryClean)
    {z : V}
    (hzBoundary : z ∈ S.boundarySet)
    (hzT : z ∈ T.vertexSet) :
    Exists fun i : Fin 3 => z = T.boundary i := by
  rcases hzT with hzRim | hzLeg
  · rcases hzRim with ⟨i, hzRim⟩
    rcases
        Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
          (p := T.rim i) hzRim with
      hzInternal | hzEnd
    · exact False.elim
        (Set.disjoint_left.mp (hclean.2.2.1 i) hzInternal hzBoundary)
    · rcases hzEnd with hzLeft | hzRight
      · exact False.elim (hclean.1 (by simpa [hzLeft] using hzBoundary))
      · exact False.elim
          (hclean.2.1 (by simpa [hzRight] using hzBoundary))
  · rcases hzLeg with ⟨i, hzLeg⟩
    rcases
        Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
          (p := T.leg i) hzLeg with
      hzInternal | hzEnd
    · exact False.elim
        (Set.disjoint_left.mp (hclean.2.2.2 i) hzInternal hzBoundary)
    · rcases hzEnd with hzAttach | hzBoundaryFoot
      · have hzRimInternal :
            z ∈ Walk.InternalVertices (T.rim i) := by
          simpa [hzAttach] using T.attach_mem_rim i
        exact False.elim
          (Set.disjoint_left.mp (hclean.2.2.1 i)
            hzRimInternal hzBoundary)
      · exact ⟨i, hzBoundaryFoot⟩

theorem boundary_not_mem_leg_of_ne {S : GeneralSociety V} (T : S.Tripod)
    {i j : Fin 3} (hij : i ≠ j) :
    T.boundary j ∉ (T.leg i).support := by
  intro hmem
  exact
    Set.disjoint_left.mp (T.legs_pairwise_disjoint i j hij)
      hmem (T.leg j).end_mem_support

def legSuffixFromHit {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod)
    {i : Fin 3} {x : V}
    (hx : x ∈ (T.leg i).support) :
    S.graph.Walk x (T.boundary i) :=
  (T.leg i).dropUntil x hx

theorem legSuffixFromHit_isPath {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod)
    {i : Fin 3} {x : V}
    (hx : x ∈ (T.leg i).support) :
    (T.legSuffixFromHit hx).IsPath := by
  exact (T.leg_isPath i).dropUntil hx

theorem legSuffixFromHit_support_subset {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod)
    {i : Fin 3} {x z : V}
    (hx : x ∈ (T.leg i).support)
    (hz : z ∈ (T.legSuffixFromHit hx).support) :
    z ∈ (T.leg i).support := by
  exact SimpleGraph.Walk.support_dropUntil_subset (T.leg i) hx hz

theorem leg_takeUntil_support_disjoint_legSuffixFromHit_of_idx_lt
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod)
    {i : Fin 3} {x y : V}
    (hx : x ∈ (T.leg i).support)
    (hy : y ∈ (T.leg i).support)
    (hidx : (T.leg i).support.idxOf x < (T.leg i).support.idxOf y) :
    Disjoint
      {z : V | z ∈ ((T.leg i).takeUntil x hx).support}
      {z : V | z ∈ (T.legSuffixFromHit hy).support} := by
  simpa [Tripod.legSuffixFromHit] using
    Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
      (T.leg_isPath i) hx hy hidx

theorem leg_takeUntil_support_disjoint_legSuffixFromHit_of_supportIndex_lt
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod)
    {i : Fin 3} {x y : V}
    (hx : x ∈ (T.leg i).support)
    (hy : y ∈ (T.leg i).support)
    (hidx :
      Walk.supportIndex (T.leg i) x < Walk.supportIndex (T.leg i) y) :
    Disjoint
      {z : V | z ∈ ((T.leg i).takeUntil x hx).support}
      {z : V | z ∈ (T.legSuffixFromHit hy).support} :=
  T.leg_takeUntil_support_disjoint_legSuffixFromHit_of_idx_lt
    hx hy (by simpa [Walk.supportIndex] using hidx)

theorem leg_later_not_mem_takeUntil_of_supportIndex_lt
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod)
    {i : Fin 3} {x y : V}
    (hx : x ∈ (T.leg i).support)
    (hidx :
      Walk.supportIndex (T.leg i) x < Walk.supportIndex (T.leg i) y) :
    y ∉ ((T.leg i).takeUntil x hx).support :=
  Walk.not_mem_takeUntil_of_idxOf_lt
    hx (by simpa [Walk.supportIndex] using hidx)

theorem leg_earlier_not_mem_legSuffixFromHit_of_supportIndex_lt
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod)
    {i : Fin 3} {x y : V}
    (hy : y ∈ (T.leg i).support)
    (hidx :
      Walk.supportIndex (T.leg i) x < Walk.supportIndex (T.leg i) y) :
    x ∉ (T.legSuffixFromHit hy).support := by
  simpa [Tripod.legSuffixFromHit] using
    Walk.IsPath.earlier_not_mem_dropUntil_of_idx_lt
      (T.leg_isPath i) hy (by simpa [Walk.supportIndex] using hidx)

theorem boundary_eq_attach_of_mem_rim {S : GeneralSociety V}
    (T : S.Tripod)
    {i j : Fin 3}
    (hboundary_rim : T.boundary i ∈ (T.rim j).support) :
    T.boundary i = T.attach i :=
  T.legs_meet_rims_only_at_attach i j (T.boundary i)
    (T.leg i).end_mem_support hboundary_rim

theorem boundary_not_mem_rim_of_ne_attach {S : GeneralSociety V}
    (T : S.Tripod)
    {i j : Fin 3}
    (hboundary_ne_attach : T.boundary i ≠ T.attach i) :
    T.boundary i ∉ (T.rim j).support := by
  intro hboundary_rim
  exact hboundary_ne_attach (T.boundary_eq_attach_of_mem_rim hboundary_rim)

theorem boundary_ne_attach_of_leg_hit_ne_boundary
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i : Fin 3} {x : V}
    (hx : x ∈ (T.leg i).support)
    (hx_ne_boundary : x ≠ T.boundary i) :
    T.boundary i ≠ T.attach i := by
  intro hboundary_attach
  have hx_eq_attach : x = T.attach i := by
    let q : S.graph.Walk (T.attach i) (T.attach i) :=
      (T.leg i).copy rfl hboundary_attach
    have hq_path : q.IsPath := by
      simpa [q] using
        (SimpleGraph.Walk.isPath_copy (T.leg i) rfl
          hboundary_attach).mpr (T.leg_isPath i)
    have hxq : x ∈ q.support := by
      simpa [q] using hx
    exact Walk.IsPath.mem_support_eq_of_closed hq_path hxq
  exact hx_ne_boundary (by rw [hx_eq_attach, hboundary_attach])

/-- A boundary foot coincides with its attachment exactly when the
corresponding tripod leg is trivial.

This packages the degenerate side-tripod case left by the GM IX `(2.4)`
common-end analysis: after `Tripod.boundary_mem_rim_eq_attach` normalizes a
rim contact to `boundary = attach`, the leg contributes no additional
vertices. -/
theorem boundary_eq_attach_iff_leg_nil
    {S : GeneralSociety V}
    (T : S.Tripod) (i : Fin 3) :
    T.boundary i = T.attach i ↔ (T.leg i).Nil := by
  constructor
  · intro hboundary_attach
    let q : S.graph.Walk (T.attach i) (T.attach i) :=
      (T.leg i).copy rfl hboundary_attach
    have hq_path : q.IsPath := by
      simpa [q] using
        (SimpleGraph.Walk.isPath_copy (T.leg i) rfl
          hboundary_attach).mpr (T.leg_isPath i)
    have hq_nil : q.Nil := by
      have hq_eq : q = SimpleGraph.Walk.nil :=
        (SimpleGraph.Walk.isPath_iff_eq_nil q).mp hq_path
      rw [hq_eq]
      exact SimpleGraph.Walk.Nil.nil
    simpa [q] using hq_nil
  · intro hnil
    exact (SimpleGraph.Walk.Nil.eq hnil).symm

theorem leg_nil_iff_boundary_eq_attach
    {S : GeneralSociety V}
    (T : S.Tripod) (i : Fin 3) :
    (T.leg i).Nil ↔ T.boundary i = T.attach i :=
  (T.boundary_eq_attach_iff_leg_nil i).symm

/-- A nontrivial tripod leg separates its boundary foot from its rim
attachment. -/
theorem boundary_ne_attach_of_no_leg_nil
    {S : GeneralSociety V}
    (T : S.Tripod)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil)
    (i : Fin 3) :
    T.boundary i ≠ T.attach i := by
  intro hboundary_attach
  exact hleg_not_nil i ((T.boundary_eq_attach_iff_leg_nil i).mp hboundary_attach)

/-- A nontrivial tripod leg keeps its boundary foot off every rim. -/
theorem boundary_not_mem_rim_of_no_leg_nil
    {S : GeneralSociety V}
    (T : S.Tripod)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil)
    (i j : Fin 3) :
    T.boundary i ∉ (T.rim j).support :=
  T.boundary_not_mem_rim_of_ne_attach
    (T.boundary_ne_attach_of_no_leg_nil hleg_not_nil i)

/-- A nontrivial branch leg keeps its own boundary foot off its own rim. -/
theorem boundary_not_mem_own_rim_of_leg_not_nil
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i : Fin 3}
    (hleg_not_nil : Not (T.leg i).Nil) :
    T.boundary i ∉ (T.rim i).support :=
  T.boundary_not_mem_rim_of_ne_attach
    (by
      intro hboundary_attach
      exact hleg_not_nil
        ((T.boundary_eq_attach_iff_leg_nil i).mp hboundary_attach))

theorem boundary_not_mem_rim_of_leg_hit_ne_boundary
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i j : Fin 3} {x : V}
    (hx : x ∈ (T.leg i).support)
    (hx_ne_boundary : x ≠ T.boundary i) :
    T.boundary i ∉ (T.rim j).support :=
  T.boundary_not_mem_rim_of_ne_attach
    (T.boundary_ne_attach_of_leg_hit_ne_boundary hx hx_ne_boundary)

theorem boundary_not_mem_leg_takeUntil_of_hit_ne_boundary
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod)
    {i : Fin 3} {x : V}
    (hx : x ∈ (T.leg i).support)
    (hx_ne_boundary : x ≠ T.boundary i) :
    T.boundary i ∉ ((T.leg i).takeUntil x hx).support :=
  SimpleGraph.Walk.endpoint_notMem_support_takeUntil
    (T.leg_isPath i) hx (by simpa [ne_eq] using hx_ne_boundary.symm)

theorem left_not_mem_leg {S : GeneralSociety V} (T : S.Tripod)
    (i : Fin 3) :
    T.left ∉ (T.leg i).support := by
  intro hleft_leg
  have hleft_rim : T.left ∈ (T.rim i).support :=
    (T.rim i).start_mem_support
  have hattach :
      T.left = T.attach i :=
    T.legs_meet_rims_only_at_attach i i T.left hleft_leg hleft_rim
  exact (T.attach_mem_rim i).2.1 hattach.symm

theorem right_not_mem_leg {S : GeneralSociety V} (T : S.Tripod)
    (i : Fin 3) :
    T.right ∉ (T.leg i).support := by
  intro hright_leg
  have hright_rim : T.right ∈ (T.rim i).support :=
    (T.rim i).end_mem_support
  have hattach :
      T.right = T.attach i :=
    T.legs_meet_rims_only_at_attach i i T.right hright_leg hright_rim
  exact (T.attach_mem_rim i).2.2 hattach.symm

theorem left_ne_boundary {S : GeneralSociety V} (T : S.Tripod)
    (i : Fin 3) :
    T.left ≠ T.boundary i := by
  intro h
  exact T.left_not_mem_leg i (by simp [h])

theorem right_ne_boundary {S : GeneralSociety V} (T : S.Tripod)
    (i : Fin 3) :
    T.right ≠ T.boundary i := by
  intro h
  exact T.right_not_mem_leg i (by simp [h])

theorem clean_tail_from_left_endpoint_mem_vertexSet_eq
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.left y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left)
    (hyT : y ∈ T.vertexSet) :
    y = T.left :=
  hq_clean y q.end_mem_support hyT

theorem clean_tail_from_right_endpoint_mem_vertexSet_eq
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.right y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.right)
    (hyT : y ∈ T.vertexSet) :
    y = T.right :=
  hq_clean y q.end_mem_support hyT

theorem clean_tail_from_left_not_right_end
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.left y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left) :
    T.right ≠ y := by
  intro hright_y
  have hyT : y ∈ T.vertexSet := by
    rw [← hright_y]
    exact T.right_mem_vertexSet
  have hy_eq_left : y = T.left :=
    T.clean_tail_from_left_endpoint_mem_vertexSet_eq q hq_clean hyT
  exact T.left_ne_right (hy_eq_left.symm.trans hright_y.symm)

theorem clean_tail_from_right_not_left_end
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.right y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.right) :
    T.left ≠ y := by
  intro hleft_y
  have hyT : y ∈ T.vertexSet := by
    rw [← hleft_y]
    exact T.left_mem_vertexSet
  have hy_eq_right : y = T.right :=
    T.clean_tail_from_right_endpoint_mem_vertexSet_eq q hq_clean hyT
  exact T.left_ne_right (hleft_y.trans hy_eq_right)

theorem clean_tail_from_left_not_boundary
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.left y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left) :
    forall i : Fin 3, y ≠ T.boundary i := by
  intro i hy
  have hyT : y ∈ T.vertexSet := by
    simpa [hy] using T.boundary_mem_vertexSet i
  have hy_eq_left : y = T.left :=
    T.clean_tail_from_left_endpoint_mem_vertexSet_eq q hq_clean hyT
  exact T.left_not_mem_leg i (by
    simp [hy_eq_left.symm.trans hy])

theorem clean_tail_from_right_not_boundary
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.right y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.right) :
    forall i : Fin 3, y ≠ T.boundary i := by
  intro i hy
  have hyT : y ∈ T.vertexSet := by
    simpa [hy] using T.boundary_mem_vertexSet i
  have hy_eq_right : y = T.right :=
    T.clean_tail_from_right_endpoint_mem_vertexSet_eq q hq_clean hyT
  exact T.right_not_mem_leg i (by
    simp [hy_eq_right.symm.trans hy])

theorem clean_tail_from_left_not_attach
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.left y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left) :
    forall i : Fin 3, y ≠ T.attach i := by
  intro i hy
  have hyT : y ∈ T.vertexSet := by
    simpa [hy] using T.attach_mem_vertexSet i
  have hy_eq_left : y = T.left :=
    T.clean_tail_from_left_endpoint_mem_vertexSet_eq q hq_clean hyT
  exact (T.attach_mem_rim i).2.1 (hy.symm.trans hy_eq_left)

theorem clean_tail_from_right_not_attach
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.right y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.right) :
    forall i : Fin 3, y ≠ T.attach i := by
  intro i hy
  have hyT : y ∈ T.vertexSet := by
    simpa [hy] using T.attach_mem_vertexSet i
  have hy_eq_right : y = T.right :=
    T.clean_tail_from_right_endpoint_mem_vertexSet_eq q hq_clean hyT
  exact (T.attach_mem_rim i).2.2 (hy.symm.trans hy_eq_right)

theorem clean_tail_from_left_support_not_right
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.left y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left) :
    T.right ∉ q.support := by
  intro hright
  have hright_left : T.right = T.left :=
    hq_clean T.right hright T.right_mem_vertexSet
  exact T.left_ne_right hright_left.symm

theorem clean_tail_from_right_support_not_left
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.right y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.right) :
    T.left ∉ q.support := by
  intro hleft
  have hleft_right : T.left = T.right :=
    hq_clean T.left hleft T.left_mem_vertexSet
  exact T.left_ne_right hleft_right

theorem clean_tail_from_left_support_not_boundary
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.left y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left) :
    forall i : Fin 3, T.boundary i ∉ q.support := by
  intro i hboundary
  have hboundary_left : T.boundary i = T.left :=
    hq_clean (T.boundary i) hboundary (T.boundary_mem_vertexSet i)
  exact T.left_not_mem_leg i (by
    simpa [hboundary_left] using (T.leg i).end_mem_support)

theorem clean_tail_from_right_support_not_boundary
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.right y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.right) :
    forall i : Fin 3, T.boundary i ∉ q.support := by
  intro i hboundary
  have hboundary_right : T.boundary i = T.right :=
    hq_clean (T.boundary i) hboundary (T.boundary_mem_vertexSet i)
  exact T.right_not_mem_leg i (by
    simpa [hboundary_right] using (T.leg i).end_mem_support)

theorem clean_tail_from_left_support_not_attach
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.left y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left) :
    forall i : Fin 3, T.attach i ∉ q.support := by
  intro i hattach
  have hattach_left : T.attach i = T.left :=
    hq_clean (T.attach i) hattach (T.attach_mem_vertexSet i)
  exact (T.attach_mem_rim i).2.1 hattach_left

theorem clean_tail_from_right_support_not_attach
    {S : GeneralSociety V} {G : SimpleGraph V} (T : S.Tripod) {y : V}
    (q : G.Walk T.right y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.right) :
    forall i : Fin 3, T.attach i ∉ q.support := by
  intro i hattach
  have hattach_right : T.attach i = T.right :=
    hq_clean (T.attach i) hattach (T.attach_mem_vertexSet i)
  exact (T.attach_mem_rim i).2.2 hattach_right

theorem clean_tail_from_leg_hit_left_not_end {S : GeneralSociety V}
    (T : S.Tripod) {i : Fin 3} {x y : V}
    (hx : x ∈ (T.leg i).support)
    (q : S.graph.Walk x y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    T.left ≠ y := by
  intro hleft_y
  have hyT : y ∈ T.vertexSet := by
    rw [← hleft_y]
    exact T.left_mem_vertexSet
  have hy_eq_x : y = x :=
    hq_clean y q.end_mem_support hyT
  have hx_left : x = T.left := hy_eq_x.symm.trans hleft_y.symm
  have hx_rim : x ∈ (T.rim i).support := by
    rw [hx_left]
    exact (T.rim i).start_mem_support
  have hx_attach : x = T.attach i :=
    T.legs_meet_rims_only_at_attach i i x hx hx_rim
  exact (T.attach_mem_rim i).2.1 (hx_attach.symm.trans hx_left)

theorem clean_tail_from_leg_hit_right_not_end {S : GeneralSociety V}
    (T : S.Tripod) {i : Fin 3} {x y : V}
    (hx : x ∈ (T.leg i).support)
    (q : S.graph.Walk x y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    T.right ≠ y := by
  intro hright_y
  have hyT : y ∈ T.vertexSet := by
    rw [← hright_y]
    exact T.right_mem_vertexSet
  have hy_eq_x : y = x :=
    hq_clean y q.end_mem_support hyT
  have hx_right : x = T.right := hy_eq_x.symm.trans hright_y.symm
  have hx_rim : x ∈ (T.rim i).support := by
    rw [hx_right]
    exact (T.rim i).end_mem_support
  have hx_attach : x = T.attach i :=
    T.legs_meet_rims_only_at_attach i i x hx hx_rim
  exact (T.attach_mem_rim i).2.2 (hx_attach.symm.trans hx_right)

theorem clean_tail_from_leg_hit_ne_other_boundary {S : GeneralSociety V}
    {G : SimpleGraph V}
    (T : S.Tripod) {x y : V} {i j : Fin 3}
    (hij : i ≠ j)
    (hx : x ∈ (T.leg i).support)
    (q : G.Walk x y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    y ≠ T.boundary j := by
  intro hy
  have hy_vertex : y ∈ T.vertexSet := by
    simpa [hy] using T.boundary_mem_vertexSet j
  have hyx : y = x := hq_clean y q.end_mem_support hy_vertex
  have hx_boundary : x = T.boundary j := hyx.symm.trans hy
  have hboundary_leg_i : T.boundary j ∈ (T.leg i).support := by
    simpa [hx_boundary] using hx
  exact
    Set.disjoint_left.mp (T.legs_pairwise_disjoint i j hij)
      hboundary_leg_i (T.leg j).end_mem_support

theorem rim_support_internal_or_endpoint {S : GeneralSociety V}
    (T : S.Tripod) {i : Fin 3} {v : V}
    (hv : v ∈ (T.rim i).support) :
    v ∈ Walk.InternalVertices (T.rim i) ∨ v = T.left ∨ v = T.right := by
  simpa using
    Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
      (p := T.rim i) hv

/-- A non-endpoint vertex in a tripod rim support is internal to that rim. -/
theorem rim_support_internal_of_not_endpoint {S : GeneralSociety V}
    (T : S.Tripod) {i : Fin 3} {v : V}
    (hv : v ∈ (T.rim i).support)
    (hne : v ≠ T.left ∧ v ≠ T.right) :
    v ∈ Walk.InternalVertices (T.rim i) := by
  rcases T.rim_support_internal_or_endpoint hv with hint | hleft | hright
  · exact hint
  · exact False.elim (hne.1 hleft)
  · exact False.elim (hne.2 hright)

/-- If a boundary foot of a tripod lies on any rim, it must coincide with its
own attachment.

This is the precise structural content behind the remaining "degenerate
non-median rim" residual in the GM IX `(2.4)` side-tripod proof. -/
theorem boundary_mem_rim_eq_attach {S : GeneralSociety V}
    (T : S.Tripod) {i s : Fin 3}
    (hmem : T.boundary i ∈ (T.rim s).support) :
    T.boundary i = T.attach i :=
  T.legs_meet_rims_only_at_attach i s (T.boundary i)
    (T.leg i).end_mem_support hmem

/-- A boundary foot of a tripod can lie only on its own rim, and then only at
its attachment.

The theorem is stated as an equality of indices because later residual
arguments need to collapse an existential rim witness to the matching branch
before doing the ordered side-tripod case split. -/
theorem boundary_mem_rim_index_eq {S : GeneralSociety V}
    (T : S.Tripod) {i s : Fin 3}
    (hmem : T.boundary i ∈ (T.rim s).support) :
    s = i := by
  classical
  by_contra hne
  have hattach : T.boundary i = T.attach i :=
    T.boundary_mem_rim_eq_attach hmem
  have hi_internal :
      T.boundary i ∈ Walk.InternalVertices (T.rim i) := by
    simpa [hattach] using T.attach_mem_rim i
  have hs_internal :
      T.boundary i ∈ Walk.InternalVertices (T.rim s) := by
    rcases T.rim_support_internal_or_endpoint hmem with hs | hend
    · exact hs
    · rcases hend with hleft | hright
      · have hattach_left : T.attach i = T.left := hattach.symm.trans hleft
        exact False.elim ((T.attach_mem_rim i).2.1 hattach_left)
      · have hattach_right : T.attach i = T.right := hattach.symm.trans hright
        exact False.elim ((T.attach_mem_rim i).2.2 hattach_right)
  exact
    Set.disjoint_left.mp
      (T.rim_internals_disjoint i s (fun h => hne h.symm))
      hi_internal hs_internal

/-- A boundary foot of one branch cannot lie on a different rim. -/
theorem boundary_not_mem_rim_of_ne_index {S : GeneralSociety V}
    (T : S.Tripod) {i s : Fin 3} (his : i ≠ s) :
    T.boundary i ∉ (T.rim s).support := by
  intro hmem
  exact his ((T.boundary_mem_rim_index_eq hmem).symm)

end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
