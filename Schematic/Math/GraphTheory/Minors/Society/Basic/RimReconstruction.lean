import Schematic.Math.GraphTheory.Minors.Society.Basic.RimOrientation

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- The ambient path obtained by following the old left arm to a hit `x` and
then taking a clean tail to `a`. -/
def leftArmPrefixTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i : Fin 3} {x a : V}
    (hx : x ∈ (T.leftToAttach i).support)
    (q : S.graph.Walk x a) :
    S.graph.Walk T.left a :=
  (((T.leftToAttach i).takeUntil x hx).mapLe hgraph).append q

/-- The ambient path obtained by following the old right arm to a hit `x` and
then taking a clean tail to `a`. -/
def rightArmPrefixTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i : Fin 3} {x a : V}
    (hx : x ∈ (T.rightToAttach i).support)
    (q : S.graph.Walk x a) :
    S.graph.Walk T.right a :=
  (((T.rightToAttach i).takeUntil x hx).mapLe hgraph).append q

theorem leftArmPrefixTail_isPath {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i : Fin 3} {x a : V}
    (hx : x ∈ (T.leftToAttach i).support)
    (q : S.graph.Walk x a)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    (T.leftArmPrefixTail hgraph hx q).IsPath := by
  dsimp [Tripod.leftArmPrefixTail]
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    (SimpleGraph.Walk.IsPath.mapLe hgraph
      ((T.leftToAttach_isPath i).takeUntil hx))
    hq_path ?_
  intro z hzPrefix hzq
  have hzOldPrefix :
      z ∈ ((T.leftToAttach i).takeUntil x hx).support := by
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefix
  have hzArm : z ∈ (T.leftToAttach i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hx
      hzOldPrefix
  exact hq_clean z hzq
    (T.rim_mem_vertexSet (i := i)
      (T.leftToAttach_support_subset_rim i hzArm))

theorem rightArmPrefixTail_isPath {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i : Fin 3} {x a : V}
    (hx : x ∈ (T.rightToAttach i).support)
    (q : S.graph.Walk x a)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    (T.rightArmPrefixTail hgraph hx q).IsPath := by
  dsimp [Tripod.rightArmPrefixTail]
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    (SimpleGraph.Walk.IsPath.mapLe hgraph
      ((T.rightToAttach_isPath i).takeUntil hx))
    hq_path ?_
  intro z hzPrefix hzq
  have hzOldPrefix :
      z ∈ ((T.rightToAttach i).takeUntil x hx).support := by
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefix
  have hzArm : z ∈ (T.rightToAttach i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach i) hx
      hzOldPrefix
  exact hq_clean z hzq
    (T.rim_mem_vertexSet (i := i)
      (T.rightToAttach_support_subset_rim i hzArm))

/-- The reusable proof package for a clean tail spliced onto a prefix of a
tripod's left arm. -/
structure LeftArmPrefixTailData
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph)
    {r : Fin 3} {x a : V}
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (q : S.graph.Walk x a) : Prop where
  hit_ne_attach : x ≠ T.attach r
  hit_internal : x ∈ Walk.InternalVertices (T.rim r)
  tail_isPath : q.IsPath
  tail_clean : forall z : V, z ∈ q.support ->
    z ∈ T.vertexSet -> z = x

def LeftArmPrefixTailData.walk
    {S H : GeneralSociety V} [DecidableEq V]
    {T : H.Tripod} {hgraph : H.graph ≤ S.graph}
    {r : Fin 3} {x a : V}
    {hx_arm : x ∈ (T.leftToAttach r).support}
    {q : S.graph.Walk x a}
    (_D : T.LeftArmPrefixTailData hgraph hx_arm q) :
    S.graph.Walk T.left a :=
  T.leftArmPrefixTail hgraph hx_arm q

theorem LeftArmPrefixTailData.walk_isPath
    {S H : GeneralSociety V} [DecidableEq V]
    {T : H.Tripod} {hgraph : H.graph ≤ S.graph}
    {r : Fin 3} {x a : V}
    {hx_arm : x ∈ (T.leftToAttach r).support}
    {q : S.graph.Walk x a}
    (D : T.LeftArmPrefixTailData hgraph hx_arm q) :
    D.walk.IsPath :=
  T.leftArmPrefixTail_isPath hgraph hx_arm q D.tail_isPath D.tail_clean

theorem leftArmPrefixTail_inter_distinct_rim_eq_left_of_clean
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph)
    {r s : Fin 3} (hrs : r ≠ s)
    {x a : V} (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (q : S.graph.Walk x a)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x) :
    forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support ->
      z ∈ (T.rim s).support -> z = T.left := by
  intro z hzTail hzRim
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzTail with
    hzPrefix | hzq
  · apply T.leftToAttach_takeUntil_support_inter_rim_eq_left hrs
    · simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefix
    · exact hzRim
  · have hzx : z = x := hq_clean z hzq (T.rim_mem_vertexSet hzRim)
    have hxRimS : x ∈ (T.rim s).support := by simpa [hzx] using hzRim
    have hxInternalS : x ∈ Walk.InternalVertices (T.rim s) :=
      T.rim_support_internal_of_not_endpoint hxRimS
        ⟨hx_internal.2.1, hx_internal.2.2⟩
    exact False.elim
      (Set.disjoint_left.mp (T.rim_internals_disjoint r s hrs)
        hx_internal hxInternalS)

theorem leftArmPrefixTail_disjoint_attachToRight_of_clean
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph)
    {r s : Fin 3}
    {x a : V} (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (q : S.graph.Walk x a)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x) :
    forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support ->
      z ∈ (T.attachToRight s).support -> False := by
  intro z hzTail hzRight
  by_cases hrs : r = s
  · subst s
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzTail with
      hzPrefix | hzq
    · have hzLeft : z ∈ (T.leftToAttach r).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach r) hx_arm
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefix)
      have hzAttach : z = T.attach r :=
        T.leftToAttach_support_inter_rightToAttach_eq_attach r hzLeft (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzRight)
      exact
        (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.leftToAttach_isPath r) hx_arm hx_ne_attach.symm)
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support,
            hzAttach] using hzPrefix)
    · have hzx : z = x := hq_clean z hzq
          (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim r hzRight))
      exact hx_ne_attach
        (T.leftToAttach_support_inter_rightToAttach_eq_attach r hx_arm (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse, hzx] using hzRight))
  · have hzLeft : z = T.left :=
      T.leftArmPrefixTail_inter_distinct_rim_eq_left_of_clean
        hgraph hrs hx_arm hx_internal q hq_clean z hzTail
        (T.attachToRight_support_subset_rim s hzRight)
    exact T.left_not_mem_attachToRight s (by simpa [hzLeft] using hzRight)

theorem LeftArmPrefixTailData.inter_distinct_rim_eq_left
    {S H : GeneralSociety V} [DecidableEq V]
    {T : H.Tripod} {hgraph : H.graph ≤ S.graph}
    {r s : Fin 3} {x a : V}
    {hx_arm : x ∈ (T.leftToAttach r).support}
    {q : S.graph.Walk x a}
    (D : T.LeftArmPrefixTailData hgraph hx_arm q)
    (hrs : r ≠ s) :
    forall z : V, z ∈ D.walk.support ->
      z ∈ (T.rim s).support -> z = T.left :=
  T.leftArmPrefixTail_inter_distinct_rim_eq_left_of_clean
    hgraph hrs hx_arm D.hit_internal q D.tail_clean

theorem LeftArmPrefixTailData.inter_distinct_leftToAttach_eq_left
    {S H : GeneralSociety V} [DecidableEq V]
    {T : H.Tripod} {hgraph : H.graph ≤ S.graph}
    {r s : Fin 3} {x a : V}
    {hx_arm : x ∈ (T.leftToAttach r).support}
    {q : S.graph.Walk x a}
    (D : T.LeftArmPrefixTailData hgraph hx_arm q)
    (hrs : r ≠ s) :
    forall z : V, z ∈ D.walk.support ->
      z ∈ (T.leftToAttach s).support -> z = T.left := by
  intro z hzTail hzLeft
  exact D.inter_distinct_rim_eq_left hrs z hzTail
    (T.leftToAttach_support_subset_rim s hzLeft)

theorem LeftArmPrefixTailData.disjoint_attachToRight
    {S H : GeneralSociety V} [DecidableEq V]
    {T : H.Tripod} {hgraph : H.graph ≤ S.graph}
    {r : Fin 3} {x a : V}
    {hx_arm : x ∈ (T.leftToAttach r).support}
    {q : S.graph.Walk x a}
    (D : T.LeftArmPrefixTailData hgraph hx_arm q)
    (s : Fin 3) :
    forall z : V, z ∈ D.walk.support ->
      z ∈ (T.attachToRight s).support -> False :=
  T.leftArmPrefixTail_disjoint_attachToRight_of_clean
    hgraph hx_arm D.hit_ne_attach D.hit_internal q D.tail_clean

/-- Rebuilt rim through the old left common end. -/
def attachToAttachViaLeft {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i j : Fin 3) :
    S.graph.Walk (T.attach i) (T.attach j) :=
  (T.attachToLeft i).append (T.leftToAttach j)

/-- Rebuilt rim through the old right common end. -/
def attachToAttachViaRight {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i j : Fin 3) :
    S.graph.Walk (T.attach i) (T.attach j) :=
  (T.attachToRight i).append (T.rightToAttach j)

theorem attachToAttachViaLeft_isPath {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} (hij : i ≠ j) :
    (T.attachToAttachViaLeft i j).IsPath := by
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    (T.attachToLeft_isPath i) (T.leftToAttach_isPath j) ?_
  intro z hzi hzj
  have hziRim : z ∈ (T.rim i).support :=
    T.attachToLeft_support_subset_rim i hzi
  have hzjRim : z ∈ (T.rim j).support :=
    T.leftToAttach_support_subset_rim j hzj
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := T.rim i) hziRim with
    hziInt | hziEnd
  · rcases
        Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
          (p := T.rim j) hzjRim with
      hzjInt | hzjEnd
    · exact False.elim
        (Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
          hziInt hzjInt)
    · rcases hzjEnd with hzLeft | hzRight
      · exact hzLeft
      · exact False.elim (hziInt.2.2 hzRight)
  · rcases hziEnd with hzLeft | hzRight
    · exact hzLeft
    · exact False.elim (T.right_not_mem_attachToLeft i (by simpa [hzRight] using hzi))

theorem attachToAttachViaRight_isPath {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} (hij : i ≠ j) :
    (T.attachToAttachViaRight i j).IsPath := by
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    (T.attachToRight_isPath i) (T.rightToAttach_isPath j) ?_
  intro z hzi hzj
  have hziRim : z ∈ (T.rim i).support :=
    T.attachToRight_support_subset_rim i hzi
  have hzjRim : z ∈ (T.rim j).support :=
    T.rightToAttach_support_subset_rim j hzj
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := T.rim i) hziRim with
    hziInt | hziEnd
  · rcases
        Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
          (p := T.rim j) hzjRim with
      hzjInt | hzjEnd
    · exact False.elim
        (Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
          hziInt hzjInt)
    · rcases hzjEnd with hzLeft | hzRight
      · exact False.elim (hziInt.2.1 hzLeft)
      · exact hzRight
  · rcases hziEnd with hzLeft | hzRight
    · exact False.elim
        (T.left_not_mem_attachToRight i (by simpa [hzLeft] using hzi))
    · exact hzRight

theorem attachToAttachViaLeft_support_cases {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} {z : V}
    (hz : z ∈ (T.attachToAttachViaLeft i j).support) :
    z ∈ (T.rim i).support ∨ z ∈ (T.rim j).support := by
  rw [Tripod.attachToAttachViaLeft,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzi | hzj
  · exact Or.inl (T.attachToLeft_support_subset_rim i hzi)
  · exact Or.inr (T.leftToAttach_support_subset_rim j hzj)

theorem attachToAttachViaRight_support_cases {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} {z : V}
    (hz : z ∈ (T.attachToAttachViaRight i j).support) :
    z ∈ (T.rim i).support ∨ z ∈ (T.rim j).support := by
  rw [Tripod.attachToAttachViaRight,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzi | hzj
  · exact Or.inl (T.attachToRight_support_subset_rim i hzi)
  · exact Or.inr (T.rightToAttach_support_subset_rim j hzj)

theorem attachToAttachViaLeft_support_precise_cases {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} {z : V}
    (hz : z ∈ (T.attachToAttachViaLeft i j).support) :
    z ∈ (T.attachToLeft i).support ∨ z ∈ (T.leftToAttach j).support := by
  simpa [Tripod.attachToAttachViaLeft,
    SimpleGraph.Walk.mem_support_append_iff] using hz

theorem attachToAttachViaRight_support_precise_cases {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} {z : V}
    (hz : z ∈ (T.attachToAttachViaRight i j).support) :
    z ∈ (T.attachToRight i).support ∨ z ∈ (T.rightToAttach j).support := by
  simpa [Tripod.attachToAttachViaRight,
    SimpleGraph.Walk.mem_support_append_iff] using hz

theorem left_mem_internal_attachToAttachViaLeft {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i j : Fin 3) :
    T.left ∈ Walk.InternalVertices (T.attachToAttachViaLeft i j) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Tripod.attachToAttachViaLeft]
  · intro h
    exact (T.attach_mem_rim i).2.1 h.symm
  · intro h
    exact (T.attach_mem_rim j).2.1 h.symm

theorem right_mem_internal_attachToAttachViaRight {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i j : Fin 3) :
    T.right ∈ Walk.InternalVertices (T.attachToAttachViaRight i j) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Tripod.attachToAttachViaRight]
  · intro h
    exact (T.attach_mem_rim i).2.2 h.symm
  · intro h
    exact (T.attach_mem_rim j).2.2 h.symm

/-- Rebuilt rim through two old legs and an ambient middle segment. -/
def liftAttachToAttachViaLegSegment {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (i j : Fin 3)
    (middle : S.graph.Walk (T.boundary i) (T.boundary j)) :
    S.graph.Walk (T.attach i) (T.attach j) :=
  (((T.leg i).mapLe hgraph).append middle).append
    ((T.leg j).mapLe hgraph).reverse

theorem liftAttachToAttachViaLegSegment_isPath
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j : Fin 3} (hij : i ≠ j)
    {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    (hmiddle_path : middle.IsPath)
    (hmiddle_clean :
      forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
        z = T.boundary i ∨ z = T.boundary j) :
    (T.liftAttachToAttachViaLegSegment hgraph i j middle).IsPath := by
  let oldLegI : S.graph.Walk (T.attach i) (T.boundary i) :=
    (T.leg i).mapLe hgraph
  let oldLegJ : S.graph.Walk (T.attach j) (T.boundary j) :=
    (T.leg j).mapLe hgraph
  have hOldI_path : oldLegI.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath i)
  have hOldJ_path : oldLegJ.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath j)
  have hfirst : (oldLegI.append middle).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hOldI_path hmiddle_path ?_
    intro z hzOld hzMid
    have hzOldT : z ∈ (T.leg i).support := by
      simpa [oldLegI, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
    rcases hmiddle_clean z hzMid (T.leg_mem_vertexSet (i := i) hzOldT)
      with hzi | hzj
    · exact hzi
    · exact False.elim
        (T.boundary_not_mem_leg_of_ne hij (by simpa [hzj] using hzOldT))
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    hfirst hOldJ_path.reverse ?_
  intro z hzFirst hzOldJRev
  have hzOldJ : z ∈ (T.leg j).support := by
    have hzOldJMap : z ∈ oldLegJ.support := by
      simpa [oldLegJ, SimpleGraph.Walk.support_reverse] using hzOldJRev
    simpa [oldLegJ, SimpleGraph.Walk.support_mapLe_eq_support] using hzOldJMap
  have hzFirstCases :
      z ∈ oldLegI.support ∨ z ∈ middle.support := by
    simpa [SimpleGraph.Walk.mem_support_append_iff] using hzFirst
  rcases hzFirstCases with hzOldI | hzMid
  · have hzOldIT : z ∈ (T.leg i).support := by
      simpa [oldLegI, SimpleGraph.Walk.support_mapLe_eq_support] using hzOldI
    exact False.elim
      (Set.disjoint_left.mp (T.legs_pairwise_disjoint i j hij)
        hzOldIT hzOldJ)
  · rcases hmiddle_clean z hzMid (T.leg_mem_vertexSet (i := j) hzOldJ)
      with hzi | hzj
    · exact False.elim
        (T.boundary_not_mem_leg_of_ne (i := j) (j := i)
          (fun h => hij h.symm) (by simpa [hzi] using hzOldJ))
    · exact hzj

theorem liftAttachToAttachViaLegSegment_support_cases
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j : Fin 3}
    {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    {z : V}
    (hz :
      z ∈
        (T.liftAttachToAttachViaLegSegment hgraph i j middle).support) :
    z ∈ (T.leg i).support ∨
      z ∈ middle.support ∨ z ∈ (T.leg j).support := by
  rw [Tripod.liftAttachToAttachViaLegSegment,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzFirst | hzLast
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzFirst
    rcases hzFirst with hzLegI | hzMiddle
    · exact Or.inl
        (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLegI)
    · exact Or.inr (Or.inl hzMiddle)
  · have hzLegJMap :
        z ∈ ((T.leg j).mapLe hgraph).support := by
      simpa [SimpleGraph.Walk.support_reverse] using hzLast
    exact Or.inr (Or.inr
      (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLegJMap))

theorem boundary_mem_internal_liftAttachToAttachViaLegSegment
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j : Fin 3}
    (middle : S.graph.Walk (T.boundary i) (T.boundary j))
    (hbi_ne_ai : T.boundary i ≠ T.attach i)
    (hbi_ne_aj : T.boundary i ≠ T.attach j) :
    T.boundary i ∈
      Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle) := by
  refine ⟨?_, ?_, ?_⟩
  · change
      T.boundary i ∈
        ((((T.leg i).mapLe hgraph).append middle).append
          ((T.leg j).mapLe hgraph).reverse).support
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    simp [SimpleGraph.Walk.support_mapLe_eq_support]
  · intro h
    exact hbi_ne_ai h
  · intro h
    exact hbi_ne_aj h

/-- The right-hand old boundary foot is also internal to a lifted
attach-to-attach rim, provided it has not collapsed to either new rim end.

This is the symmetric local fact needed for the source GM IX `(2.4)`
residual case where the first ordered side-tripod leg has collapsed: the
ambient tripod then uses the second ordered foot as the attachment on the
leg-segment rim and sends it to the `t` end of the cut path. -/
theorem boundary_right_mem_internal_liftAttachToAttachViaLegSegment
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j : Fin 3}
    (middle : S.graph.Walk (T.boundary i) (T.boundary j))
    (hbj_ne_ai : T.boundary j ≠ T.attach i)
    (hbj_ne_aj : T.boundary j ≠ T.attach j) :
    T.boundary j ∈
      Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle) := by
  refine ⟨?_, ?_, ?_⟩
  · change
      T.boundary j ∈
        ((((T.leg i).mapLe hgraph).append middle).append
          ((T.leg j).mapLe hgraph).reverse).support
    rw [SimpleGraph.Walk.mem_support_append_iff]
    right
    simp [SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_mapLe_eq_support]
  · intro h
    exact hbj_ne_ai h
  · intro h
    exact hbj_ne_aj h

private theorem liftAttachToAttachViaLegSegment_rim_internal_disjoint_of_middle_clean
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph) {i j : Fin 3}
    (hij : i ≠ j) {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    (hmiddle_clean : forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
      z = T.boundary i ∨ z = T.boundary j)
    (oldRim : H.graph.Walk (T.attach i) (T.attach j))
    (hold_support_cases : forall z : V, z ∈ oldRim.support ->
      z ∈ (T.rim i).support ∨ z ∈ (T.rim j).support) :
    Disjoint
      (Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle))
      (Walk.InternalVertices (oldRim.mapLe hgraph)) := by
  rw [Set.disjoint_left]
  intro z hz0 hzOldLift
  have hz0Support :
      z ∈ (T.liftAttachToAttachViaLegSegment hgraph i j middle).support :=
    hz0.1
  have hzOld : z ∈ oldRim.support := by
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using hzOldLift.1
  rcases T.liftAttachToAttachViaLegSegment_support_cases hgraph hz0Support
    with hzLegI | hzRest
  · rcases hold_support_cases z hzOld with hzRimI | hzRimJ
    · have hzAttachI : z = T.attach i :=
        T.legs_meet_rims_only_at_attach i i z hzLegI hzRimI
      exact hz0.2.1 hzAttachI
    · have hzAttachI : z = T.attach i :=
        T.legs_meet_rims_only_at_attach i j z hzLegI hzRimJ
      exact hz0.2.1 hzAttachI
  · rcases hzRest with hzMid | hzLegJ
    · rcases hold_support_cases z hzOld with hzRimI | hzRimJ
      · rcases hmiddle_clean z hzMid (T.rim_mem_vertexSet (i := i) hzRimI)
          with hzi | hzj
        · by_cases hleg_i_nil : (T.leg i).Nil
          · exact hz0.2.1
              (hzi.trans ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil))
          · exact T.boundary_not_mem_own_rim_of_leg_not_nil hleg_i_nil
              (by simpa [hzi] using hzRimI)
        · exact
            T.boundary_not_mem_rim_of_ne_index (fun hji => hij hji.symm)
              (by simpa [hzj] using hzRimI)
      · rcases hmiddle_clean z hzMid (T.rim_mem_vertexSet (i := j) hzRimJ)
          with hzi | hzj
        · exact
            T.boundary_not_mem_rim_of_ne_index hij
              (by simpa [hzi] using hzRimJ)
        · by_cases hleg_j_nil : (T.leg j).Nil
          · exact hz0.2.2
              (hzj.trans ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
          · exact T.boundary_not_mem_own_rim_of_leg_not_nil hleg_j_nil
              (by simpa [hzj] using hzRimJ)
    · rcases hold_support_cases z hzOld with hzRimI | hzRimJ
      · have hzAttachJ : z = T.attach j :=
          T.legs_meet_rims_only_at_attach j i z hzLegJ hzRimI
        exact hz0.2.2 hzAttachJ
      · have hzAttachJ : z = T.attach j :=
          T.legs_meet_rims_only_at_attach j j z hzLegJ hzRimJ
        exact hz0.2.2 hzAttachJ

/-- A lifted leg-segment rim is internally disjoint from the old left rim
between the same two attachments when the middle segment only meets the old
tripod at its two feet. -/
theorem liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph) {i j : Fin 3}
    (hij : i ≠ j) {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    (hmiddle_clean : forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
      z = T.boundary i ∨ z = T.boundary j) :
    Disjoint
      (Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle))
      (Walk.InternalVertices ((T.attachToAttachViaLeft i j).mapLe hgraph)) :=
  liftAttachToAttachViaLegSegment_rim_internal_disjoint_of_middle_clean
    T hgraph hij hmiddle_clean (T.attachToAttachViaLeft i j)
      (fun _ hz => T.attachToAttachViaLeft_support_cases hz)

/-- Right-rim analogue of
`liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean`. -/
theorem liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph) {i j : Fin 3}
    (hij : i ≠ j) {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    (hmiddle_clean : forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
      z = T.boundary i ∨ z = T.boundary j) :
    Disjoint
      (Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle))
      (Walk.InternalVertices ((T.attachToAttachViaRight i j).mapLe hgraph)) :=
  liftAttachToAttachViaLegSegment_rim_internal_disjoint_of_middle_clean
    T hgraph hij hmiddle_clean (T.attachToAttachViaRight i j)
      (fun _ hz => T.attachToAttachViaRight_support_cases hz)

/- These names expose the two formerly one-sided forms.  The hypotheses are no
longer required because nil legs place the corresponding foot at a path
endpoint. -/
theorem liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean_left_non_nil
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph) {i j : Fin 3}
    (hij : i ≠ j) {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    (hmiddle_clean : forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
      z = T.boundary i ∨ z = T.boundary j) :
    Disjoint
      (Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle))
      (Walk.InternalVertices ((T.attachToAttachViaRight i j).mapLe hgraph)) :=
  T.liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean
    hgraph hij hmiddle_clean

theorem liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean_right_non_nil
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph) {i j : Fin 3}
    (hij : i ≠ j) {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    (hmiddle_clean : forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
      z = T.boundary i ∨ z = T.boundary j) :
    Disjoint
      (Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle))
      (Walk.InternalVertices ((T.attachToAttachViaLeft i j).mapLe hgraph)) :=
  T.liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean
    hgraph hij hmiddle_clean

theorem liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean_right_non_nil
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph) {i j : Fin 3}
    (hij : i ≠ j) {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    (hmiddle_clean : forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
      z = T.boundary i ∨ z = T.boundary j) :
    Disjoint
      (Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle))
      (Walk.InternalVertices ((T.attachToAttachViaRight i j).mapLe hgraph)) :=
  T.liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean
    hgraph hij hmiddle_clean

theorem liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean_left_non_nil
    {S H : GeneralSociety V} [DecidableEq V]
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph) {i j : Fin 3}
    (hij : i ≠ j) {middle : S.graph.Walk (T.boundary i) (T.boundary j)}
    (hmiddle_clean : forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
      z = T.boundary i ∨ z = T.boundary j) :
    Disjoint
      (Walk.InternalVertices
        (T.liftAttachToAttachViaLegSegment hgraph i j middle))
      (Walk.InternalVertices ((T.attachToAttachViaLeft i j).mapLe hgraph)) :=
  T.liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean
    hgraph hij hmiddle_clean


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
