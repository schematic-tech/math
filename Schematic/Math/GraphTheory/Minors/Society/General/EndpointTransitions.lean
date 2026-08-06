import Schematic.Math.GraphTheory.Minors.Society.General.Foundations

/-! Transitions from an ordered outer rim to the common left endpoint. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- A strict first-rim contact joined to the old left end closes a residual
prefixed along the first ordered left arm. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndFirstToLeftEndpoint
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (transition : S.graph.Walk u T.left)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = T.left)
    (htransition_qLeft : forall z : V,
      z ∈ transition.support ->
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z = T.left) :
    Nonempty S.Tripod := by
  let qLeftData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let qLeft : S.graph.Walk T.left a := qLeftData.walk
  have hqLeft_path : qLeft.IsPath := by
    simpa [qLeft] using qLeftData.walk_isPath
  have hqLeft_outside : forall z : V,
      z ∈ qLeft.support -> z ∈ P.outside := by
    simpa [qLeft] using hq_prefix_outside
  have hqLeft_distinct (s : Fin 3) (his : i ≠ s) : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.rim s).support -> z = T.left := by
    simpa [qLeft] using qLeftData.inter_distinct_rim_eq_left his
  have hqLeft_right (s : Fin 3) : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.attachToRight s).support -> False := by
    simpa [qLeft] using qLeftData.disjoint_attachToRight s
  have hqLeft_rim : forall s : Fin 3, forall z : V,
      z ∈ qLeft.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu
          (T.leftToAttach i).start_mem_support transition s).support ->
      z = T.left := by
    intro s z hzqLeft hzRim
    fin_cases s
    · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu
          (T.leftToAttach i).start_mem_support transition hzRim with
        hzSegment | hzArm
      · exact False.elim ((hqLeft_outside z hzqLeft).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegment))
      · exact False.elim (hqLeft_right i z hzqLeft
          (SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToRight i) (by
              simpa [Tripod.rightToAttach,
                SimpleGraph.Walk.support_reverse] using hu) hzArm))
    · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_support_cases
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu
          (T.leftToAttach i).start_mem_support transition hzRim with
        hzJ | hzLeft | hzTransition
      · exact hqLeft_distinct j hij z hzqLeft
          (T.attachToLeft_support_subset_rim j hzJ)
      · simpa using hzLeft
      · exact htransition_qLeft z hzTransition (by simpa [qLeft] using hzqLeft)
    · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu
          (T.leftToAttach i).start_mem_support transition hzRim with
        hzSegment | hzK | hzRight
      · exact False.elim ((hqLeft_outside z hzqLeft).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment))
      · exact False.elim (hqLeft_right k z hzqLeft hzK)
      · have hzRightOld : z ∈ (T.rightToAttach i).support :=
          SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach i) hu hzRight
        exact False.elim (hqLeft_right i z hzqLeft (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzRightOld))
  apply GMIX24SourceProof.Tripod.liftAllNilOfSameFirstArmTransitionOfRimClean
    P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
    hpath_contacts qLeft ha hqLeft_path hqLeft_outside hu hu_ne_attach
    hu_internal (T.leftToAttach i).start_mem_support
    (by
      intro h
      exact T.left_ne_boundary i
        (h.trans ((T.leg_nil_iff_boundary_eq_attach i).mp
          (hlegs_nil i)).symm))
    (Or.inr rfl) transition htransition_path htransition_outside
    htransition_clean hqLeft_rim

/-- Cut-path-reversed form of the strict last-rim-to-left-end exchange. -/
theorem Tripod.liftAllNilOfOuterLastLeftArmResidualAndLastToLeftEndpoint
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach k).support)
    (hx_ne_attach : x ≠ T.attach k)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach k).support)
    (hu_ne_attach : u ≠ T.attach k)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u T.left)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = T.left)
    (htransition_qLeft : forall z : V,
      z ∈ transition.support ->
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z = T.left) :
    Nonempty S.Tripod := by
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndFirstToLeftEndpoint
      (i := k) (j := j) (k := i) (q := q) (hx_arm := hx_arm)
      (u := u) (transition := transition) P.reverse T hgraph
      (fun h => hjk h.symm) (fun h => hik h.symm) (fun h => hij h.symm)
      hlegs_nil
  · simpa using hk
  · simpa using hj
  · simpa using hi
  · exact (GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order
  · exact (GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order
  · intro z hzPath hzT
    exact hpath_contacts z (by simpa using hzPath) hzT
  · exact hx_ne_attach
  · exact hx_internal
  · rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl (by simpa using ha)
  · exact hq_path
  · exact hq_clean
  · intro z hzq
    simpa using hq_prefix_outside z hzq
  · exact hu
  · exact hu_ne_attach
  · exact hu_internal
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean
  · exact htransition_qLeft

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
