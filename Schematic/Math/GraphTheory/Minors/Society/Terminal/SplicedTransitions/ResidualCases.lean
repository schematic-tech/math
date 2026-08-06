import Schematic.Math.GraphTheory.Minors.Society.Terminal.SplicedTransitions.RimClean

/-!
Disjoint residual-transition cases for the ordered old rims.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- First-to-last transition against an escape prefixed along the first
ordered rim.  The rebuilt transition theta uses only the opposite side of
that first rim, so the prefixed leg meets it at the intended old left end. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndDisjointFirstToLastTransition
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hu : u ∈ (T.rightToAttach i).support)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim i) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ (T.leftArmPrefixTail
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
        hx_arm q).support -> False) :
    Nonempty S.Tripod := by
  let hgraph :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  let qLeftData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let qLeft : S.graph.Walk T.left a := qLeftData.walk
  have hqLeft_path : qLeft.IsPath := by
    simpa [qLeft] using qLeftData.walk_isPath
  have hqLeft_outside : forall z : V,
      z ∈ qLeft.support -> z ∈ P.outside := by
    simpa [qLeft, hgraph] using
      GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
        P hno_cross T hpath_contacts hx_arm hx_ne_attach q hq_outside
  have hqLeft_distinct_left (s : Fin 3) (his : i ≠ s) : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.leftToAttach s).support ->
        z = T.left := by
    simpa [qLeft] using qLeftData.inter_distinct_leftToAttach_eq_left his
  have hqLeft_same_right : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.attachToRight i).support -> False := by
    simpa [qLeft] using qLeftData.disjoint_attachToRight i
  have hqLeft_rim : forall s : Fin 3, forall z : V,
      z ∈ qLeft.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRim
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu hv transition s).support ->
      z = T.left := by
    intro s z hzqLeft hzRim
    fin_cases s
    · rcases
          GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRim_zero_support_cases
            P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu hv transition hzRim with
        hzSegment | hzArm | hzTransition
      · exact False.elim ((hqLeft_outside z hzqLeft).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegment))
      · exact False.elim (hqLeft_same_right z hzqLeft
          (SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToRight i) (by
              simpa [Tripod.rightToAttach,
                SimpleGraph.Walk.support_reverse] using hu) hzArm))
      · exact False.elim
          (htransition_q z hzTransition (by simpa [qLeft] using hzqLeft))
    · rcases
          GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRim_one_support_cases
            P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu hv transition hzRim with
        hzJ | hzK
      · apply hqLeft_distinct_left j hij z hzqLeft
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hzJ
      · apply hqLeft_distinct_left k hik z hzqLeft
        exact SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzK
    · rcases
          GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRim_two_support_cases
            P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu hv transition hzRim with
        hzSegment | hzArm
      · exact False.elim ((hqLeft_outside z hzqLeft).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment))
      · apply hqLeft_distinct_left k hik z hzqLeft
        have hzOld : z ∈ (T.attachToLeft k).support :=
          SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToLeft k) (by
              simpa [Tripod.attachToLeft,
                SimpleGraph.Walk.support_reverse] using hv) hzArm
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hzOld
  exact
    GMIX24SourceProof.Tripod.liftAllNilOfFirstToLastArmTransitionOfRimClean
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts qLeft ha hqLeft_path hqLeft_outside hu hright_contact
      hv hv_ne_attach hv_internal transition htransition_path
      htransition_outside htransition_clean hqLeft_rim

/-- First-to-middle transition against an escape prefixed along the first
ordered rim.  The prefixed escape is disjoint from the transition, and its
old-rim prefix avoids every other piece of the rebuilt theta. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndDisjointFirstToMiddleTransition
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
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
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> False) :
    Nonempty S.Tripod := by
  let qLeftData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let qLeft : S.graph.Walk T.left a := qLeftData.walk
  have hqLeft_path : qLeft.IsPath := by
    simpa [qLeft] using qLeftData.walk_isPath
  have hqLeft_outside : forall z : V,
      z ∈ qLeft.support -> z ∈ P.outside := by
    simpa [qLeft] using hq_prefix_outside
  have hqLeft_distinct_left (s : Fin 3) (his : i ≠ s) : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.leftToAttach s).support ->
        z = T.left := by
    simpa [qLeft] using qLeftData.inter_distinct_leftToAttach_eq_left his
  have hqLeft_right (s : Fin 3) : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.attachToRight s).support -> False := by
    simpa [qLeft] using qLeftData.disjoint_attachToRight s
  have hqLeft_rim : forall s : Fin 3, forall z : V,
      z ∈ qLeft.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu hv transition s).support ->
      z = v := by
    intro s z hzqLeft hzRim
    fin_cases s
    · rcases
          GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_zero_support_cases
            P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu hv transition hzRim with
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
          GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
            P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu hv transition hzRim with
        hzArm | hzTransition
      · have hzOld : z ∈ (T.attachToLeft j).support :=
          SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToLeft j) (by
              simpa [Tripod.attachToLeft,
                SimpleGraph.Walk.support_reverse] using hv) hzArm
        have hzLeft : z ∈ (T.leftToAttach j).support := by
          simpa [Tripod.attachToLeft,
            SimpleGraph.Walk.support_reverse] using hzOld
        have hzEq : z = T.left :=
          hqLeft_distinct_left j hij z hzqLeft hzLeft
        have hleftNotArm : T.left ∉
            ((T.attachToLeft j).takeUntil v (by
              simpa [Tripod.attachToLeft,
                SimpleGraph.Walk.support_reverse] using hv)).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (T.attachToLeft_isPath j) (by
              simpa [Tripod.attachToLeft,
                SimpleGraph.Walk.support_reverse] using hv)
              hv_internal.2.1.symm
        exact False.elim (hleftNotArm (by simpa [hzEq] using hzArm))
      · exact False.elim
          (htransition_q z hzTransition (by simpa [qLeft] using hzqLeft))
    · rcases
          GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
            P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu hv transition hzRim with
        hzSegment | hzArmK | hzRightI
      · exact False.elim ((hqLeft_outside z hzqLeft).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment))
      · exact False.elim (hqLeft_right k z hzqLeft hzArmK)
      · have hzOld : z ∈ (T.rightToAttach i).support :=
          SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach i) hu hzRightI
        exact False.elim (hqLeft_right i z hzqLeft (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzOld))
  have harm_qLeft : forall z : V,
      z ∈
        (((T.leftToAttach j).takeUntil v hv).reverse.mapLe hgraph).support ->
      z ∈ qLeft.support -> z = T.left := by
    intro z hzArm hzqLeft
    apply hqLeft_distinct_left j hij z hzqLeft
    apply SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach j) hv
    exact Walk.mem_support_of_mem_reverse_mapLe hgraph
      ((T.leftToAttach j).takeUntil v hv) hzArm
  exact
    GMIX24SourceProof.Tripod.liftAllNilOfFirstToMiddleArmTransitionOfRimClean
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts qLeft ha hqLeft_path hqLeft_outside hu hu_ne_attach
      hu_internal hv hv_ne_attach hv_internal transition htransition_path
      htransition_outside htransition_clean harm_qLeft hqLeft_rim

/-- Cut-path-reversed form of the prefixed first-to-middle exchange. -/
theorem Tripod.liftAllNilOfOuterLastLeftArmResidualAndDisjointLastToMiddleTransition
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
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
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> False) :
    Nonempty S.Tripod := by
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndDisjointFirstToMiddleTransition
      (i := k) (j := j) (k := i) (x := x) (a := a) (u := u) (v := v)
      (q := q) (hx_arm := hx_arm) (transition := transition)
      P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
      (fun h => hij h.symm) hlegs_nil
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
  · exact hv
  · exact hv_ne_attach
  · exact hv_internal
  · exact htransition_path
  · intro z hzTransition
    simpa using htransition_outside z hzTransition
  · exact htransition_clean
  · exact htransition_q

/-- Flip-symmetric form of first-left/first-to-middle: a right escape on the
first ordered rim and a middle-to-first transition. -/
theorem Tripod.liftAllNilOfOuterFirstRightArmResidualAndDisjointMiddleToFirstTransition
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_flip_arm : x ∈ (T.flip.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.flip.leftArmPrefixTail hgraph hx_flip_arm q).support ->
        z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim j))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim i))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.reverse.support ->
      z ∈ (T.flip.leftArmPrefixTail hgraph hx_flip_arm q).support -> False) :
    Nonempty S.Tripod := by
  let U := T.flip
  have hgraph_U : H.graph <= S.graph := hgraph
  have hpath_contacts_U : forall z : V,
      z ∈ P.pathSet -> z ∈ U.vertexSet ->
        Exists fun m : Fin 3 => z = U.boundary m := by
    simpa [U] using T.pathContacts_flip hpath_contacts
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndDisjointFirstToMiddleTransition
      (q := q) (hx_arm := hx_flip_arm) (transition := transition.reverse)
      P U hgraph_U hij hik hjk
      (fun s => by simpa [U] using hlegs_nil s)
  · simpa [U] using hi
  · simpa [U] using hj
  · simpa [U] using hk
  · simpa [U] using hij_order
  · simpa [U] using hjk_order
  · exact hpath_contacts_U
  · simpa [U] using hx_ne_attach
  · simpa [U, Walk.internalVertices_reverse] using hx_internal
  · exact ha
  · exact hq_path
  · intro z hzq hzU
    exact hq_clean z hzq (by simpa [U] using hzU)
  · simpa [U] using hq_prefix_outside
  · simpa [U] using
      (GMIX24SourceProof.Tripod.mem_flip_rightToAttach_of_mem_leftToAttach T hv)
  · simpa [U] using hv_ne_attach
  · simpa [U, Walk.internalVertices_reverse] using hv_internal
  · simpa [U] using
      (GMIX24SourceProof.Tripod.mem_flip_leftToAttach_of_mem_rightToAttach T hu)
  · simpa [U] using hu_ne_attach
  · simpa [U, Walk.internalVertices_reverse] using hu_internal
  · exact htransition_path.reverse
  · intro z hz
    apply htransition_outside z
    simpa [SimpleGraph.Walk.support_reverse] using hz
  · intro z hz hzU
    have hzTransition : z ∈ transition.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hz
    rcases htransition_clean z hzTransition (by simpa [U] using hzU) with
      hzu | hzv
    · exact Or.inr hzu
    · exact Or.inl hzv
  · exact htransition_q

/-- Flip-symmetric form of last-left/last-to-middle: a right escape on the
last ordered rim and a middle-to-last transition. -/
theorem Tripod.liftAllNilOfOuterLastRightArmResidualAndDisjointMiddleToLastTransition
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_flip_arm : x ∈ (T.flip.leftToAttach k).support)
    (hx_ne_attach : x ≠ T.attach k)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.flip.leftArmPrefixTail hgraph hx_flip_arm q).support ->
        z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim j))
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.reverse.support ->
      z ∈ (T.flip.leftArmPrefixTail hgraph hx_flip_arm q).support -> False) :
    Nonempty S.Tripod := by
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstRightArmResidualAndDisjointMiddleToFirstTransition
      (i := k) (j := j) (k := i) (q := q) (transition := transition)
      P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) hlegs_nil
  · simpa using hk
  · simpa using hj
  · simpa using hi
  · exact
      (GMIX24SourceProof.GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2
        hjk_order
  · exact
      (GMIX24SourceProof.GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2
        hij_order
  · intro z hzPath hzT
    exact hpath_contacts z (by simpa using hzPath) hzT
  · exact hx_ne_attach
  · exact hx_internal
  · simpa [or_comm] using ha
  · exact hq_path
  · exact hq_clean
  · intro z hz
    simpa using hq_prefix_outside z hz
  · exact hu
  · exact hu_ne_attach
  · exact hu_internal
  · exact hv
  · exact hv_ne_attach
  · exact hv_internal
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean
  · exact htransition_q

/-- A normalized transition whose two strict contacts lie on the median rim
closes an internal outer-left-arm residual, provided it is disjoint from the
prefixed escape.  Only the prefixed old arm is new: the theta itself is the
checked same-middle transition theta. -/
theorem Tripod.liftAllNilOfOuterLeftArmResidualAndDisjointSameMiddleTransition
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ (T.leftArmPrefixTail
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
        hx_arm q).support -> False) :
    Nonempty S.Tripod := by
  let hgraph :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  let qLeftData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let qLeft : S.graph.Walk T.left a := qLeftData.walk
  have hrj : r ≠ j := by
    rcases hr with rfl | rfl
    · exact hij
    · exact fun h => hjk h.symm
  have hqLeft_path : qLeft.IsPath := by
    simpa [qLeft] using qLeftData.walk_isPath
  have hqLeft_outside : forall z : V,
      z ∈ qLeft.support -> z ∈ P.outside := by
    simpa [qLeft, hgraph] using
      GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
        P hno_cross T hpath_contacts hx_arm hx_ne_attach q hq_outside
  have hqLeft_middle_arm : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.leftToAttach j).support ->
        z = T.left := by
    simpa [qLeft] using qLeftData.inter_distinct_leftToAttach_eq_left hrj
  have hqLeft_right_arm : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.rightToAttach j).support -> False := by
    simpa [qLeft, Tripod.rightToAttach,
      SimpleGraph.Walk.support_reverse] using
        qLeftData.disjoint_attachToRight j
  have hqLeft_outer_avoid : forall s : Fin 3, forall z : V,
      z ∈ qLeft.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support -> False := by
    simpa [qLeft] using
      GMIX24SourceProof.Tripod.leftArmPrefixTail_avoids_outerNilMiddleNonNilCommonLeftRims
        P T hgraph hi hj hk
        hij_order hjk_order hx_arm hx_ne_attach hx_internal q hq_clean
        hqLeft_outside
  have hqLeft_rim : forall s : Fin 3, forall z : V,
      z ∈ qLeft.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph (hlegs_nil j)
          hi hj hk hij_order hjk_order hu hv transition s).support ->
      z = v := by
    intro s z hzqLeft hzRim
    fin_cases s
    · exact False.elim (hqLeft_outer_avoid 0 z hzqLeft (by
        simpa [Tripod.allNilSameMiddleTransitionRim,
          SimpleGraph.Walk.support_copy] using hzRim))
    · rcases
          GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
            P T hgraph (hlegs_nil j)
            hi hj hk hij_order hjk_order hu hv transition hzRim with
        hzRight | hzTransition | hzLeftSuffix
      · exact False.elim (hqLeft_right_arm z hzqLeft
          (SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach j) hu hzRight))
      · exact False.elim
          (htransition_q z hzTransition (by simpa [qLeft] using hzqLeft))
      · have hzLeft : z ∈ (T.leftToAttach j).support :=
          SimpleGraph.Walk.support_dropUntil_subset
            (T.leftToAttach j) hv hzLeftSuffix
        have hzEq : z = T.left := hqLeft_middle_arm z hzqLeft hzLeft
        have hleftNotSuffix :
            T.left ∉ ((T.leftToAttach j).dropUntil v hv).support :=
          Walk.IsPath.start_not_mem_dropUntil_support_of_ne
            (T.leftToAttach_isPath j) hv hv_internal.2.1
        exact False.elim (hleftNotSuffix (by simpa [hzEq] using hzLeftSuffix))
    · exact False.elim (hqLeft_outer_avoid 2 z hzqLeft (by
        simpa [Tripod.allNilSameMiddleTransitionRim,
          SimpleGraph.Walk.support_copy] using hzRim))
  have harm_qLeft : forall z : V,
      z ∈
        (((T.leftToAttach j).takeUntil v hv).reverse.mapLe hgraph).support ->
      z ∈ qLeft.support -> z = T.left := by
    intro z hzArm hzqLeft
    apply hqLeft_middle_arm z hzqLeft
    apply SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach j) hv
    exact Walk.mem_support_of_mem_reverse_mapLe hgraph
      ((T.leftToAttach j).takeUntil v hv) hzArm
  exact
    GMIX24SourceProof.Tripod.liftAllNilOfSameMiddleArmTransitionOfRimClean
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts qLeft (Or.inl ha) hqLeft_path hqLeft_outside hu hu_ne_attach
      hright_contact hv hv_ne_attach (Or.inl hv_internal) transition
      htransition_path htransition_outside htransition_clean
      harm_qLeft hqLeft_rim

/-- Right-arm symmetric form of the disjoint median-transition residual.  The
old theta and transition are both reversed, turning the selected right-arm
prefix into the left-arm prefix handled above. -/
theorem Tripod.liftAllNilOfOuterRightArmResidualAndDisjointSameMiddleTransition
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_flip_arm : x ∈ (T.flip.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim j))
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.reverse.support ->
      z ∈ (T.flip.leftArmPrefixTail
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
        hx_flip_arm q).support -> False) :
    Nonempty S.Tripod := by
  let U := T.flip
  have hv_U_right : v ∈ (U.rightToAttach j).support := by
    simpa [U] using
      GMIX24SourceProof.Tripod.mem_flip_rightToAttach_of_mem_leftToAttach T hv
  have hu_U_left : u ∈ (U.leftToAttach j).support := by
    simpa [U] using
      GMIX24SourceProof.Tripod.mem_flip_leftToAttach_of_mem_rightToAttach T hu
  have hpath_contacts_U : forall z : V,
      z ∈ P.pathSet -> z ∈ U.vertexSet ->
        Exists fun m : Fin 3 => z = U.boundary m := by
    simpa [U] using T.pathContacts_flip hpath_contacts
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfOuterLeftArmResidualAndDisjointSameMiddleTransition
      P hno_cross U hij hik hjk hr
      (fun s => by simpa [U] using hlegs_nil s)
      (by simpa [U] using hi) (by simpa [U] using hj)
      (by simpa [U] using hk) (by simpa [U] using hij_order)
      (by simpa [U] using hjk_order) hpath_contacts_U q hx_flip_arm
      (by simpa [U] using hx_ne_attach)
      (by simpa [U, Walk.internalVertices_reverse] using hx_internal)
      ha hq_path hq_outside
      (by
        intro z hzq hzU
        exact hq_clean z hzq (by simpa [U] using hzU))
      hv_U_right (by simpa [U] using hv_ne_attach)
      (Or.inl (by simpa [U, Walk.internalVertices_reverse] using hv_internal))
      hu_U_left (by simpa [U] using hu_ne_attach)
      (by simpa [U, Walk.internalVertices_reverse] using hu_internal)
      transition.reverse htransition_path.reverse
      (by
        intro z hz
        apply htransition_outside z
        simpa [SimpleGraph.Walk.support_reverse] using hz)
      (by
        intro z hz hzU
        have hzTransition : z ∈ transition.support := by
          simpa [SimpleGraph.Walk.support_reverse] using hz
        rcases htransition_clean z hzTransition (by simpa [U] using hzU) with
          hzu | hzv
        · exact Or.inr hzu
        · exact Or.inl hzv)
      htransition_q

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
