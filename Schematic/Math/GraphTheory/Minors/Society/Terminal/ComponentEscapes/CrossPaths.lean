import Schematic.Math.GraphTheory.Minors.Society.Terminal.ComponentEscapes.ArmComponents

/-!
Component-preserving paths from collapsed tripod arms across the cut path.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Splice a component-preserving escape from the old left common end onto
the initial tail of the induced cut path.

The escape is cut after its last contact with the selected collapsed arm.
This makes the splice simple even when the original component path wandered
through that arm.  The support conclusion records the two pieces needed for
the later distinct-component disjointness proof. -/
theorem Tripod.exists_leftComponentCrossPath
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    (hleftOutside : T.left ∈ P.outside)
    (hleftC : (⟨T.left, hleftOutside⟩ : P.outside) ∈ C.supp)
    {a : V} (q : S.graph.Walk T.left a)
    (hqPath : q.IsPath)
    (hqComponent : forall z : V, z ∈ q.support ->
      z ∈ induceComponentSupport (G := S.graph) C) :
    Exists fun firstPath : S.graph.Walk P.s a =>
      firstPath.IsPath ∧
        forall z : V, z ∈ firstPath.support ->
          z ∈ (P.pathTailToStart hi).support ∨
            z ∈ induceComponentSupport (G := S.graph) C := by
  classical
  let armSet : Set V := {z : V | z ∈ (T.attachToLeft i).support}
  have hleftArm : T.left ∈ armSet := by
    exact (T.attachToLeft i).end_mem_support
  obtain ⟨x, hxq, hxArmSet, hqTailPath, hqTailClean,
      hqTailSubset, _hqTailCovers, _hxIndex⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath armSet hleftArm
  have hxArm : x ∈ (T.attachToLeft i).support := by
    simpa [armSet] using hxArmSet
  let armPrefixOld :
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Walk
        (T.attach i) x :=
    (T.attachToLeft i).takeUntil x hxArm
  let armPrefix : S.graph.Walk (T.attach i) x :=
    armPrefixOld.mapLe
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  let qTail : S.graph.Walk x a := q.dropUntil x hxq
  let startTail : S.graph.Walk P.s (T.attach i) :=
    (P.pathTailToStart hi).reverse.copy rfl
      ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
  let core : S.graph.Walk (T.attach i) a := armPrefix.append qTail
  let firstPath : S.graph.Walk P.s a := startTail.append core
  have harmPrefixPath : armPrefix.IsPath := by
    simpa [armPrefix, armPrefixOld] using
      SimpleGraph.Walk.IsPath.mapLe
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
        ((T.attachToLeft_isPath i).takeUntil hxArm)
  have hqTailPath' : qTail.IsPath := by
    simpa [qTail] using hqTailPath
  have hcorePath : core.IsPath := by
    dsimp [core]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      harmPrefixPath hqTailPath' ?_
    intro z hzArmPrefix hzTail
    have hzArmOld : z ∈ (T.attachToLeft i).support := by
      apply SimpleGraph.Walk.support_takeUntil_subset
        (T.attachToLeft i) hxArm
      simpa [armPrefix, armPrefixOld,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzArmPrefix
    exact hqTailClean z (by simpa [qTail] using hzTail)
      (by simpa [armSet] using hzArmOld)
  have hstartTailPath : startTail.IsPath := by
    simpa [startTail] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathTailToStart hi).reverse rfl
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)).mpr
        (P.pathTailToStart_isPath hi).reverse
  have hfirstPath : firstPath.IsPath := by
    dsimp [firstPath]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hstartTailPath hcorePath ?_
    intro z hzStart hzCore
    have hzStartOld : z ∈ (P.pathTailToStart hi).support := by
      simpa [startTail, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse] using hzStart
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzCore with
      hzArmPrefix | hzTail
    · have hzArmOld : z ∈ (T.attachToLeft i).support := by
        apply SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft i) hxArm
        simpa [armPrefix, armPrefixOld,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzArmPrefix
      have hzRim : z ∈ (T.rim i).support :=
        T.attachToLeft_support_subset_rim i hzArmOld
      rcases hpath_contacts z
          (P.pathTailToStart_support_subset_pathSet hi z hzStartOld)
          (T.rim_mem_vertexSet (i := i) hzRim) with ⟨m, hm⟩
      by_cases hmi : m = i
      · subst m
        exact hm.trans ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
      · exact False.elim
          (T.boundary_not_mem_rim_of_ne_index hmi
            (by simpa [hm] using hzRim))
    · have hzComponent : z ∈ induceComponentSupport (G := S.graph) C :=
        hqComponent z (hqTailSubset z (by simpa [qTail] using hzTail))
      exact False.elim
        ((induceComponentSupport_subset (G := S.graph) C hzComponent).2
          (P.pathTailToStart_support_subset_pathSet hi z hzStartOld))
  refine ⟨firstPath, hfirstPath, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with
    hzStart | hzCore
  · left
    simpa [firstPath, startTail, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_reverse] using hzStart
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzCore with
      hzArmPrefix | hzTail
    · have hzArmOld : z ∈ (T.attachToLeft i).support := by
        apply SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft i) hxArm
        simpa [firstPath, core, armPrefix, armPrefixOld,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzArmPrefix
      by_cases hzAttach : z = T.attach i
      · left
        simp [hzAttach,
          ← (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil]
      · right
        exact
          GMIX24SourceProof.Tripod.attachToLeft_mem_outsideComponent_of_path_contacts_of_leg_nil
            hno_cross P T hpath_contacts hleg_i_nil C hleftOutside hleftC
            hzArmOld hzAttach
    · right
      exact hqComponent z (hqTailSubset z (by
        simpa [firstPath, core, qTail] using hzTail))

/-- Splice a component-preserving escape from the old right common end onto
the final tail of the induced cut path.

As in `exists_leftComponentCrossPath`, the escape is cut after its last
contact with the selected collapsed arm.  Reversing that clean tail and then
following the remaining arm and the final cut-path tail gives the path in the
orientation required by a cross. -/
theorem Tripod.exists_rightComponentCrossPath
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {k : Fin 3}
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_k_nil : (T.leg k).Nil)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    (hrightOutside : T.right ∈ P.outside)
    (hrightC : (⟨T.right, hrightOutside⟩ : P.outside) ∈ C.supp)
    {b : V} (q : S.graph.Walk T.right b)
    (hqPath : q.IsPath)
    (hqComponent : forall z : V, z ∈ q.support ->
      z ∈ induceComponentSupport (G := S.graph) C) :
    Exists fun secondPath : S.graph.Walk b P.t =>
      secondPath.IsPath ∧
        forall z : V, z ∈ secondPath.support ->
          z ∈ (P.pathTailToEnd hk).support ∨
            z ∈ induceComponentSupport (G := S.graph) C := by
  classical
  let armSet : Set V := {z : V | z ∈ (T.rightToAttach k).support}
  have hrightArm : T.right ∈ armSet := by
    exact (T.rightToAttach k).start_mem_support
  obtain ⟨x, hxq, hxArmSet, hqTailPath, hqTailClean,
      hqTailSubset, _hqTailCovers, _hxIndex⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath armSet hrightArm
  have hxArm : x ∈ (T.rightToAttach k).support := by
    simpa [armSet] using hxArmSet
  let armSuffixOld :
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Walk
        x (T.attach k) :=
    (T.rightToAttach k).dropUntil x hxArm
  let armSuffix : S.graph.Walk x (T.attach k) :=
    armSuffixOld.mapLe
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  let qTail : S.graph.Walk x b := q.dropUntil x hxq
  let endTail : S.graph.Walk (T.attach k) P.t :=
    (P.pathTailToEnd hk).copy
      ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl
  let core : S.graph.Walk b (T.attach k) := qTail.reverse.append armSuffix
  let secondPath : S.graph.Walk b P.t := core.append endTail
  have harmSuffixPath : armSuffix.IsPath := by
    simpa [armSuffix, armSuffixOld] using
      SimpleGraph.Walk.IsPath.mapLe
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
        ((T.rightToAttach_isPath k).dropUntil hxArm)
  have hqTailPath' : qTail.IsPath := by
    simpa [qTail] using hqTailPath
  have hcorePath : core.IsPath := by
    dsimp [core]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hqTailPath'.reverse harmSuffixPath ?_
    intro z hzTailRev hzArmSuffix
    have hzTail : z ∈ qTail.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hzTailRev
    have hzArmOld : z ∈ (T.rightToAttach k).support := by
      apply SimpleGraph.Walk.support_dropUntil_subset
        (T.rightToAttach k) hxArm
      simpa [armSuffix, armSuffixOld,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzArmSuffix
    exact hqTailClean z (by simpa [qTail] using hzTail)
      (by simpa [armSet] using hzArmOld)
  have hendTailPath : endTail.IsPath := by
    simpa [endTail] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathTailToEnd hk)
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl).mpr
        (P.pathTailToEnd_isPath hk)
  have hsecondPath : secondPath.IsPath := by
    dsimp [secondPath]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hcorePath hendTailPath ?_
    intro z hzCore hzEnd
    have hzEndOld : z ∈ (P.pathTailToEnd hk).support := by
      simpa [endTail, SimpleGraph.Walk.support_copy] using hzEnd
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzCore with
      hzTailRev | hzArmSuffix
    · have hzTail : z ∈ qTail.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzTailRev
      have hzComponent : z ∈ induceComponentSupport (G := S.graph) C :=
        hqComponent z (hqTailSubset z (by simpa [qTail] using hzTail))
      exact False.elim
        ((induceComponentSupport_subset (G := S.graph) C hzComponent).2
          (P.pathTailToEnd_support_subset_pathSet hk z hzEndOld))
    · have hzArmOld : z ∈ (T.rightToAttach k).support := by
        apply SimpleGraph.Walk.support_dropUntil_subset
          (T.rightToAttach k) hxArm
        simpa [armSuffix, armSuffixOld,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzArmSuffix
      have hzRim : z ∈ (T.rim k).support :=
        T.rightToAttach_support_subset_rim k hzArmOld
      rcases hpath_contacts z
          (P.pathTailToEnd_support_subset_pathSet hk z hzEndOld)
          (T.rim_mem_vertexSet (i := k) hzRim) with ⟨m, hm⟩
      by_cases hmk : m = k
      · subst m
        exact hm.trans ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
      · exact False.elim
          (T.boundary_not_mem_rim_of_ne_index hmk
            (by simpa [hm] using hzRim))
  refine ⟨secondPath, hsecondPath, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with
    hzCore | hzEnd
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzCore with
      hzTailRev | hzArmSuffix
    · right
      have hzTail : z ∈ qTail.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzTailRev
      exact hqComponent z (hqTailSubset z (by
        simpa [secondPath, core, qTail] using hzTail))
    · have hzArmOld : z ∈ (T.rightToAttach k).support := by
        apply SimpleGraph.Walk.support_dropUntil_subset
          (T.rightToAttach k) hxArm
        simpa [secondPath, core, armSuffix, armSuffixOld,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzArmSuffix
      by_cases hzAttach : z = T.attach k
      · left
        simp [hzAttach,
          ← (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil]
      · right
        exact
          GMIX24SourceProof.Tripod.rightToAttach_mem_outsideComponent_of_path_contacts_of_leg_nil
            hno_cross P T hpath_contacts hleg_k_nil C hrightOutside hrightC
            hzArmOld hzAttach
  · left
    simpa [secondPath, endTail, SimpleGraph.Walk.support_copy] using hzEnd

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
