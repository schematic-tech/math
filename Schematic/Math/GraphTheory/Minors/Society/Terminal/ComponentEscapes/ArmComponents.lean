import Schematic.Math.GraphTheory.Minors.Society.Terminal.Symmetry

/-!
Collapsed rim arms in the outside region and its connected components.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

private theorem rim_mem_outside_of_path_contacts_of_leg_nil
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} (hleg_nil : (T.leg r).Nil)
    {z : V} (hzRim : z ∈ (T.rim r).support)
    (hz_ne_attach : z ≠ T.attach r) :
    z ∈ P.outside := by
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_rim_support_subset_side_or_path
        P hno_cross T r hzRim with
    hzSide | hzPath
  · exact P.leftSide_subset_outside hzSide
  · rcases hpath_contacts z hzPath
        (T.rim_mem_vertexSet (i := r) hzRim) with ⟨m, hm⟩
    by_cases hmr : m = r
    · subst m
      exact False.elim (hz_ne_attach (by
        rw [← (T.leg_nil_iff_boundary_eq_attach r).mp hleg_nil]
        exact hm))
    · exact False.elim
        (T.boundary_not_mem_rim_of_ne_index hmr
          (by simpa [hm] using hzRim))

/-- Apart from its collapsed cut-path foot, the arm from that foot to the old
left common end lies outside the induced cut path. -/
theorem Tripod.attachToLeft_mem_outside_of_path_contacts_of_leg_nil
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} (hleg_nil : (T.leg r).Nil)
    {z : V} (hzArm : z ∈ (T.attachToLeft r).support)
    (hz_ne_attach : z ≠ T.attach r) :
    z ∈ P.outside := by
  exact rim_mem_outside_of_path_contacts_of_leg_nil hno_cross P T
    hpath_contacts hleg_nil (T.attachToLeft_support_subset_rim r hzArm)
    hz_ne_attach

/-- Apart from its collapsed cut-path foot, the arm from the old right common
end to that foot lies outside the induced cut path. -/
theorem Tripod.rightToAttach_mem_outside_of_path_contacts_of_leg_nil
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} (hleg_nil : (T.leg r).Nil)
    {z : V} (hzArm : z ∈ (T.rightToAttach r).support)
    (hz_ne_attach : z ≠ T.attach r) :
    z ∈ P.outside := by
  exact rim_mem_outside_of_path_contacts_of_leg_nil hno_cross P T
    hpath_contacts hleg_nil (T.rightToAttach_support_subset_rim r hzArm)
    hz_ne_attach

/-- A non-foot vertex on a collapsed left arm belongs to the same outside
component as the old left common end. -/
theorem Tripod.attachToLeft_mem_outsideComponent_of_path_contacts_of_leg_nil
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} (hleg_nil : (T.leg r).Nil)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    (hleftOutside : T.left ∈ P.outside)
    (hleftC : (⟨T.left, hleftOutside⟩ : P.outside) ∈ C.supp)
    {z : V} (hzArm : z ∈ (T.attachToLeft r).support)
    (hz_ne_attach : z ≠ T.attach r) :
    z ∈ induceComponentSupport (G := S.graph) C := by
  classical
  let oldTail :
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Walk
        z T.left :=
    (T.attachToLeft r).dropUntil z hzArm
  let tail : S.graph.Walk T.left z :=
    oldTail.reverse.mapLe
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  have hattach_not_oldTail : T.attach r ∉ oldTail.support := by
    simpa [oldTail] using
      Walk.IsPath.start_not_mem_dropUntil_support_of_ne
        (T.attachToLeft_isPath r) hzArm hz_ne_attach
  have htailOutside :
      forall w : V, w ∈ tail.support -> w ∈ P.outside := by
    intro w hw
    have hwOldTail : w ∈ oldTail.support := by
      simpa [tail, SimpleGraph.Walk.support_mapLe_eq_support,
        SimpleGraph.Walk.support_reverse] using hw
    have hwArm : w ∈ (T.attachToLeft r).support :=
      SimpleGraph.Walk.support_dropUntil_subset
        (T.attachToLeft r) hzArm (by simpa [oldTail] using hwOldTail)
    exact GMIX24SourceProof.Tripod.attachToLeft_mem_outside_of_path_contacts_of_leg_nil
      hno_cross P T hpath_contacts hleg_nil hwArm
      (fun hwAttach => hattach_not_oldTail (by simpa [hwAttach] using hwOldTail))
  exact
    SimpleGraph.Walk.support_subset_induceComponentSupport_of_start_mem
      C tail htailOutside ⟨hleftOutside, hleftC⟩ z tail.end_mem_support

/-- A non-foot vertex on a collapsed right arm belongs to the same outside
component as the old right common end. -/
theorem Tripod.rightToAttach_mem_outsideComponent_of_path_contacts_of_leg_nil
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} (hleg_nil : (T.leg r).Nil)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    (hrightOutside : T.right ∈ P.outside)
    (hrightC : (⟨T.right, hrightOutside⟩ : P.outside) ∈ C.supp)
    {z : V} (hzArm : z ∈ (T.rightToAttach r).support)
    (hz_ne_attach : z ≠ T.attach r) :
    z ∈ induceComponentSupport (G := S.graph) C := by
  classical
  let oldHead :
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Walk
        T.right z :=
    (T.rightToAttach r).takeUntil z hzArm
  let head : S.graph.Walk T.right z :=
    oldHead.mapLe
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  have hattach_not_oldHead : T.attach r ∉ oldHead.support := by
    simpa [oldHead] using
      SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        (T.rightToAttach_isPath r) hzArm
        (by simpa [ne_eq] using hz_ne_attach.symm)
  have hheadOutside :
      forall w : V, w ∈ head.support -> w ∈ P.outside := by
    intro w hw
    have hwOldHead : w ∈ oldHead.support := by
      simpa [head, SimpleGraph.Walk.support_mapLe_eq_support] using hw
    have hwArm : w ∈ (T.rightToAttach r).support :=
      SimpleGraph.Walk.support_takeUntil_subset
        (T.rightToAttach r) hzArm (by simpa [oldHead] using hwOldHead)
    exact GMIX24SourceProof.Tripod.rightToAttach_mem_outside_of_path_contacts_of_leg_nil
      hno_cross P T hpath_contacts hleg_nil hwArm
      (fun hwAttach => hattach_not_oldHead (by simpa [hwAttach] using hwOldHead))
  exact
    SimpleGraph.Walk.support_subset_induceComponentSupport_of_start_mem
      C head hheadOutside ⟨hrightOutside, hrightC⟩ z head.end_mem_support

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
