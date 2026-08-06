import Schematic.Math.GraphTheory.Minors.Society.Terminal.SplicedTransitions.CarrierBridge

/-!
Transition lifts with precise rebuilt-rim incidence assumptions.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Same-median transition lift with the exact weaker interface needed by a
prefixed outer-rim escape.  The escape need not be clean against the whole old
tripod: its arm prefix must meet the escape only at `T.left`, and its outside
suffix must meet each rebuilt rim only at the middle attachment `v`. -/
theorem Tripod.liftAllNilOfSameMiddleArmTransitionOfRimClean
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
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
    {a u v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (harm_q : forall z : V,
      z ∈
        (((T.leftToAttach j).takeUntil v hv).reverse.mapLe hgraph).support ->
      z ∈ q.support -> z = T.left)
    (hq_rim : forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph (hlegs_nil j)
          hi hj hk hij_order hjk_order hu hv transition s).support ->
      z = v) :
    Nonempty S.Tripod := by
  let qnil : S.graph.Walk T.left T.left := SimpleGraph.Walk.nil
  have hqnil_outside : forall z : V,
      z ∈ qnil.support -> z ∈ P.outside := by
    intro z hz
    have hzLeft : z = T.left := by simpa [qnil] using hz
    simpa [hzLeft] using hq_outside T.left q.start_mem_support
  have hqnil_clean : forall z : V, z ∈ qnil.support ->
      z ∈ T.vertexSet -> z = T.left := by
    intro z hz _hzT
    simpa [qnil] using hz
  have hu_ne_left : u ≠ T.left := by
    intro huLeft
    rcases hright_contact with huInternal | huRight
    · exact huInternal.2.1 huLeft
    · exact T.left_ne_right (huLeft.symm.trans huRight)
  have htransition_qnil : forall z : V, z ∈ transition.support ->
      z ∈ qnil.support -> z = v := by
    intro z hzTransition hzNil
    have hzLeft : z = T.left := by simpa [qnil] using hzNil
    rcases htransition_clean z hzTransition (by
        simp [hzLeft]) with hzu | hzv
    · exact False.elim (hu_ne_left (hzu.symm.trans hzLeft))
    · exact hzv
  have hold_incidence :=
    GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts qnil hqnil_outside
      hqnil_clean hu hu_ne_attach hv hv_ne_attach hleft_contact transition
      htransition_outside htransition_clean htransition_qnil
  have hlegs_incidence : forall r s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
          P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q r).support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph (hlegs_nil j)
          hi hj hk hij_order hjk_order hu hv transition s).support ->
      z =
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v r := by
    intro r s z hzLeg hzRim
    fin_cases r
    · apply hold_incidence 0 s z
      · simpa [Tripod.allNilSameMiddleTransitionLeg, qnil] using hzLeg
      · exact hzRim
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzLeg with
        hzArm | hzq
      · apply hold_incidence 1 s z
        · exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inl hzArm)
        · exact hzRim
      · simpa [Tripod.allNilSameMiddleTransitionAttach] using
          hq_rim s z hzq hzRim
    · apply hold_incidence 2 s z
      · simpa [Tripod.allNilSameMiddleTransitionLeg, qnil] using hzLeg
      · exact hzRim
  have hleg_path : forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
        P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q r).IsPath := by
    intro r
    fin_cases r
    · simpa [Tripod.allNilSameMiddleTransitionLeg] using
        (SimpleGraph.Walk.isPath_copy (P.pathTailToStart hi)
          ((T.leg_nil_iff_boundary_eq_attach i).mp (hlegs_nil i)) rfl).mpr
            (P.pathTailToStart_isPath hi)
    · exact Walk.IsPath.append_of_support_inter_eq_endpoint
        (SimpleGraph.Walk.IsPath.mapLe hgraph
          ((T.leftToAttach_isPath j).takeUntil hv).reverse)
        hq_path harm_q
    · simpa [Tripod.allNilSameMiddleTransitionLeg] using
        (SimpleGraph.Walk.isPath_copy (P.pathTailToEnd hk)
          ((T.leg_nil_iff_boundary_eq_attach k).mp (hlegs_nil k)) rfl).mpr
            (P.pathTailToEnd_isPath hk)
  refine ⟨{
    left := T.right
    right := T.attach j
    left_ne_right := by
      intro h
      exact T.right_ne_boundary j
        (h.trans ((T.leg_nil_iff_boundary_eq_attach j).mp
          (hlegs_nil j)).symm)
    rim := GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
      P T hgraph (hlegs_nil j)
      hi hj hk hij_order hjk_order hu hv transition
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hv hv_ne_attach transition htransition_path htransition_clean
    attach :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach_mem_rim
        P T hgraph hij hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hu hv hv_ne_attach hleft_contact transition
    boundary := P.boundaryTriple a
    boundary_mem := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_mem_of_leftArc ha
      · exact P.boundaryTriple_mem_of_rightArc ha
    boundary_injective := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_injective_of_leftArc ha
      · exact P.boundaryTriple_injective_of_rightArc ha
    leg := GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
      P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q
    leg_isPath := hleg_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact
        hv hleft_contact transition htransition_outside htransition_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_pairwise_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order hpath_contacts hv q hq_outside
    legs_meet_rims_only_at_attach := hlegs_incidence
  }⟩

/-- Replace only the middle leg in any checked all-nil transition theta.
The two extreme cut-path tails keep their old incidence proof; the caller
supplies the exact intersection of the new middle leg with the rebuilt rims. -/
theorem Tripod.allNilCleanBridgeLegs_meet_rims_of_middle_rim_clean
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    {i k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {l r a : V}
    (rim : Fin 3 -> S.graph.Walk l r)
    (q : S.graph.Walk T.left a)
    (hbase : forall p s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg
          P T hleg_i_nil hleg_k_nil hi hk
          (SimpleGraph.Walk.nil : S.graph.Walk T.left T.left) p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k p)
    (hq_rim : forall s : Fin 3, forall z : V,
      z ∈ q.support -> z ∈ (rim s).support -> z = T.left) :
    forall p s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg
          P T hleg_i_nil hleg_k_nil hi hk q p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k p := by
  intro p s z hzLeg hzRim
  fin_cases p
  · apply hbase 0 s z
    · simpa [Tripod.allNilCleanBridgeLeg] using hzLeg
    · exact hzRim
  · simpa [Tripod.allNilCleanBridgeAttach] using
      hq_rim s z (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg) hzRim
  · apply hbase 2 s z
    · simpa [Tripod.allNilCleanBridgeLeg] using hzLeg
    · exact hzRim

/-- Middle-arm-prefixed analogue of
`allNilCleanBridgeLegs_meet_rims_of_middle_rim_clean`. -/
theorem Tripod.allNilSameMiddleTransitionLegs_meet_rims_of_tail_rim_clean
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {l r a v : V}
    (hv : v ∈ (T.leftToAttach j).support)
    (rim : Fin 3 -> S.graph.Walk l r)
    (q : S.graph.Walk T.left a)
    (hbase : forall p s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
          P T hgraph hleg_i_nil hleg_k_nil hi hk hv
          (SimpleGraph.Walk.nil : S.graph.Walk T.left T.left) p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v p)
    (hq_rim : forall s : Fin 3, forall z : V,
      z ∈ q.support -> z ∈ (rim s).support -> z = v) :
    forall p s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
          P T hgraph hleg_i_nil hleg_k_nil hi hk hv q p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v p := by
  intro p s z hzLeg hzRim
  fin_cases p
  · apply hbase 0 s z
    · simpa [Tripod.allNilSameMiddleTransitionLeg] using hzLeg
    · exact hzRim
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzLeg with
      hzArm | hzq
    · apply hbase 1 s z
      · exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inl hzArm)
      · exact hzRim
    · simpa [Tripod.allNilSameMiddleTransitionAttach] using
        hq_rim s z hzq hzRim
  · apply hbase 2 s z
    · simpa [Tripod.allNilSameMiddleTransitionLeg] using hzLeg
    · exact hzRim

/-- First-to-middle transition theta with a prefixed middle boundary leg and
only exact arm/rim incidence assumptions. -/
theorem Tripod.liftAllNilOfFirstToMiddleArmTransitionOfRimClean
    [DecidableEq V]
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a u v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
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
    (harm_q : forall z : V,
      z ∈
        (((T.leftToAttach j).takeUntil v hv).reverse.mapLe hgraph).support ->
      z ∈ q.support -> z = T.left)
    (hq_rim : forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu hv transition s).support ->
      z = v) :
    Nonempty S.Tripod := by
  let qnil : S.graph.Walk T.left T.left := SimpleGraph.Walk.nil
  have hqnil_outside : forall z : V,
      z ∈ qnil.support -> z ∈ P.outside := by
    intro z hz
    have hzLeft : z = T.left := by simpa [qnil] using hz
    simpa [hzLeft] using hq_outside T.left q.start_mem_support
  have hqnil_clean : forall z : V, z ∈ qnil.support ->
      z ∈ T.vertexSet -> z = T.left := by
    intro z hz _hzT
    simpa [qnil] using hz
  have htransition_qnil : forall z : V, z ∈ transition.support ->
      z ∈ qnil.support -> False := by
    intro z hzTransition hzNil
    have hzLeft : z = T.left := by simpa [qnil] using hzNil
    rcases htransition_clean z hzTransition (by
        simp [hzLeft]) with hzu | hzv
    · exact hu_internal.2.1 (hzu.symm.trans hzLeft)
    · exact hv_internal.2.1 (hzv.symm.trans hzLeft)
  have hbase :=
    GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts qnil hqnil_outside
      hqnil_clean hu hu_ne_attach hu_internal hv hv_ne_attach hv_internal
      transition htransition_outside htransition_clean htransition_qnil
  have hincidence :=
    GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_meet_rims_of_tail_rim_clean
      P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
        P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hv transition)
      q (by simpa [qnil] using hbase) hq_rim
  have hleg_path : forall s : Fin 3,
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
        P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q s).IsPath := by
    intro s
    fin_cases s
    · simpa [Tripod.allNilSameMiddleTransitionLeg] using
        (SimpleGraph.Walk.isPath_copy (P.pathTailToStart hi)
          ((T.leg_nil_iff_boundary_eq_attach i).mp (hlegs_nil i)) rfl).mpr
            (P.pathTailToStart_isPath hi)
    · exact Walk.IsPath.append_of_support_inter_eq_endpoint
        (SimpleGraph.Walk.IsPath.mapLe hgraph
          ((T.leftToAttach_isPath j).takeUntil hv).reverse)
        hq_path harm_q
    · simpa [Tripod.allNilSameMiddleTransitionLeg] using
        (SimpleGraph.Walk.isPath_copy (P.pathTailToEnd hk)
          ((T.leg_nil_iff_boundary_eq_attach k).mp (hlegs_nil k)) rfl).mpr
            (P.pathTailToEnd_isPath hk)
  refine ⟨{
    left := T.attach j
    right := u
    left_ne_right := by
      intro hju
      exact T.attach_not_mem_rim_of_ne (fun h => hij h.symm)
        (by simpa [hju] using hu_internal.1)
    rim := GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
      P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu hv transition
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_internal
        hv transition htransition_path htransition_clean
    attach := GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionAttach_mem_rim
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hu_ne_attach hu_internal
        hv hv_ne_attach hv_internal transition
    boundary := P.boundaryTriple a
    boundary_mem := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_mem_of_leftArc ha
      · exact P.boundaryTriple_mem_of_rightArc ha
    boundary_injective := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_injective_of_leftArc ha
      · exact P.boundaryTriple_injective_of_rightArc ha
    leg := GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
      P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q
    leg_isPath := hleg_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach hu_internal
        hv hv_internal transition htransition_outside htransition_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_pairwise_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order hpath_contacts hv q hq_outside
    legs_meet_rims_only_at_attach := hincidence
  }⟩

/-- First-to-last transition theta with a middle boundary leg known clean
only against the three rebuilt rims. -/
theorem Tripod.liftAllNilOfFirstToLastArmTransitionOfRimClean
    [DecidableEq V]
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a u v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
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
    (hq_rim : forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRim
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu hv transition s).support ->
      z = T.left) :
    Nonempty S.Tripod := by
  let qnil : S.graph.Walk T.left T.left := SimpleGraph.Walk.nil
  have hqnil_outside : forall z : V,
      z ∈ qnil.support -> z ∈ P.outside := by
    intro z hz
    have hzLeft : z = T.left := by simpa [qnil] using hz
    simpa [hzLeft] using hq_outside T.left q.start_mem_support
  have hqnil_clean : forall z : V, z ∈ qnil.support ->
      z ∈ T.vertexSet -> z = T.left := by
    intro z hz _hzT
    simpa [qnil] using hz
  have hu_ne_left : u ≠ T.left := by
    intro huLeft
    rcases hright_contact with huInternal | huRight
    · exact huInternal.2.1 huLeft
    · exact T.left_ne_right (huLeft.symm.trans huRight)
  have htransition_qnil : forall z : V, z ∈ transition.support ->
      z ∈ qnil.support -> False := by
    intro z hzTransition hzNil
    have hzLeft : z = T.left := by simpa [qnil] using hzNil
    rcases htransition_clean z hzTransition (by
        simp [hzLeft]) with hzu | hzv
    · exact hu_ne_left (hzu.symm.trans hzLeft)
    · exact hv_internal.2.1 (hzv.symm.trans hzLeft)
  have hbase :=
    GMIX24SourceProof.Tripod.allNilFirstToLastTransitionLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts qnil hqnil_outside
      hqnil_clean hu hv hv_ne_attach hv_internal transition
      htransition_outside htransition_qnil
  have hincidence :=
    GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_meet_rims_of_middle_rim_clean
      P T (hlegs_nil i) (hlegs_nil k) hi hk
      (GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRim
        P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hv transition)
      q (by simpa [qnil] using hbase) hq_rim
  refine ⟨{
    left := T.attach j
    right := v
    left_ne_right := by
      intro hju
      exact T.attach_not_mem_rim_of_ne hjk
        (by simpa [hju] using hv_internal.1)
    rim := GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRim
      P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu hv transition
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hv
        hv_internal transition htransition_path htransition_outside
        htransition_clean
    attach := GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilFirstToLastTransitionAttach_mem_rim
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hv hv_ne_attach hv_internal transition
    boundary := P.boundaryTriple a
    boundary_mem := P.boundaryTriple_mem_of_leftArc ha
    boundary_injective := P.boundaryTriple_injective_of_leftArc ha
    leg := GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
      (hlegs_nil i) (hlegs_nil k) hi hk q
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLeg_isPath P T
        (hlegs_nil i) (hlegs_nil k) hi hk q hq_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilFirstToLastTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact hv
        hv_ne_attach hv_internal transition htransition_outside htransition_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_pairwise_disjoint
        P T (j := j) (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order q hq_outside
    legs_meet_rims_only_at_attach := hincidence
  }⟩

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
