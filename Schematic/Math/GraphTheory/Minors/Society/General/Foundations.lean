import Schematic.Math.GraphTheory.Minors.Society.Hidden
import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.OrderedTripodData

/-! Shared lifting and arm-incidence facts for the GM IX `(2.4)` source proof. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Replace the middle attachment and middle boundary leg of an already
checked theta.  The two extreme legs are the ordered cut-path tails; callers
only have to prove their (usually inherited) rim incidence and the exact
incidence of the new middle leg. -/
theorem Tripod.liftCheckedRimsWithSplicedMiddleLeg
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
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
        Walk.supportIndex P.path (T.boundary k))
    {l r a c : V}
    (hlr : l ≠ r)
    (rim : Fin 3 -> S.graph.Walk l r)
    (hrim_path : forall s : Fin 3, (rim s).IsPath)
    (hrim_disjoint : forall s t : Fin 3, s ≠ t ->
      Disjoint (Walk.InternalVertices (rim s))
        (Walk.InternalVertices (rim t)))
    (hattach : forall s : Fin 3,
      GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c s ∈
        Walk.InternalVertices (rim s))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (tail : S.graph.Walk c a)
    (htail_path : tail.IsPath)
    (htail_outside : forall z : V,
      z ∈ tail.support -> z ∈ P.outside)
    (houter_incidence : forall p s : Fin 3, p ≠ 1 -> forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
          hleg_i_nil hleg_k_nil hi hk tail p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c p)
    (hmiddle_incidence : forall s : Fin 3, forall z : V,
      z ∈ tail.support -> z ∈ (rim s).support -> z = c) :
    Nonempty S.Tripod := by
  refine ⟨{
    left := l
    right := r
    left_ne_right := hlr
    rim := rim
    rim_isPath := hrim_path
    attach :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c
    attach_mem_rim := hattach
    boundary := P.boundaryTriple a
    boundary_mem := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_mem_of_leftArc ha
      · exact P.boundaryTriple_mem_of_rightArc ha
    boundary_injective := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_injective_of_leftArc ha
      · exact P.boundaryTriple_injective_of_rightArc ha
    leg := GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
      hleg_i_nil hleg_k_nil hi hk tail
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg_isPath
        P T hleg_i_nil hleg_k_nil hi hk tail htail_path
    rim_internals_disjoint := hrim_disjoint
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionLegs_pairwise_disjoint
        P T hleg_i_nil hleg_k_nil hi hk hij_order hjk_order tail
        htail_outside
    legs_meet_rims_only_at_attach := by
      intro p s z hzLeg hzRim
      fin_cases p
      · exact houter_incidence 0 s (by decide) z hzLeg hzRim
      · simpa [Tripod.allNilSplicedTransitionLeg,
          Tripod.allNilSplicedTransitionAttach] using
          hmiddle_incidence s z
            (by simpa [Tripod.allNilSplicedTransitionLeg] using hzLeg) hzRim
      · exact houter_incidence 2 s (by decide) z hzLeg hzRim
  }⟩

/-- Last-contact form of `liftCheckedRimsWithSplicedMiddleLeg`.  The full
escape avoids the two outer rebuilt rims and starts on the middle one; its
suffix after the last middle-rim contact is therefore an exact middle leg. -/
theorem Tripod.liftCheckedRimsAtLastMiddleContact
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
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
        Walk.supportIndex P.path (T.boundary k))
    {l r a : V}
    (hlr : l ≠ r)
    (rim : Fin 3 -> S.graph.Walk l r)
    (hrim_path : forall s : Fin 3, (rim s).IsPath)
    (hrim_disjoint : forall s t : Fin 3, s ≠ t ->
      Disjoint (Walk.InternalVertices (rim s))
        (Walk.InternalVertices (rim t)))
    (hi_attach : T.attach i ∈ Walk.InternalVertices (rim 0))
    (hk_attach : T.attach k ∈ Walk.InternalVertices (rim 2))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    {c0 : V}
    (escape : S.graph.Walk c0 a)
    (hescape_path : escape.IsPath)
    (hescape_outside : forall z : V,
      z ∈ escape.support -> z ∈ P.outside)
    (hescape_middle : Exists fun z : V =>
      z ∈ escape.support ∧ z ∈ (rim 1).support)
    (hescape_outer : forall z : V, z ∈ escape.support ->
      z ∈ (rim 0).support ∨ z ∈ (rim 2).support -> False)
    (hescape_ne_leftEnd : forall z : V,
      z ∈ escape.support -> z ≠ l)
    (hescape_ne_rightEnd : forall z : V,
      z ∈ escape.support -> z ≠ r)
    (houter_incidence : forall p s : Fin 3, p ≠ 1 -> forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
          hleg_i_nil hleg_k_nil hi hk escape p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach
        T i k c0 p) :
    Nonempty S.Tripod := by
  rcases hescape_middle with ⟨c0', hc0Escape, hc0Middle⟩
  let escape' : S.graph.Walk c0' a := escape.dropUntil c0' hc0Escape
  have hescape'_path : escape'.IsPath := by
    simpa [escape'] using hescape_path.dropUntil hc0Escape
  obtain ⟨c, hcEscape, hcMiddle, htail_path, hlast, htail_subset,
      _htail_covers, _hc_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound hescape'_path
      {z : V | z ∈ (rim 1).support} hc0Middle
  let tail : S.graph.Walk c a := escape'.dropUntil c hcEscape
  have hescape'_subset : forall z : V,
      z ∈ escape'.support -> z ∈ escape.support := by
    intro z hz
    exact SimpleGraph.Walk.support_dropUntil_subset escape hc0Escape
      (by simpa [escape'] using hz)
  have htail_outside : forall z : V,
      z ∈ tail.support -> z ∈ P.outside := by
    intro z hz
    exact hescape_outside z (hescape'_subset z
      (htail_subset z (by simpa [tail] using hz)))
  have hc_internal : c ∈ Walk.InternalVertices (rim 1) :=
    ⟨hcMiddle, hescape_ne_leftEnd c (hescape'_subset c hcEscape),
      hescape_ne_rightEnd c (hescape'_subset c hcEscape)⟩
  have hattach : forall s : Fin 3,
      GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c s ∈
        Walk.InternalVertices (rim s) := by
    intro s
    fin_cases s
    · simpa [Tripod.allNilSplicedTransitionAttach] using hi_attach
    · simpa [Tripod.allNilSplicedTransitionAttach] using hc_internal
    · simpa [Tripod.allNilSplicedTransitionAttach] using hk_attach
  have houter_incidence_tail : forall p s : Fin 3, p ≠ 1 -> forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
          hleg_i_nil hleg_k_nil hi hk tail p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c p := by
    intro p s hp z hzLeg hzRim
    fin_cases p
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilSplicedTransitionAttach] using
        houter_incidence 0 s (by decide) z (by
          simpa [Tripod.allNilSplicedTransitionLeg] using hzLeg) hzRim
    · exact False.elim (hp rfl)
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilSplicedTransitionAttach] using
        houter_incidence 2 s (by decide) z (by
          simpa [Tripod.allNilSplicedTransitionLeg] using hzLeg) hzRim
  have hmiddle_incidence : forall s : Fin 3, forall z : V,
      z ∈ tail.support -> z ∈ (rim s).support -> z = c := by
    intro s z hzTail hzRim
    have hzEscape : z ∈ escape.support := hescape'_subset z
      (htail_subset z (by simpa [tail] using hzTail))
    fin_cases s
    · exact False.elim (hescape_outer z hzEscape (Or.inl hzRim))
    · exact hlast z (by simpa [tail] using hzTail) hzRim
    · exact False.elim (hescape_outer z hzEscape (Or.inr hzRim))
  exact GMIX24SourceProof.Tripod.liftCheckedRimsWithSplicedMiddleLeg
    P T hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hlr rim
    hrim_path hrim_disjoint hattach ha tail (by simpa [tail] using htail_path)
    htail_outside houter_incidence_tail hmiddle_incidence

theorem Tripod.leftArmPrefixTail_inter_distinct_rim_eq_left
    {S H : GeneralSociety V}
    (T : H.Tripod) (hgraph : H.graph <= S.graph)
    {r s : Fin 3} (hrs : r ≠ s)
    {x a : V} (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (q : S.graph.Walk x a)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x) :
    forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support ->
      z ∈ (T.rim s).support -> z = T.left :=
  T.leftArmPrefixTail_inter_distinct_rim_eq_left_of_clean
    hgraph hrs hx_arm hx_internal q hq_clean

theorem Tripod.leftArmPrefixTail_disjoint_attachToRight
    {S H : GeneralSociety V}
    (T : H.Tripod) (hgraph : H.graph <= S.graph)
    {r s : Fin 3}
    {x a : V} (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (q : S.graph.Walk x a)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x) :
    forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support ->
      z ∈ (T.attachToRight s).support -> False :=
  T.leftArmPrefixTail_disjoint_attachToRight_of_clean
    hgraph hx_arm hx_ne_attach hx_internal q hq_clean

/-- Same-first transition theta with a middle boundary leg required to be
clean only against the three rebuilt rims. -/
theorem Tripod.liftAllNilOfSameFirstArmTransitionOfRimClean
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
    {a u v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hleft_contact : v ∈ Walk.InternalVertices (T.rim i) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (hq_rim : forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
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
  have htransition_qnil : forall z : V, z ∈ transition.support ->
      z ∈ qnil.support -> z = T.left := by
    intro z _hzTransition hzNil
    simpa [qnil] using hzNil
  have hbase :=
    GMIX24SourceProof.Tripod.allNilSameFirstTransitionLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts qnil hqnil_outside
      hqnil_clean hu hu_ne_attach hv hv_ne_attach transition
      htransition_outside htransition_qnil
  have hincidence :=
    GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_meet_rims_of_middle_rim_clean
      P T (hlegs_nil i) (hlegs_nil k) hi hk
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
        P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hv transition)
      q (by simpa [qnil] using hbase) hq_rim
  refine ⟨{
    left := T.attach j
    right := u
    left_ne_right := by
      intro hju
      exact T.attach_not_mem_rim_of_ne (fun h => hij h.symm)
        (by simpa [hju] using hu_internal.1)
    rim := GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
      P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu hv transition
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hu_internal hv transition
        htransition_path htransition_clean
    attach := GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionAttach_mem_rim
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hu_ne_attach hu_internal hv transition
    boundary := P.boundaryTriple a
    boundary_mem := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_mem_of_leftArc ha
      · exact P.boundaryTriple_mem_of_rightArc ha
    boundary_injective := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_injective_of_leftArc ha
      · exact P.boundaryTriple_injective_of_rightArc ha
    leg := GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
      (hlegs_nil i) (hlegs_nil k) hi hk q
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLeg_isPath P T
        (hlegs_nil i) (hlegs_nil k) hi hk q hq_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hu_internal hv hv_ne_attach hleft_contact transition
        htransition_outside htransition_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_pairwise_disjoint
        P T (j := j) (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order q hq_outside
    legs_meet_rims_only_at_attach := hincidence
  }⟩

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
