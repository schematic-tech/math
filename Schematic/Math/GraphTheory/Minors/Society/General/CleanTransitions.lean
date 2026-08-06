import Schematic.Math.GraphTheory.Minors.Society.General.TransitionCases

/-! Exhaustive dispatchers for carrier-clean transitions. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/- Source side-tripod paragraph for the left side of the canonical cut path.

The right side of `SideTripodObligations` is the same statement applied to
`P.reverse`, so the remaining source proof is kept in this one left-side
form.

This is intentionally the live proof obligation.  An earlier decomposition
asked for `BoundaryClean` of every raw side `Tripod`, but that is stronger
than the printed GM IX definition: the source linkage paths have the
`X -> Ω` cleanliness property, while the rim endpoints and all rim interiors
are not globally asserted to avoid the society boundary.  The correct target
is the direct contradiction paragraph: assume a side tripod, use its three
attachment paths to force its boundary feet onto the cut path, extract the
opposite-side path `Q`, and construct the forbidden ambient tripod. -/
/-- Exhaustive selected-first-arm dispatcher for one carrier-clean transition.
Every cell is one of the checked all-nil theta exchanges above. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndCleanTransition
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
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
    (hu_contact : u = T.right ∨
      (u ∈ Walk.InternalVertices (T.rim i) ∧
        u ∈ (T.rightToAttach i).support ∧ u ≠ T.attach i) ∨
      (u ∈ Walk.InternalVertices (T.rim j) ∧
        u ∈ (T.rightToAttach j).support ∧ u ≠ T.attach j) ∨
      (u ∈ Walk.InternalVertices (T.rim k) ∧
        u ∈ (T.rightToAttach k).support ∧ u ≠ T.attach k))
    (hv_contact : v = T.left ∨
      (v ∈ Walk.InternalVertices (T.rim i) ∧
        v ∈ (T.leftToAttach i).support ∧ v ≠ T.attach i) ∨
      (v ∈ Walk.InternalVertices (T.rim j) ∧
        v ∈ (T.leftToAttach j).support ∧ v ≠ T.attach j) ∨
      (v ∈ Walk.InternalVertices (T.rim k) ∧
        v ∈ (T.leftToAttach k).support ∧ v ≠ T.attach k))
    (hright_prefix_outside : forall (s : Fin 3) (w : V)
      (hw : w ∈ (T.rightToAttach s).support), w ≠ T.attach s ->
        forall z : V, z ∈ ((T.rightToAttach s).takeUntil w hw).support ->
          z ∈ P.outside)
    (hleft_prefix_outside : forall (s : Fin 3) (w : V)
      (hw : w ∈ (T.leftToAttach s).support), w ≠ T.attach s ->
        forall z : V, z ∈ ((T.leftToAttach s).takeUntil w hw).support ->
          z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (hcommon : u = T.right -> v = T.left -> Nonempty S.Tripod) :
    Nonempty S.Tripod := by
  have hright_mem (s : Fin 3) : T.right ∈ (T.rightToAttach s).support :=
    (T.rightToAttach s).start_mem_support
  have hleft_mem (s : Fin 3) : T.left ∈ (T.leftToAttach s).support :=
    (T.leftToAttach s).start_mem_support
  have hright_ne_attach (s : Fin 3) : T.right ≠ T.attach s := by
    intro h
    exact T.right_ne_boundary s
      (h.trans ((T.leg_nil_iff_boundary_eq_attach s).mp (hlegs_nil s)).symm)
  have hleft_ne_attach (s : Fin 3) : T.left ≠ T.attach s := by
    intro h
    exact T.left_ne_boundary s
      (h.trans ((T.leg_nil_iff_boundary_eq_attach s).mp (hlegs_nil s)).symm)
  have sameMiddle {u' v' : V}
      (hu : u' ∈ (T.rightToAttach j).support)
      (hu_ne : u' ≠ T.attach j)
      (hu_at : u' ∈ Walk.InternalVertices (T.rim j) ∨ u' = T.right)
      (hv : v' ∈ (T.leftToAttach j).support)
      (hv_ne : v' ≠ T.attach j)
      (hv_at : v' ∈ Walk.InternalVertices (T.rim j) ∨ v' = T.left)
      (t : S.graph.Walk u' v') (ht_path : t.IsPath)
      (ht_outside : forall z : V, z ∈ t.support -> z ∈ P.outside)
      (ht_clean : forall z : V, z ∈ t.support ->
        z ∈ T.vertexSet -> z = u' ∨ z = v') : Nonempty S.Tripod := by
    by_cases hinter : Exists fun z : V =>
        z ∈ t.support ∧ z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support
    · exact Tripod.liftAllNilOfOuterLeftArmResidualAndIntersectingSameMiddleTransition
        P T hgraph hij hik hjk (Or.inl rfl) hlegs_nil hi hj hk
        hij_order hjk_order hpath_contacts q hx_arm hx_ne_attach hx_internal
        ha hq_path hq_clean hq_prefix_outside hu hu_ne hu_at hv hv_ne hv_at
        t ht_path ht_outside ht_clean hinter
    · exact Tripod.liftAllNilOfOuterLeftArmResidualAndSameMiddleTransition
        P T hgraph hij hik hjk (Or.inl rfl) hlegs_nil hi hj hk
        hij_order hjk_order hpath_contacts q hx_arm hx_ne_attach hx_internal
        ha hq_path hq_clean hq_prefix_outside hu hu_ne hu_at hv hv_ne hv_at
        t ht_path ht_outside ht_clean (by
          intro z hzt hzq
          exact False.elim (hinter ⟨z, hzt, hzq⟩))
  have middleFirst {u' v' : V}
      (hu : u' ∈ (T.rightToAttach j).support)
      (hu_ne : u' ≠ T.attach j)
      (hu_at : u' ∈ Walk.InternalVertices (T.rim j) ∨ u' = T.right)
      (hv : v' ∈ (T.leftToAttach i).support)
      (hv_ne : v' ≠ T.attach i)
      (hv_int : v' ∈ Walk.InternalVertices (T.rim i))
      (t : S.graph.Walk u' v') (ht_path : t.IsPath)
      (ht_outside : forall z : V, z ∈ t.support -> z ∈ P.outside)
      (ht_clean : forall z : V, z ∈ t.support ->
        z ∈ T.vertexSet -> z = u' ∨ z = v') : Nonempty S.Tripod :=
    Tripod.liftAllNilOfOuterFirstLeftArmResidualAndMiddleToFirstTransition
      P T hgraph hij hik hjk (Or.inl rfl) hlegs_nil hi hj hk
      hij_order hjk_order hpath_contacts q hx_arm hx_ne_attach hx_internal
      ha hq_path hq_clean hq_prefix_outside hu hu_ne hu_at
      (hright_prefix_outside j u' hu hu_ne) hv hv_ne hv_int
      (hleft_prefix_outside i v' hv hv_ne) t ht_path ht_outside ht_clean
  have middleLast {u' v' : V}
      (hu : u' ∈ (T.rightToAttach j).support)
      (hu_ne : u' ≠ T.attach j)
      (hu_at : u' ∈ Walk.InternalVertices (T.rim j) ∨ u' = T.right)
      (hv : v' ∈ (T.leftToAttach k).support)
      (hv_ne : v' ≠ T.attach k)
      (hv_int : v' ∈ Walk.InternalVertices (T.rim k))
      (t : S.graph.Walk u' v') (ht_path : t.IsPath)
      (ht_outside : forall z : V, z ∈ t.support -> z ∈ P.outside)
      (ht_clean : forall z : V, z ∈ t.support ->
        z ∈ T.vertexSet -> z = u' ∨ z = v') : Nonempty S.Tripod :=
    Tripod.liftAllNilOfOuterFirstLeftArmResidualAndMiddleToLastTransition
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
      hq_prefix_outside hu hu_ne hu_at
      (hright_prefix_outside j u' hu hu_ne) hv hv_ne hv_int
      (hleft_prefix_outside k v' hv hv_ne) t ht_path ht_outside ht_clean
  rcases hu_contact with huRight | huI | huJ | huK
  · rcases hv_contact with hvLeft | hvI | hvJ | hvK
    · exact hcommon huRight hvLeft
    · exact middleFirst (by rw [huRight]; exact hright_mem j)
        (by simpa [huRight] using hright_ne_attach j) (Or.inr huRight)
        hvI.2.1 hvI.2.2 hvI.1 transition htransition_path
        htransition_outside htransition_clean
    · exact sameMiddle (by rw [huRight]; exact hright_mem j)
        (by simpa [huRight] using hright_ne_attach j) (Or.inr huRight)
        hvJ.2.1 hvJ.2.2 (Or.inl hvJ.1) transition htransition_path
        htransition_outside htransition_clean
    · exact middleLast (by rw [huRight]; exact hright_mem j)
        (by simpa [huRight] using hright_ne_attach j) (Or.inr huRight)
        hvK.2.1 hvK.2.2 hvK.1 transition htransition_path
        htransition_outside htransition_clean
  · rcases hv_contact with hvLeft | hvI | hvJ | hvK
    · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndSameFirstTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
        hq_prefix_outside huI.2.1 huI.2.2 huI.1
        (by rw [hvLeft]; exact hleft_mem i)
        (by simpa [hvLeft] using hleft_ne_attach i) (Or.inr hvLeft)
        transition htransition_path htransition_outside htransition_clean
    · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndSameFirstTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
        hq_prefix_outside huI.2.1 huI.2.2 huI.1 hvI.2.1 hvI.2.2
        (Or.inl hvI.1) transition htransition_path htransition_outside
        htransition_clean
    · by_cases hinter : Exists fun z : V =>
          z ∈ transition.support ∧
            z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support
      · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndIntersectingFirstToMiddleTransition
          P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
          hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
          hq_prefix_outside huI.2.1 huI.2.2 huI.1 hvJ.2.1 hvJ.2.2 hvJ.1
          transition htransition_path htransition_outside htransition_clean hinter
      · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndDisjointFirstToMiddleTransition
          P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
          hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path
          hq_clean hq_prefix_outside huI.2.1 huI.2.2 huI.1
          hvJ.2.1 hvJ.2.2 hvJ.1 transition htransition_path
          htransition_outside htransition_clean (by
            intro z hzt hzq
            exact hinter ⟨z, hzt, hzq⟩)
    · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndFirstToLastTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
        hq_prefix_outside huI.2.1 huI.2.2 huI.1 hvK.2.1 hvK.2.2 hvK.1
        (hleft_prefix_outside k v hvK.2.1 hvK.2.2) transition
        htransition_path htransition_outside htransition_clean
  · rcases hv_contact with hvLeft | hvI | hvJ | hvK
    · exact sameMiddle huJ.2.1 huJ.2.2 (Or.inl huJ.1)
        (by rw [hvLeft]; exact hleft_mem j)
        (by simpa [hvLeft] using hleft_ne_attach j) (Or.inr hvLeft)
        transition htransition_path htransition_outside htransition_clean
    · exact middleFirst huJ.2.1 huJ.2.2 (Or.inl huJ.1)
        hvI.2.1 hvI.2.2 hvI.1 transition htransition_path
        htransition_outside htransition_clean
    · exact sameMiddle huJ.2.1 huJ.2.2 (Or.inl huJ.1)
        hvJ.2.1 hvJ.2.2 (Or.inl hvJ.1) transition htransition_path
        htransition_outside htransition_clean
    · exact middleLast huJ.2.1 huJ.2.2 (Or.inl huJ.1)
        hvK.2.1 hvK.2.2 hvK.1 transition htransition_path
        htransition_outside htransition_clean
  · rcases hv_contact with hvLeft | hvI | hvJ | hvK
    · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndSameLastTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
        hq_prefix_outside huK.2.1 huK.2.2 huK.1
        (by rw [hvLeft]; exact hleft_mem k)
        (by simpa [hvLeft] using hleft_ne_attach k) (Or.inr hvLeft)
        transition htransition_path htransition_outside htransition_clean
    · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndLastToFirstTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
        hq_prefix_outside huK.2.1 huK.2.2 huK.1 hvI.2.1 hvI.2.2 hvI.1
        (hleft_prefix_outside i v hvI.2.1 hvI.2.2) transition
        htransition_path htransition_outside htransition_clean
    · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndLastToMiddleTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
        hq_prefix_outside huK.2.1 huK.2.2 huK.1 hvJ.2.1 hvJ.2.2 hvJ.1
        (hleft_prefix_outside j v hvJ.2.1 hvJ.2.2) transition
        htransition_path htransition_outside htransition_clean
    · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndSameLastTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
        hq_prefix_outside huK.2.1 huK.2.2 huK.1 hvK.2.1 hvK.2.2
        (Or.inl hvK.1) transition htransition_path htransition_outside
        htransition_clean

/-- The selected outer rim may be either end of the cut order. -/
theorem Tripod.liftAllNilOfOuterLeftArmResidualAndCleanTransition
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu_contact : u = T.right ∨
      (u ∈ Walk.InternalVertices (T.rim i) ∧
        u ∈ (T.rightToAttach i).support ∧ u ≠ T.attach i) ∨
      (u ∈ Walk.InternalVertices (T.rim j) ∧
        u ∈ (T.rightToAttach j).support ∧ u ≠ T.attach j) ∨
      (u ∈ Walk.InternalVertices (T.rim k) ∧
        u ∈ (T.rightToAttach k).support ∧ u ≠ T.attach k))
    (hv_contact : v = T.left ∨
      (v ∈ Walk.InternalVertices (T.rim i) ∧
        v ∈ (T.leftToAttach i).support ∧ v ≠ T.attach i) ∨
      (v ∈ Walk.InternalVertices (T.rim j) ∧
        v ∈ (T.leftToAttach j).support ∧ v ≠ T.attach j) ∨
      (v ∈ Walk.InternalVertices (T.rim k) ∧
        v ∈ (T.leftToAttach k).support ∧ v ≠ T.attach k))
    (hright_prefix_outside : forall (s : Fin 3) (w : V)
      (hw : w ∈ (T.rightToAttach s).support), w ≠ T.attach s ->
        forall z : V, z ∈ ((T.rightToAttach s).takeUntil w hw).support ->
          z ∈ P.outside)
    (hleft_prefix_outside : forall (s : Fin 3) (w : V)
      (hw : w ∈ (T.leftToAttach s).support), w ≠ T.attach s ->
        forall z : V, z ∈ ((T.leftToAttach s).takeUntil w hw).support ->
          z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (hcommon : u = T.right -> v = T.left -> Nonempty S.Tripod) :
    Nonempty S.Tripod := by
  let O : GeneralSociety.GMIX24CutPath.OrderedTripodData P T i j k :=
    ⟨hij, hik, hjk, hi, hj, hk, hij_order, hjk_order, hpath_contacts⟩
  let Orev := O.reverse
  rcases hr with rfl | rfl
  · exact Tripod.liftAllNilOfOuterFirstLeftArmResidualAndCleanTransition
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_clean
      hq_prefix_outside hu_contact hv_contact hright_prefix_outside
      hleft_prefix_outside transition htransition_path htransition_outside
      htransition_clean hcommon
  · have hu_reverse : u = T.right ∨
        (u ∈ Walk.InternalVertices (T.rim r) ∧
          u ∈ (T.rightToAttach r).support ∧ u ≠ T.attach r) ∨
        (u ∈ Walk.InternalVertices (T.rim j) ∧
          u ∈ (T.rightToAttach j).support ∧ u ≠ T.attach j) ∨
        (u ∈ Walk.InternalVertices (T.rim i) ∧
          u ∈ (T.rightToAttach i).support ∧ u ≠ T.attach i) := by
      rcases hu_contact with huRight | huI | huJ | huK
      · exact Or.inl huRight
      · exact Or.inr (Or.inr (Or.inr huI))
      · exact Or.inr (Or.inr (Or.inl huJ))
      · exact Or.inr (Or.inl huK)
    have hv_reverse : v = T.left ∨
        (v ∈ Walk.InternalVertices (T.rim r) ∧
          v ∈ (T.leftToAttach r).support ∧ v ≠ T.attach r) ∨
        (v ∈ Walk.InternalVertices (T.rim j) ∧
          v ∈ (T.leftToAttach j).support ∧ v ≠ T.attach j) ∨
        (v ∈ Walk.InternalVertices (T.rim i) ∧
          v ∈ (T.leftToAttach i).support ∧ v ≠ T.attach i) := by
      rcases hv_contact with hvLeft | hvI | hvJ | hvK
      · exact Or.inl hvLeft
      · exact Or.inr (Or.inr (Or.inr hvI))
      · exact Or.inr (Or.inr (Or.inl hvJ))
      · exact Or.inr (Or.inl hvK)
    apply Tripod.liftAllNilOfOuterFirstLeftArmResidualAndCleanTransition
      P.reverse T hgraph Orev.first_ne_middle Orev.first_ne_last
      Orev.middle_ne_last hlegs_nil
      Orev.first_mem_path Orev.middle_mem_path Orev.last_mem_path
      Orev.first_lt_middle Orev.middle_lt_last
      Orev.path_contacts
    · exact hx_ne_attach
    · exact hx_internal
    · rcases ha with ha | ha
      · exact Or.inr (by simpa using ha)
      · exact Or.inl (by simpa using ha)
    · exact hq_path
    · exact hq_clean
    · intro z hz
      simpa using hq_prefix_outside z hz
    · exact hu_reverse
    · exact hv_reverse
    · intro s w hw hne z hz
      simpa using hright_prefix_outside s w hw hne z hz
    · intro s w hw hne z hz
      simpa using hleft_prefix_outside s w hw hne z hz
    · exact htransition_path
    · intro z hz
      simpa using htransition_outside z hz
    · exact htransition_clean
    · exact hcommon

/-- Flip-symmetric exhaustive dispatcher for a selected outer right arm. -/
theorem Tripod.liftAllNilOfOuterRightArmResidualAndCleanTransition
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
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.attachToRight r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hu_contact : u = T.right ∨
      (u ∈ Walk.InternalVertices (T.rim i) ∧
        u ∈ (T.rightToAttach i).support ∧ u ≠ T.attach i) ∨
      (u ∈ Walk.InternalVertices (T.rim j) ∧
        u ∈ (T.rightToAttach j).support ∧ u ≠ T.attach j) ∨
      (u ∈ Walk.InternalVertices (T.rim k) ∧
        u ∈ (T.rightToAttach k).support ∧ u ≠ T.attach k))
    (hv_contact : v = T.left ∨
      (v ∈ Walk.InternalVertices (T.rim i) ∧
        v ∈ (T.leftToAttach i).support ∧ v ≠ T.attach i) ∨
      (v ∈ Walk.InternalVertices (T.rim j) ∧
        v ∈ (T.leftToAttach j).support ∧ v ≠ T.attach j) ∨
      (v ∈ Walk.InternalVertices (T.rim k) ∧
        v ∈ (T.leftToAttach k).support ∧ v ≠ T.attach k))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (hcommon : u = T.right -> v = T.left -> Nonempty S.Tripod) :
    Nonempty S.Tripod := by
  let U := T.flip
  let hgraph :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  have hx_U_arm : x ∈ (U.leftToAttach r).support := by
    have hx_right : x ∈ (T.rightToAttach r).support := by
      simpa [Tripod.rightToAttach, SimpleGraph.Walk.support_reverse] using hx_arm
    have hx_drop : x ∈
        ((T.rim r).dropUntil (T.attach r) (T.attach_mem_rim r).1).support := by
      simpa [Tripod.rightToAttach, Tripod.attachToRight,
        SimpleGraph.Walk.support_reverse] using hx_right
    have hattach_rev : T.attach r ∈ (T.rim r).reverse.support := by
      simpa [SimpleGraph.Walk.support_reverse] using (T.attach_mem_rim r).1
    have hx_rev_take : x ∈
        ((T.rim r).reverse.takeUntil (T.attach r) hattach_rev).support :=
      Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
        (T.rim_isPath r) (T.attach_mem_rim r).1 hattach_rev hx_drop
    simpa [U, Tripod.leftToAttach, Tripod.flip] using hx_rev_take
  have hpath_contacts_U : forall z : V, z ∈ P.pathSet -> z ∈ U.vertexSet ->
      Exists fun m : Fin 3 => z = U.boundary m := by
    intro z hzPath hzU
    rcases hpath_contacts z hzPath (by simpa [U] using hzU) with ⟨m, hm⟩
    exact ⟨m, by simpa [U] using hm⟩
  have hu_U : v = U.right ∨
      (v ∈ Walk.InternalVertices (U.rim i) ∧
        v ∈ (U.rightToAttach i).support ∧ v ≠ U.attach i) ∨
      (v ∈ Walk.InternalVertices (U.rim j) ∧
        v ∈ (U.rightToAttach j).support ∧ v ≠ U.attach j) ∨
      (v ∈ Walk.InternalVertices (U.rim k) ∧
        v ∈ (U.rightToAttach k).support ∧ v ≠ U.attach k) := by
    rcases hv_contact with hvLeft | hvI | hvJ | hvK
    · exact Or.inl (by simpa [U] using hvLeft)
    · exact Or.inr (Or.inl ⟨by
          simpa [U, Walk.internalVertices_reverse] using hvI.1,
        by simpa [U] using
          (Tripod.mem_flip_rightToAttach_of_mem_leftToAttach T hvI.2.1),
        by simpa [U] using hvI.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by
          simpa [U, Walk.internalVertices_reverse] using hvJ.1,
        by simpa [U] using
          (Tripod.mem_flip_rightToAttach_of_mem_leftToAttach T hvJ.2.1),
        by simpa [U] using hvJ.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by
          simpa [U, Walk.internalVertices_reverse] using hvK.1,
        by simpa [U] using
          (Tripod.mem_flip_rightToAttach_of_mem_leftToAttach T hvK.2.1),
        by simpa [U] using hvK.2.2⟩))
  have hv_U : u = U.left ∨
      (u ∈ Walk.InternalVertices (U.rim i) ∧
        u ∈ (U.leftToAttach i).support ∧ u ≠ U.attach i) ∨
      (u ∈ Walk.InternalVertices (U.rim j) ∧
        u ∈ (U.leftToAttach j).support ∧ u ≠ U.attach j) ∨
      (u ∈ Walk.InternalVertices (U.rim k) ∧
        u ∈ (U.leftToAttach k).support ∧ u ≠ U.attach k) := by
    rcases hu_contact with huRight | huI | huJ | huK
    · exact Or.inl (by simpa [U] using huRight)
    · exact Or.inr (Or.inl ⟨by
          simpa [U, Walk.internalVertices_reverse] using huI.1,
        by simpa [U] using
          (Tripod.mem_flip_leftToAttach_of_mem_rightToAttach T huI.2.1),
        by simpa [U] using huI.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by
          simpa [U, Walk.internalVertices_reverse] using huJ.1,
        by simpa [U] using
          (Tripod.mem_flip_leftToAttach_of_mem_rightToAttach T huJ.2.1),
        by simpa [U] using huJ.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by
          simpa [U, Walk.internalVertices_reverse] using huK.1,
        by simpa [U] using
          (Tripod.mem_flip_leftToAttach_of_mem_rightToAttach T huK.2.1),
        by simpa [U] using huK.2.2⟩))
  apply Tripod.liftAllNilOfOuterLeftArmResidualAndCleanTransition
    P U hgraph hij hik hjk hr (fun s => by simpa [U] using hlegs_nil s)
    (by simpa [U] using hi) (by simpa [U] using hj)
    (by simpa [U] using hk) (by simpa [U] using hij_order)
    (by simpa [U] using hjk_order) hpath_contacts_U q hx_U_arm
    (by simpa [U] using hx_ne_attach)
    (by simpa [U, Walk.internalVertices_reverse] using hx_internal)
    ha hq_path
    (by
      intro z hzq hzU
      exact hq_clean z hzq (by simpa [U] using hzU))
    (by
      simpa [U, hgraph] using
        GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
          P hno_cross U hpath_contacts_U hx_U_arm
          (by simpa [U] using hx_ne_attach) q hq_outside)
    hu_U hv_U
    (fun s w hw hne =>
      GMIX24Split.canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
        P hno_cross U hpath_contacts_U hw hne)
    (fun s w hw hne =>
      GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
        P hno_cross U hpath_contacts_U hw hne)
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
    (by
      intro hvLeft huRight
      apply hcommon
      · simpa [U] using huRight
      · simpa [U] using hvLeft)

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
