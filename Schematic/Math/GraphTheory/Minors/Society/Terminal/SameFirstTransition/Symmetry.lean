import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameFirstTransition.Construction
import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.OrderedTripodData

/-!
Orientation and last-arm symmetry corollaries for same-first-arm transitions.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/- Checked symmetry corollaries of the same-first transition constructor. -/

theorem GMIX24CutPath.reverse_supportIndex_lt_iff
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet) :
    Walk.supportIndex P.reverse.path x <
        Walk.supportIndex P.reverse.path y ↔
      Walk.supportIndex P.path y < Walk.supportIndex P.path x := by
  exact GeneralSociety.GMIX24CutPath.supportIndex_reverse_lt_iff P hx hy

/-- Right-boundary-arc form of the first-arm transition constructor.  The
theta geometry is unchanged; only the orientation used to certify the three
ambient boundary feet differs. -/
theorem Tripod.liftAllNilOfSameFirstArmTransition_rightArc
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
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim i) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> z = T.left) :
    Nonempty S.Tripod := by
  exact
    GMIX24SourceProof.Tripod.liftAllNilOfSameFirstArmTransition
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts q (Or.inr ha) hq_path hq_outside hq_clean
      hu hu_ne_attach hu_internal hv hv_ne_attach hleft_contact transition
      htransition_path htransition_outside htransition_clean htransition_q

/-- Last ordered-rim diagonal, obtained from the first-rim constructor by
reversing the induced cut path. -/
theorem Tripod.liftAllNilOfSameLastArmTransition
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
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu : u ∈ (T.rightToAttach k).support)
    (hu_ne_attach : u ≠ T.attach k)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim k))
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim k) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> z = T.left) :
    Nonempty S.Tripod := by
  let O : GeneralSociety.GMIX24CutPath.OrderedTripodData P T i j k :=
    ⟨hij, hik, hjk, hi, hj, hk, hij_order, hjk_order, hpath_contacts⟩
  let Orev := O.reverse
  apply GMIX24SourceProof.Tripod.liftAllNilOfSameFirstArmTransition_rightArc
    (i := k) (j := j) (k := i) (a := a) (u := u) (v := v) (q := q)
    (transition := transition)
    P.reverse T hgraph Orev.first_ne_middle Orev.first_ne_last
      Orev.middle_ne_last hlegs_nil
      Orev.first_mem_path Orev.middle_mem_path Orev.last_mem_path
      Orev.first_lt_middle Orev.middle_lt_last
      Orev.path_contacts
  · simpa using ha
  · exact hq_path
  · intro z hzq
    simpa using hq_outside z hzq
  · exact hq_clean
  · exact hu
  · exact hu_ne_attach
  · exact hu_internal
  · exact hv
  · exact hv_ne_attach
  · exact hleft_contact
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean
  · exact htransition_q

/-- Last ordered-rim first-intersection splice, obtained by reversing the cut
path and applying the first-rim splice. -/
theorem Tripod.liftAllNilOfSplicedSameLastArmTransition
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
    {a u c : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hu : u ∈ (T.rightToAttach k).support)
    (hu_ne_attach : u ≠ T.attach k)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim k))
    (bridge : S.graph.Walk u T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = u ∨ z = T.left)
    (tail : S.graph.Walk c a)
    (htail_path : tail.IsPath)
    (htail_outside : forall z : V, z ∈ tail.support -> z ∈ P.outside)
    (htail_clean : forall z : V, z ∈ tail.support ->
      z ∈ T.vertexSet -> False)
    (hc_bridge : c ∈ bridge.support)
    (hbridge_tail : forall z : V, z ∈ bridge.support ->
      z ∈ tail.support -> z = c) :
    Nonempty S.Tripod := by
  let O : GeneralSociety.GMIX24CutPath.OrderedTripodData P T i j k :=
    ⟨hij, hik, hjk, hi, hj, hk, hij_order, hjk_order, hpath_contacts⟩
  let Orev := O.reverse
  apply GMIX24SourceProof.Tripod.liftAllNilOfSplicedSameFirstArmTransition
    (i := k) (j := j) (k := i) (a := a) (u := u) (c := c)
    P.reverse T hgraph Orev.first_ne_middle Orev.first_ne_last
      Orev.middle_ne_last hlegs_nil
      Orev.first_mem_path Orev.middle_mem_path Orev.last_mem_path
      Orev.first_lt_middle Orev.middle_lt_last
      Orev.path_contacts
  · exact Or.inr (by simpa using ha)
  · exact hu
  · exact hu_ne_attach
  · exact hu_internal
  · exact hbridge_path
  · intro z hz
    simpa using hbridge_outside z hz
  · exact hbridge_clean
  · exact htail_path
  · intro z hz
    simpa using htail_outside z hz
  · exact htail_clean
  · exact hc_bridge
  · exact hbridge_tail



end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
