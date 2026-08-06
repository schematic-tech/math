import Schematic.Math.GraphTheory.Minors.Society.Terminal.FirstToLastTransition
import Schematic.Math.GraphTheory.Minors.Society.Terminal.FirstToMiddleTransition
import Schematic.Math.GraphTheory.Minors.Society.Terminal.MiddleToFirstTransition

/-!
Endpoint cases for clean all-nil transitions.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

theorem Tripod.liftAllNilOfRightEndpointToLastArmTransition
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
    {a v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk T.right v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  exact Tripod.liftAllNilOfFirstToLastArmTransition
    P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
    hpath_contacts q ha hq_path hq_outside hq_clean
    (T.rightToAttach i).start_mem_support (Or.inr rfl)
    hv hv_ne_attach hv_internal transition htransition_path
    htransition_outside htransition_clean htransition_q

theorem Tripod.liftAllNilOfRightEndpointToFirstArmTransition
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
    {a v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim i))
    (transition : S.graph.Walk T.right v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  let O : GeneralSociety.GMIX24CutPath.OrderedTripodData P T i j k :=
    ⟨hij, hik, hjk, hi, hj, hk, hij_order, hjk_order, hpath_contacts⟩
  let Orev := O.reverse
  apply Tripod.liftAllNilOfRightEndpointToLastArmTransition
    (i := k) (j := j) (k := i) (a := a) (v := v)
    (q := q) (transition := transition)
    P.reverse T hgraph Orev.first_ne_middle Orev.first_ne_last
      Orev.middle_ne_last hlegs_nil
      Orev.first_mem_path Orev.middle_mem_path Orev.last_mem_path
      Orev.first_lt_middle Orev.middle_lt_last
      Orev.path_contacts
  · rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl (by simpa using ha)
  · exact hq_path
  · intro z hzq
    simpa using hq_outside z hzq
  · exact hq_clean
  · exact hv
  · exact hv_ne_attach
  · exact hv_internal
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean
  · exact htransition_q

theorem Tripod.liftAllNilOfRightEndpointToMiddleArmTransition
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
    {a v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk T.right v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  have hright_ne_attach : T.right ≠ T.attach j := by
    intro h
    exact T.right_ne_boundary j
      (h.trans ((T.leg_nil_iff_boundary_eq_attach j).mp (hlegs_nil j)).symm)
  exact Tripod.liftAllNilOfSameMiddleArmTransition
    P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
    hpath_contacts q ha hq_path hq_outside hq_clean
    (T.rightToAttach j).start_mem_support hright_ne_attach (Or.inr rfl)
    hv hv_ne_attach (Or.inl hv_internal) transition htransition_path
    htransition_outside htransition_clean
    (fun z hzTransition hzQ => False.elim (htransition_q z hzTransition hzQ))



end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
