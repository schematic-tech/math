import Schematic.Math.GraphTheory.Minors.Society.General.MiddleToFirstTransition

/-! The middle-to-last transition obtained by reversing the cut order. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Median-right to last-left exchange with the selected escape on the
opposite first rim.  After reversing the cut order this is the generalized
median-to-first last-contact theorem with its selected rim set to the other
outer index. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndMiddleToLastTransition
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
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact : u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hright_prefix_outside : forall z : V,
      z ∈ ((T.rightToAttach j).takeUntil u hu).support -> z ∈ P.outside)
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (hleft_prefix_outside : forall z : V,
      z ∈ ((T.leftToAttach k).takeUntil v hv).support -> z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Nonempty S.Tripod := by
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndMiddleToFirstTransition
      (i := k) (j := j) (k := i) (r := i) (q := q) (hx_arm := hx_arm)
      (u := u) (v := v) (hu := hu) (hv := hv) (transition := transition)
      P.reverse T hgraph
      (fun h => hjk h.symm) (fun h => hik h.symm) (fun h => hij h.symm)
      (Or.inr rfl) hlegs_nil
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
  · intro z hz
    simpa using hq_prefix_outside z hz
  · exact hu_ne_attach
  · exact hright_contact
  · intro z hz
    simpa using hright_prefix_outside z hz
  · exact hv_ne_attach
  · exact hv_internal
  · intro z hz
    simpa using hleft_prefix_outside z hz
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
