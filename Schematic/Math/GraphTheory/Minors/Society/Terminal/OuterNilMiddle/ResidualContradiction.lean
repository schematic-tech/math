import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle.ResidualLifts

/-!
Elimination of the complete outer-nil, middle-non-nil residual branch.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- The complete double-outer-collapsed residual is impossible whenever the
ordered middle leg is nontrivial.  Common-end starts use the direct endpoint
constructors; internal outer-rim starts are normalized to one of the two rim
arms and use the prefixed-tail constructors above. -/
theorem outerNilMiddleNonNil_residual_impossible
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
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
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) -> z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    False := by
  have hall : forall r : Fin 3, T.boundary r ∈ P.pathSet := by
    intro r
    rcases fin3_eq_of_pairwise (m := r) hij hik hjk with rfl | hr
    · exact hi
    · rcases hr with rfl | rfl
      · exact hj
      · exact hk
  have hq_clean_vertex :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x := by
    intro z hzq hzT
    exact hq_clean z hzq (by
      rcases hzT with hzRim | hzLeg
      · rcases hzRim with ⟨r, hr⟩
        exact ⟨r, Or.inl hr⟩
      · rcases hzLeg with ⟨r, hr⟩
        exact ⟨r, Or.inr hr⟩)
  rcases hresidual with hend | hnil
  · rcases hend with rfl | rfl
    · exact hno_tripod
        (GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilCommonLeft
          P T (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
          hij hik hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
          hi hj hk hij_order hjk_order ha q hq_path hq_outside
          hq_clean_vertex hpath_contacts)
    · exact hno_tripod
        (GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilCommonRight
          P T (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
          hij hik hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
          hi hj hk hij_order hjk_order ha q hq_path hq_outside
          hq_clean_vertex hpath_contacts)
  · rcases
        GMIX24Split.tripod_leg_nil_residual_arm_of_outside
          P T q hall hq_outside hnil with
      ⟨r, hr, hxInternal, _hlegRNil, hxNeAttach, harm⟩
    rcases harm with hleft | hright
    · exact hno_tripod
        (GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilLeftArmResidual
          P hno_cross T hij hik hjk hr hleg_i_nil hleg_j_not_nil hleg_k_nil
          hi hj hk hij_order hjk_order hpath_contacts q hleft.1 hxNeAttach
          hxInternal ha hq_path hq_outside hq_clean_vertex)
    · exact hno_tripod
        (GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilRightArmResidual
          P hno_cross T hij hik hjk hr hleg_i_nil hleg_j_not_nil hleg_k_nil
          hi hj hk hij_order hjk_order hpath_contacts q hright.1 hxNeAttach
          hxInternal ha hq_path hq_outside hq_clean_vertex)

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
