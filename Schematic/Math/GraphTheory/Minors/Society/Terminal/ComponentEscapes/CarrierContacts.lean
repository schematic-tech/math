import Schematic.Math.GraphTheory.Minors.Society.Terminal.Symmetry

/-!
Last-contact normalization for component-preserving carrier escapes.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Split a component-preserving escape at its last contact with the old
tripod carrier, retaining both the discarded prefix and the clean suffix.

The prefix is the carrier-to-carrier bridge used in the final common-end
rerouting.  The suffix is an `X -> Omega` path in the literal GM IX sense:
its only old-carrier vertex is its source.  Both pieces remain in the same
component of `G - V(P)`, and the original path is their concatenation. -/
theorem Tripod.exists_lastCarrierContactSplit_in_component
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    {v a : V}
    (q : S.graph.Walk v a)
    (hvT : v ∈ T.vertexSet)
    (hqPath : q.IsPath)
    (hqComponent : forall z : V, z ∈ q.support ->
      z ∈ induceComponentSupport (G := S.graph) C) :
    Exists fun x : V =>
      Exists fun hxq : x ∈ q.support =>
        x ∈ T.vertexSet ∧
          (q.takeUntil x hxq).IsPath ∧
          (q.dropUntil x hxq).IsPath ∧
          (forall z : V, z ∈ (q.takeUntil x hxq).support ->
            z ∈ induceComponentSupport (G := S.graph) C) ∧
          (forall z : V, z ∈ (q.dropUntil x hxq).support ->
            z ∈ induceComponentSupport (G := S.graph) C) ∧
          (forall z : V, z ∈ (q.dropUntil x hxq).support ->
            z ∈ T.vertexSet -> z = x) ∧
          (q.takeUntil x hxq).append (q.dropUntil x hxq) = q := by
  classical
  let carrier : Set V := T.vertexSet
  have hvCarrier : v ∈ carrier := by simpa [carrier] using hvT
  obtain ⟨x, hxq, hxCarrier, htailPath, htailClean,
      htailSubset, _htailCovers, _hxIndex⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath carrier hvCarrier
  refine ⟨x, hxq, by simpa [carrier] using hxCarrier,
    hqPath.takeUntil hxq, ?_, ?_, ?_, ?_, SimpleGraph.Walk.take_spec q hxq⟩
  · simpa using htailPath
  · intro z hz
    exact hqComponent z
      (SimpleGraph.Walk.support_takeUntil_subset q hxq hz)
  · intro z hz
    exact hqComponent z (htailSubset z hz)
  · intro z hzTail hzT
    exact htailClean z hzTail (by simpa [carrier] using hzT)

/-- The discarded prefix before a noninitial last carrier contact contains a
clean bridge between two distinct old-carrier vertices.

Reverse the prefix and stop at its first carrier vertex different from `x`.
Simplicity excludes a second occurrence of `x`, while first-contact
minimality excludes every other carrier vertex from the bridge interior.
This is the finite, recursive bridge step suppressed by "again it follows
easily" in the GM IX `(2.4)` proof. -/
theorem Tripod.exists_cleanCarrierBridge_before_contact
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    {v a x : V}
    (q : S.graph.Walk v a)
    (hvT : v ∈ T.vertexSet)
    (hqPath : q.IsPath)
    (hqComponent : forall z : V, z ∈ q.support ->
      z ∈ induceComponentSupport (G := S.graph) C)
    (hxq : x ∈ q.support)
    (hx_ne_v : x ≠ v) :
    Exists fun y : V =>
      Exists fun bridge : S.graph.Walk x y =>
        y ∈ T.vertexSet ∧ y ≠ x ∧ bridge.IsPath ∧
          (forall z : V, z ∈ bridge.support ->
            z ∈ induceComponentSupport (G := S.graph) C) ∧
          forall z : V, z ∈ bridge.support ->
            z ∈ T.vertexSet -> z = x ∨ z = y := by
  classical
  let pref : S.graph.Walk v x := q.takeUntil x hxq
  let backwards : S.graph.Walk x v := pref.reverse
  let otherCarrier : Set V := T.vertexSet \ {x}
  have hvOther : v ∈ otherCarrier := by
    exact ⟨hvT, by simpa [eq_comm] using hx_ne_v⟩
  have hbackwardsPath : backwards.IsPath := by
    simpa [backwards, pref] using (hqPath.takeUntil hxq).reverse
  obtain ⟨y, hyBackwards, hyOther, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem
      (G := S.graph) hbackwardsPath otherCarrier hvOther
  let bridge : S.graph.Walk x y := backwards.takeUntil y hyBackwards
  have hbridgeSubsetQ : forall z : V, z ∈ bridge.support -> z ∈ q.support := by
    intro z hz
    have hzBackwards : z ∈ backwards.support :=
      SimpleGraph.Walk.support_takeUntil_subset backwards hyBackwards
        (by simpa [bridge] using hz)
    have hzPrefix : z ∈ pref.support := by
      simpa [backwards, SimpleGraph.Walk.support_reverse] using hzBackwards
    exact SimpleGraph.Walk.support_takeUntil_subset q hxq
      (by simpa [pref] using hzPrefix)
  refine ⟨y, bridge, hyOther.1, ?_, ?_, ?_, ?_⟩
  · exact fun hyx => hyOther.2 (by simp [hyx])
  · simpa [bridge] using hbackwardsPath.takeUntil hyBackwards
  · intro z hz
    exact hqComponent z (hbridgeSubsetQ z hz)
  · intro z hzBridge hzT
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr
        (hfirst z (by simpa [bridge] using hzBridge) ⟨hzT, by simpa using hzx⟩)

/-- Normalize a component-preserving escape at its last contact with the old
tripod carrier.

This is the literal `X -> Omega` operation used in the quoted GM IX `(2.4)`
sentence.  The resulting suffix stays in the same outside component and has
no old-carrier vertex except its source. -/
theorem Tripod.exists_lastCarrierContactTail_in_component
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    {v a : V}
    (q : S.graph.Walk v a)
    (hvT : v ∈ T.vertexSet)
    (hqPath : q.IsPath)
    (hqComponent : forall z : V, z ∈ q.support ->
      z ∈ induceComponentSupport (G := S.graph) C) :
    Exists fun x : V =>
      Exists fun tail : S.graph.Walk x a =>
        x ∈ T.vertexSet ∧ tail.IsPath ∧
          (forall z : V, z ∈ tail.support ->
            z ∈ induceComponentSupport (G := S.graph) C) ∧
            forall z : V, z ∈ tail.support -> z ∈ T.vertexSet -> z = x := by
  obtain ⟨x, hxq, hxCarrier, _hprefixPath, htailPath,
      _hprefixComponent, htailComponent, htailClean, _hsplit⟩ :=
    Tripod.exists_lastCarrierContactSplit_in_component
      (S := S) (H := H) P T C q hvT hqPath hqComponent
  let tail : S.graph.Walk x a := q.dropUntil x hxq
  refine ⟨x, tail, hxCarrier, ?_, ?_, ?_⟩
  · simpa [tail] using htailPath
  · intro z hz
    exact htailComponent z (by simpa [tail] using hz)
  · intro z hzTail hzT
    exact htailClean z (by simpa [tail] using hzTail) hzT

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
