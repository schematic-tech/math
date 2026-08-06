import Schematic.Math.GraphTheory.Minors.Society.RuralGluing

/-!
Common transport lemmas for reversing a tripod's rims.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- Collapsed legs are invariant under reversal of the tripod rims. -/
theorem Tripod.legsNil_flip
    {H : GeneralSociety V}
    (T : H.Tripod)
    (hlegs : forall r : Fin 3, (T.leg r).Nil) :
    forall r : Fin 3, (T.flip.leg r).Nil := by
  intro r
  simpa using hlegs r

/-- A normalized set of tripod boundary contacts is invariant under reversal
of the tripod rims. -/
theorem Tripod.pathContacts_flip
    {H : GeneralSociety V}
    (T : H.Tripod)
    {X : Set V}
    (hcontacts : forall z : V, z ∈ X -> z ∈ T.vertexSet ->
      Exists fun r : Fin 3 => z = T.boundary r) :
    forall z : V, z ∈ X -> z ∈ T.flip.vertexSet ->
      Exists fun r : Fin 3 => z = T.flip.boundary r := by
  intro z hzX hzFlip
  simpa using hcontacts z hzX (by simpa using hzFlip)

/-- Carrier-cleanliness of a walk is invariant under reversal of the tripod
rims. -/
theorem Tripod.supportClean_flip
    {G : SimpleGraph V}
    {H : GeneralSociety V}
    (T : H.Tripod)
    {a b x : V}
    (q : G.Walk a b)
    (hclean : forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    forall z : V, z ∈ q.support -> z ∈ T.flip.vertexSet -> z = x := by
  intro z hzq hzFlip
  exact hclean z hzq (by simpa using hzFlip)

namespace GMIX24SourceProof

/-- The left arm of a tripod is the right arm after reversing all rims. -/
theorem Tripod.mem_flip_rightToAttach_of_mem_leftToAttach
    [DecidableEq V]
    {H : GeneralSociety V}
    (T : H.Tripod) {s : Fin 3} {z : V}
    (hz : z ∈ (T.leftToAttach s).support) :
    z ∈ (T.flip.rightToAttach s).support := by
  have hattach_rev :
      T.attach s ∈ (T.rim s).reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using (T.attach_mem_rim s).1
  have hzDrop :
      z ∈ ((T.rim s).reverse.dropUntil (T.attach s) hattach_rev).support :=
    Walk.IsPath.mem_reverse_dropUntil_of_mem_takeUntil
      (T.rim_isPath s) (T.attach_mem_rim s).1 hattach_rev hz
  have hzAttachToRight : z ∈ (T.flip.attachToRight s).support := by
    simpa [Tripod.flip, Tripod.attachToRight] using hzDrop
  simpa [Tripod.rightToAttach,
    SimpleGraph.Walk.support_reverse] using hzAttachToRight

/-- The right arm of a tripod is the left arm after reversing all rims. -/
theorem Tripod.mem_flip_leftToAttach_of_mem_rightToAttach
    [DecidableEq V]
    {H : GeneralSociety V}
    (T : H.Tripod) {s : Fin 3} {z : V}
    (hz : z ∈ (T.rightToAttach s).support) :
    z ∈ (T.flip.leftToAttach s).support := by
  have hzDrop :
      z ∈ ((T.rim s).dropUntil (T.attach s)
        (T.attach_mem_rim s).1).support := by
    simpa [Tripod.rightToAttach, Tripod.attachToRight,
      SimpleGraph.Walk.support_reverse] using hz
  have hattach_rev :
      T.attach s ∈ (T.rim s).reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using (T.attach_mem_rim s).1
  have hzTake :
      z ∈ ((T.rim s).reverse.takeUntil (T.attach s) hattach_rev).support :=
    Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
      (T.rim_isPath s) (T.attach_mem_rim s).1 hattach_rev hzDrop
  simpa [Tripod.flip, Tripod.leftToAttach] using hzTake

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
