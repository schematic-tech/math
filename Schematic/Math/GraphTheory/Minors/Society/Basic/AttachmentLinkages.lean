import Schematic.Math.GraphTheory.Minors.Society.Basic.ComponentBoundaries
import Schematic.Math.GraphTheory.Minors.Rerouting.Extensions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The GM IX `(2.2)` augmentation applied to the three attachment vertices
of a tripod.

The attachments are distinct because they lie in pairwise disjoint interiors
of the three rim paths.  They are active because every rim is a nontrivial
walk in the society graph.  Society three-connectivity and finite Menger
therefore supply three mutually vertex-disjoint paths from the attachments to
three society-boundary vertices.  Pairwise disjointness also forces the chosen
boundary vertices to be distinct.

This is the linkage used in the common-end paragraph of GM IX `(2.4)`;
subsequent contact normalization truncates its paths at their last contacts
with the old tripod carrier. -/
theorem ThreeConnected.hasTripodAttachmentLinkageToBoundary
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (T : S.Tripod) :
    HasThreeVertexLinkageToSet S.graph T.attach S.boundarySet := by
  apply hthree.hasThreeVertexLinkageToBoundary
  · intro i j hij
    by_contra hne
    exact (T.attach_ne_of_ne hne) hij
  · intro i
    exact Or.inl
      (T.rim_support_subset_graph_support i (T.attach_mem_rim i).1)

/-- Ambient form of `hasTripodAttachmentLinkageToBoundary`.

Here the tripod belongs to a sub-society `H`, while the augmenting linkage is
constructed in a three-connected ambient society `S`.  This is the exact type
of the side-tripod application in GM IX `(2.4)`. -/
theorem ThreeConnected.hasMappedTripodAttachmentLinkageToBoundary
    [Fintype V] [DecidableEq V]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph) :
    HasThreeVertexLinkageToSet S.graph T.attach S.boundarySet := by
  apply hthree.hasThreeVertexLinkageToBoundary
  · intro i j hij
    by_contra hne
    exact (T.attach_ne_of_ne hne) hij
  · intro i
    left
    rw [SimpleGraph.mem_support]
    have hsupport :
        T.attach i ∈ H.graph.support :=
      T.rim_support_subset_graph_support i (T.attach_mem_rim i).1
    rw [SimpleGraph.mem_support] at hsupport
    rcases hsupport with ⟨w, hiw⟩
    exact ⟨w, hgraph hiw⟩

/--
Complete the attachment linkage of a side tripod to the ambient boundary while
retaining one side-tripod foot that is already an ambient boundary vertex.

This is the direct one-selected-pair application of GM IX `(2.2)` in the
side-tripod paragraph of `(2.4)`.  The original leg supplies the selected
partial linkage.  Ambient three-connectivity supplies an unrestricted full
linkage from the same three attachments to the ambient boundary, and the
endpoint-preserving augmentation theorem combines the two.
-/
theorem ThreeConnected.hasMappedTripodAttachmentLinkageToBoundary_preserving_foot
    [Fintype V] [DecidableEq V]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (r : Fin 3)
    (hrBoundary : T.boundary r ∈ S.boundarySet)
    (hrTargetClean :
      forall z : V,
        z ∈ (T.leg r).support ->
          z ∈ S.boundarySet -> z = T.boundary r) :
    let carrier : Set V :=
      {z : V | Exists fun i : Fin 3 => z ∈ (T.rim i).support}
    Exists fun M : ThreeSetLinkage S.graph carrier S.boundarySet =>
      T.attach r ∈ Set.range M.source ∧
        T.boundary r ∈ Set.range M.target := by
  classical
  let carrier : Set V :=
    {z : V | Exists fun i : Fin 3 => z ∈ (T.rim i).support}
  rcases hthree.hasMappedTripodAttachmentLinkageToBoundary T hgraph with
    ⟨fullRight, hfullBoundary, ⟨Lfull⟩⟩
  let F : ThreeSetLinkage S.graph carrier S.boundarySet :=
    Lfull.toThreeSetLinkage carrier S.boundarySet
      (by
        intro i
        exact ⟨i, Walk.internalVertices_subset_support
          (T.rim i) (T.attach_mem_rim i)⟩)
      hfullBoundary
  let p : S.graph.Walk (T.attach r) (T.boundary r) :=
    (T.leg r).mapLe hgraph
  have hp : p.IsPath := by
    simpa [p] using
      (SimpleGraph.Walk.mapLe_isPath hgraph).mpr (T.leg_isPath r)
  have hpSourceClean :
      forall z : V,
        z ∈ p.support -> z ∈ carrier -> z = T.attach r := by
    intro z hz ⟨i, hzi⟩
    exact T.legs_meet_rims_only_at_attach r i z
      (by simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hz)
      hzi
  have hpTargetClean :
      forall z : V,
        z ∈ p.support -> z ∈ S.boundarySet -> z = T.boundary r := by
    intro z hz hzBoundary
    exact hrTargetClean z
      (by simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hz)
      hzBoundary
  let Lselected : PartialSetLinkage S.graph carrier S.boundarySet 1 :=
    PartialSetLinkage.ofOnePath p hp
      ⟨r, Walk.internalVertices_subset_support
        (T.rim r) (T.attach_mem_rim r)⟩
      hrBoundary hpSourceClean hpTargetClean
  rcases
      Lselected.exists_threeSetLinkage_extending (by omega) F with
    ⟨M, hsourceSelected, htargetSelected⟩
  refine ⟨M, hsourceSelected ?_, htargetSelected ?_⟩
  · exact ⟨0, rfl⟩
  · exact ⟨0, rfl⟩


end GeneralSociety

end Schematic.Math.GraphTheory
