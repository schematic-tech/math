import Schematic.Math.GraphTheory.Minors.Society.Basic.AttachmentLinkages
import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.TripodLinkages

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- Simultaneous last-contact data for a linkage from the three attachments of
a tripod.

For each linkage path, `contact i` is its last vertex on the old tripod
carrier.  The suffix beginning there is consequently clean with respect to
the entire carrier.  Keeping all three contacts in one object lets the
pairwise-disjointness of the original Menger linkage be reused without
independent choices. -/
structure TripodAttachmentLinkageLastContacts
    [DecidableEq V]
    {S H : GeneralSociety V}
    (T : H.Tripod)
    {right : Fin 3 -> V}
    (L : ThreeVertexLinkage S.graph T.attach right) where
  contact : Fin 3 -> V
  contact_mem_path :
    forall i : Fin 3, contact i ∈ (L.path i).support
  contact_mem_carrier :
    forall i : Fin 3,
      Exists fun r : Fin 3 => contact i ∈ (T.rim r).support
  tail :
    forall i : Fin 3,
      S.graph.Walk (contact i) (right (L.targetEquiv i))
  tail_isPath :
    forall i : Fin 3, (tail i).IsPath
  tail_support_subset_path :
    forall i : Fin 3, forall z : V,
      z ∈ (tail i).support -> z ∈ (L.path i).support
  tail_index_bound :
    forall i : Fin 3, forall z : V,
      z ∈ (tail i).support ->
        Walk.supportIndex (L.path i) (contact i) <=
          Walk.supportIndex (L.path i) z
  tail_clean :
    forall i : Fin 3, forall z : V,
      z ∈ (tail i).support ->
        (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
          z = contact i

namespace TripodAttachmentLinkageLastContacts

variable [DecidableEq V]

/-- The prefix of the `i`th augmenting path from its prescribed old tripod
attachment to its last contact with the old theta carrier. -/
def pathPrefix
    {S H : GeneralSociety V}
    {T : H.Tripod}
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    (i : Fin 3) :
    S.graph.Walk (T.attach i) (D.contact i) :=
  (L.path i).takeUntil (D.contact i) (D.contact_mem_path i)

theorem prefix_isPath
    {S H : GeneralSociety V}
    {T : H.Tripod}
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    (i : Fin 3) :
    (D.pathPrefix i).IsPath := by
  exact (L.isPath i).takeUntil (D.contact_mem_path i)

theorem prefix_support_subset_path
    {S H : GeneralSociety V}
    {T : H.Tripod}
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    (i : Fin 3) {z : V}
    (hz : z ∈ (D.pathPrefix i).support) :
    z ∈ (L.path i).support := by
  exact
    SimpleGraph.Walk.support_takeUntil_subset
      (L.path i) (D.contact_mem_path i) hz

theorem prefixes_pairwise_disjoint
    {S H : GeneralSociety V}
    {T : H.Tripod}
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    {i j : Fin 3} (hij : i ≠ j) :
    Disjoint {z : V | z ∈ (D.pathPrefix i).support}
      {z : V | z ∈ (D.pathPrefix j).support} := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  exact
    Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij)
      (D.prefix_support_subset_path i hzi)
      (D.prefix_support_subset_path j hzj)

/-- A fixed-start prefix and its last-contact suffix meet only at their common
contact.  This is the splice condition used in every theta rerouting case. -/
theorem prefix_meets_tail_only_at_contact
    {S H : GeneralSociety V}
    {T : H.Tripod}
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    (i : Fin 3) {z : V}
    (hzPrefix : z ∈ (D.pathPrefix i).support)
    (hzTail : z ∈ (D.tail i).support) :
    z = D.contact i := by
  have hzPath : z ∈ (L.path i).support :=
    D.tail_support_subset_path i z hzTail
  have hzLe :
      Walk.supportIndex (L.path i) z <=
        Walk.supportIndex (L.path i) (D.contact i) :=
    Walk.idxOf_le_of_mem_takeUntil (D.contact_mem_path i) hzPrefix
  have hcontactLe :
      Walk.supportIndex (L.path i) (D.contact i) <=
        Walk.supportIndex (L.path i) z :=
    D.tail_index_bound i z hzTail
  have hindex :
      Walk.supportIndex (L.path i) z =
        Walk.supportIndex (L.path i) (D.contact i) :=
    Nat.le_antisymm hzLe hcontactLe
  exact (List.idxOf_inj hzPath).mp hindex

theorem contact_injective
    {S H : GeneralSociety V}
    {T : H.Tripod}
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L) :
    Function.Injective D.contact := by
  intro i j hij
  by_contra hne
  exact
    Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hne)
      (D.contact_mem_path i)
      (by simpa [hij] using D.contact_mem_path j)

/-- The three clean suffixes are still a three-vertex linkage. -/
def toLinkage
    {S H : GeneralSociety V}
    {T : H.Tripod}
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L) :
    ThreeVertexLinkage S.graph D.contact right where
  targetEquiv := L.targetEquiv
  path := D.tail
  isPath := D.tail_isPath
  pairwise_vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact
      Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij)
        (D.tail_support_subset_path i z hzi)
        (D.tail_support_subset_path j z hzj)

theorem tail_meets_carrier_only_at_contact
    {S H : GeneralSociety V}
    {T : H.Tripod}
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    (i : Fin 3) (z : V)
    (hz_tail : z ∈ (D.tail i).support)
    (hz_carrier :
      Exists fun r : Fin 3 => z ∈ (T.rim r).support) :
    z = D.contact i :=
  D.tail_clean i z hz_tail hz_carrier

/--
If the three last contacts of an ambient boundary linkage lie in three
distinct old rim interiors, they are already the attachments of an ambient
tripod.

This is the generic branch of the carrier rerouting in GM IX `(2.4)`.  The
clean suffixes meet the old theta only at their initial contacts, while
injectivity of `e` assigns one contact to each distinct rim.
-/
def toAmbientTripodOfDistinctRimContacts
    {S H : GeneralSociety V}
    {T : H.Tripod}
    (hgraph : H.graph ≤ S.graph)
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    (hrightBoundary : forall i : Fin 3, right i ∈ S.boundarySet)
    (e : Fin 3 -> Fin 3)
    (he : Function.Injective e)
    (hcontact :
      forall i : Fin 3,
        D.contact i ∈ Walk.InternalVertices (T.rim (e i))) :
    S.Tripod := by
  let rim : Fin 3 -> S.graph.Walk T.left T.right :=
    fun i => (T.rim (e i)).mapLe hgraph
  apply
    Tripod.ofThreeVertexLinkage
      T.left T.right T.left_ne_right rim
      (fun i => by
        simpa [rim] using
          (SimpleGraph.Walk.mapLe_isPath hgraph).mpr (T.rim_isPath (e i)))
      D.contact
      (fun i => by
        simpa [rim, Walk.InternalVertices,
          SimpleGraph.Walk.support_mapLe_eq_support] using hcontact i)
      right hrightBoundary L.right_injective D.toLinkage
  · intro i j hij
    simpa [rim, Walk.InternalVertices,
      SimpleGraph.Walk.support_mapLe_eq_support] using
      T.rim_internals_disjoint (e i) (e j) (fun h => hij (he h))
  · intro i j z hzTail hzRim
    apply D.tail_clean i z hzTail
    exact ⟨e j, by
      simpa [rim, SimpleGraph.Walk.support_mapLe_eq_support] using hzRim⟩

theorem exists_non_distinct_rim_contact_of_no_ambient_tripod
    {S H : GeneralSociety V}
    {T : H.Tripod}
    (hgraph : H.graph ≤ S.graph)
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    (hrightBoundary : forall i : Fin 3, right i ∈ S.boundarySet)
    (hno_tripod : Not (Nonempty S.Tripod)) :
    forall e : Fin 3 -> Fin 3,
      Function.Injective e ->
        Exists fun i : Fin 3 =>
          D.contact i ∉ Walk.InternalVertices (T.rim (e i)) := by
  intro e he
  by_contra hall
  push Not at hall
  exact hno_tripod
    ⟨D.toAmbientTripodOfDistinctRimContacts
      hgraph hrightBoundary e he hall⟩

/--
The exact residual after the generic distinct-rim branch: either a clean
suffix starts at one of the two common ends of the old theta, or two distinct
suffixes have their last rim contacts in the same old branch.

This is the formal carrier-contact dichotomy behind the source sentence
"then `Q,P₁,P₂,P₃` have a common end".  Every rim contact is internal or a
common end.  If the three internal contacts belonged to three distinct rims,
`toAmbientTripodOfDistinctRimContacts` would already contradict the ambient
no-tripod hypothesis.
-/
theorem endpoint_or_same_rim_contacts_of_no_ambient_tripod
    {S H : GeneralSociety V}
    {T : H.Tripod}
    (hgraph : H.graph ≤ S.graph)
    {right : Fin 3 -> V}
    {L : ThreeVertexLinkage S.graph T.attach right}
    (D : TripodAttachmentLinkageLastContacts T L)
    (hrightBoundary : forall i : Fin 3, right i ∈ S.boundarySet)
    (hno_tripod : Not (Nonempty S.Tripod)) :
    (Exists fun i : Fin 3 =>
      D.contact i = T.left ∨ D.contact i = T.right) ∨
      Exists fun i : Fin 3 =>
        Exists fun j : Fin 3 =>
          Exists fun r : Fin 3 =>
            i ≠ j ∧
              D.contact i ∈ Walk.InternalVertices (T.rim r) ∧
                D.contact j ∈ Walk.InternalVertices (T.rim r) := by
  classical
  have hclassify :
      forall i : Fin 3,
        (D.contact i = T.left ∨ D.contact i = T.right) ∨
          Exists fun r : Fin 3 =>
            D.contact i ∈ Walk.InternalVertices (T.rim r) := by
    intro i
    rcases D.contact_mem_carrier i with ⟨r, hr⟩
    rcases T.rim_support_internal_or_endpoint hr with hinternal | hend
    · exact Or.inr ⟨r, hinternal⟩
    · exact Or.inl hend
  by_cases hendpoint :
      Exists fun i : Fin 3 =>
        D.contact i = T.left ∨ D.contact i = T.right
  · exact Or.inl hendpoint
  · right
    have hinternal :
        forall i : Fin 3,
          Exists fun r : Fin 3 =>
            D.contact i ∈ Walk.InternalVertices (T.rim r) := by
      intro i
      rcases hclassify i with hend | hr
      · exact False.elim (hendpoint ⟨i, hend⟩)
      · exact hr
    choose rimIndex hrimIndex using hinternal
    by_cases hinjective : Function.Injective rimIndex
    · exact False.elim
        (hno_tripod
          ⟨D.toAmbientTripodOfDistinctRimContacts
            hgraph hrightBoundary rimIndex hinjective hrimIndex⟩)
    · rcases Function.not_injective_iff.mp hinjective with
        ⟨i, j, hijRim, hij⟩
      exact
        ⟨i, j, rimIndex i, hij, hrimIndex i,
          by simpa [hijRim] using hrimIndex j⟩

end TripodAttachmentLinkageLastContacts

end GeneralSociety

end Schematic.Math.GraphTheory
