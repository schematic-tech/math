import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.BoundaryPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The fully proved GM IX `(2.1)` maximal-caught-subgraph setup used by
GM IX `(2.4)`.

Starting from a preconnected society with at least two boundary vertices, this
chooses distinct boundary vertices `s,t`, sets `Z = Ω - {s,t}`, constructs a
maximal subgraph caught by `Z` for which an `s`--`t` path remains outside it,
and replaces that path by a chordless one.  The remaining hard `(2.1)` step is
to prove, under the source separation hypotheses, that the maximal caught
subgraph is exactly `G \ V(P)`. -/
theorem exists_GM21_maximal_candidate_with_chordless_boundary_path
    (S : GeneralSociety V)
    [Fintype V] [DecidableEq V] [DecidableRel S.graph.Adj]
    (hpre : S.graph.Preconnected)
    (hboundary_card : 2 <= S.boundarySet.ncard) :
    Exists fun s : V =>
      Exists fun t : V =>
        s ∈ S.boundarySet ∧ t ∈ S.boundarySet ∧ s ≠ t ∧
          Exists fun H : S.graph.Subgraph =>
            Exists fun p : S.graph.Walk s t =>
              GMIX21.GM21Candidate
                (G := S.graph) (S.boundarySet \ ({s, t} : Set V)) s t H ∧
                p.IsPath ∧ p.IsChordless ∧
                  GMIX21.Walk.AvoidsSet (G := S.graph) p H.verts ∧
                    Walk.InternalVertices p ∩ S.boundarySet = ∅ ∧
                      (forall z : V,
                        z ∈ p.support ->
                          z ∈ S.boundarySet \ ({s, t} : Set V) ->
                            False) ∧
                        forall H' : S.graph.Subgraph,
                          GMIX21.GM21Candidate
                            (G := S.graph)
                            (S.boundarySet \ ({s, t} : Set V)) s t H' ->
                            H ≤ H' -> H' ≤ H := by
  classical
  obtain ⟨s, t, hs, ht, hst, q0, hq0_path, _hq0_chordless,
      _hq0_clean, hq0_avoid_remainder⟩ :=
    S.exists_chordless_boundary_path_avoiding_remainder hpre hboundary_card
  let Z : Set V := S.boundarySet \ ({s, t} : Set V)
  have hq0_avoid_Z : GMIX21.Walk.AvoidsSet (G := S.graph) q0 Z := by
    intro z hz hzZ
    exact hq0_avoid_remainder z hz hzZ
  obtain ⟨H, p, hH, hp_path, hp_chordless, hp_avoid_H, hHmax⟩ :=
    GMIX21.exists_maximal_GM21Candidate_with_chordless_path
      (G := S.graph) (Z := Z) (s := s) (t := t)
      ⟨q0, hq0_path, hq0_avoid_Z⟩
  have hp_avoid_Z : GMIX21.Walk.AvoidsSet (G := S.graph) p Z :=
    GMIX21.Walk.avoidsSet_mono hH.1.subset_verts hp_avoid_H
  have hp_avoid_remainder :
      forall z : V,
        z ∈ p.support ->
          z ∈ S.boundarySet \ ({s, t} : Set V) ->
            False := by
    intro z hz hzZ
    exact hp_avoid_Z z hz hzZ
  have hp_clean :
      Walk.InternalVertices p ∩ S.boundarySet = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hz_internal : z ∈ Walk.InternalVertices p := hz.1
    have hz_boundary : z ∈ S.boundarySet := hz.2
    have hz_not_end : z ∉ ({s, t} : Set V) := by
      intro hzst
      rcases hzst with hzs | hzt
      · exact hz_internal.2.1 hzs
      · exact hz_internal.2.2 hzt
    exact hp_avoid_remainder z hz_internal.1
      ⟨hz_boundary, hz_not_end⟩
  exact ⟨s, t, hs, ht, hst, H, p, hH, hp_path, hp_chordless,
    hp_avoid_H, hp_clean, hp_avoid_remainder, hHmax⟩

/-- The separation alternative from GM IX `(2.1)`, stated in the form that is
used by GM IX `(2.4)`: the whole society boundary is on the left shore, the
caught subgraph is on that same shore, and a nonempty active part is cut off
by a separator of order at most two. -/
def GM21SeparationObstruction
    (S : GeneralSociety V)
    (s t : V)
    (H : S.graph.Subgraph) : Prop :=
  Exists fun T : Separation S.graph =>
    s ∈ T.left ∧ t ∈ T.left ∧
      S.boundarySet \ ({s, t} : Set V) ⊆ T.left ∧
        H.verts ⊆ T.left ∧
          ((T.right \ T.left) ∩ S.activeSet).Nonempty ∧
            T.OrderAtMost 2

theorem ThreeConnected.not_GM21SeparationObstruction
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    {s t : V}
    (H : S.graph.Subgraph) :
    Not (GM21SeparationObstruction S s t H) := by
  classical
  intro hsep
  rcases hsep with
    ⟨T, hs_left, ht_left, hZ_left, _hH_left, hright, horder⟩
  have hboundary_left : S.boundarySet ⊆ T.left := by
    intro v hv
    by_cases hvs : v = s
    · simpa [hvs] using hs_left
    · by_cases hvt : v = t
      · simpa [hvt] using ht_left
      · exact hZ_left ⟨hv, by
          intro hvst
          rcases hvst with hvs' | hvt'
          · exact hvs hvs'
          · exact hvt hvt'⟩
  exact hthree T hboundary_left hright horder

/-- A closed region separated from the rest of the society by at most two
vertices gives the GM IX `(2.1)` separation obstruction.

This is the reusable form of the construction used after the source proof has
isolated one interval of the avoiding path: `K` is the side to be cut off,
`B` is its boundary in the rest of the graph, and all of `Ω` and the caught
subgraph remain outside `K`. -/
theorem GM21SeparationObstruction.of_closed_region
    [Fintype V]
    {S : GeneralSociety V}
    {s t : V}
    {H : S.graph.Subgraph}
    {K B : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B ->
        Not (S.graph.Adj a b))
    (hsK : s ∉ K)
    (htK : t ∉ K)
    (hZK : S.boundarySet \ ({s, t} : Set V) ⊆ Kᶜ)
    (hHK : H.verts ⊆ Kᶜ)
    (hK_active : (K ∩ S.activeSet).Nonempty)
    (hB_card : B.ncard <= 2) :
    GM21SeparationObstruction S s t H := by
  classical
  let T : Separation S.graph := Separation.ofCoreAndBoundary K B hclosed
  refine ⟨T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsK
  · exact htK
  · intro z hz
    exact hZK hz
  · intro z hz
    exact hHK hz
  · rcases hK_active with ⟨v, hvK, hvActive⟩
    exact ⟨v, ⟨Or.inl hvK, by simpa [T, Separation.ofCoreAndBoundary] using hvK⟩,
      hvActive⟩
  · exact
      Separation.ofCoreAndBoundary_orderAtMost_of_boundary_ncard_le
        (G := S.graph) K B hclosed hB_card

/-- Component form of the GM IX `(2.1)` separation construction.

After the source interval argument has identified two consecutive attachment
vertices `l,r`, the side cut off between them is naturally represented as a
component of `G - {l,r}`.  This lemma turns that component directly into the
order-two separation obstruction, provided the original boundary and caught
subgraph are outside the component. -/
theorem GM21SeparationObstruction.of_deleted_pair_component
    [Fintype V]
    [DecidableEq V]
    {S : GeneralSociety V}
    {s t l r : V}
    {H : S.graph.Subgraph}
    (C : (S.graph.induce (({l, r} : Set V)ᶜ)).ConnectedComponent)
    (hsK : s ∉ induceComponentSupport (G := S.graph) C)
    (htK : t ∉ induceComponentSupport (G := S.graph) C)
    (hZK :
      S.boundarySet \ ({s, t} : Set V) ⊆
        (induceComponentSupport (G := S.graph) C)ᶜ)
    (hHK :
      H.verts ⊆ (induceComponentSupport (G := S.graph) C)ᶜ)
    (hK_active :
      (induceComponentSupport (G := S.graph) C ∩ S.activeSet).Nonempty) :
    GM21SeparationObstruction S s t H := by
  classical
  let K : Set V := induceComponentSupport (G := S.graph) C
  let B : Set V := ({l, r} : Set V)
  have hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B ->
        Not (S.graph.Adj a b) := by
    intro a b ha hbK hbB hab
    have hb_deleted : b ∈ (({l, r} : Set V)ᶜ) := by
      simpa [B] using hbB
    exact hbK
      (induceComponentSupport_mem_of_adj (G := S.graph) C
        (by simpa [K] using ha) hb_deleted hab)
  refine GM21SeparationObstruction.of_closed_region
    (S := S) (s := s) (t := t) (H := H) (K := K) (B := B)
    hclosed ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [K] using hsK
  · simpa [K] using htK
  · intro z hz
    exact hZK hz
  · intro z hz
    exact hHK hz
  · simpa [K] using hK_active
  · by_cases hlr : l = r
    · change ({l, r} : Set V).ncard <= 2
      simp [hlr]
    · change ({l, r} : Set V).ncard <= 2
      rw [Set.ncard_pair hlr]

/-- Source-aligned component form of the GM IX `(2.1)` separation construction.

The proof of `(2.1)` decomposes `K = G - V(H)`, not the whole ambient graph.
After consecutive attachment/end vertices `l,r` have been chosen, the interval
side is a component of `K - {l,r}`.  This constructor turns such a component
into the same order-two obstruction once the endpoints are outside it and it has
no edge back to the caught subgraph.  The latter is the exact remaining
maximality/interval fact needed in the source proof. -/
theorem GM21SeparationObstruction.of_caught_complement_deleted_pair_component
    [Fintype V]
    [DecidableEq V]
    {S : GeneralSociety V}
    {s t l r : V}
    {H : S.graph.Subgraph}
    (C :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)}).ConnectedComponent)
    (hZH : S.boundarySet \ ({s, t} : Set V) ⊆ H.verts)
    (hsK : s ∉ induceComponentSupport (G := S.graph) C)
    (htK : t ∉ induceComponentSupport (G := S.graph) C)
    (hno_H_adj :
      forall {a b : V},
        a ∈ induceComponentSupport (G := S.graph) C ->
          b ∈ H.verts -> Not (S.graph.Adj a b))
    (hK_active :
      (induceComponentSupport (G := S.graph) C ∩ S.activeSet).Nonempty) :
    GM21SeparationObstruction S s t H := by
  classical
  let K : Set V := induceComponentSupport (G := S.graph) C
  let B : Set V := ({l, r} : Set V)
  have hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B ->
        Not (S.graph.Adj a b) := by
    intro a b ha hbK hbB hab
    by_cases hbH : b ∈ H.verts
    · exact hno_H_adj (by simpa [K] using ha) hbH hab
    · have hbA :
          b ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} := by
        exact ⟨hbH, by simpa [B] using hbB⟩
      exact hbK
        (induceComponentSupport_mem_of_adj (G := S.graph) C
          (by simpa [K] using ha) hbA hab)
  refine GM21SeparationObstruction.of_closed_region
    (S := S) (s := s) (t := t) (H := H) (K := K) (B := B)
    hclosed ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [K] using hsK
  · simpa [K] using htK
  · intro z hz zK
    have hzH : z ∈ H.verts := hZH hz
    have zOff :
        z ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
      induceComponentSupport_subset (G := S.graph) C
        (by simpa [K] using zK)
    exact zOff.1 hzH
  · intro z hzH zK
    have zOff :
        z ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
      induceComponentSupport_subset (G := S.graph) C
        (by simpa [K] using zK)
    exact zOff.1 hzH
  · simpa [K] using hK_active
  · by_cases hlr : l = r
    · change ({l, r} : Set V).ncard <= 2
      simp [hlr]
    · change ({l, r} : Set V).ncard <= 2
      rw [Set.ncard_pair hlr]

/-- A confined source interval component gives the GM IX `(2.1)` separation
obstruction.

Once the component of `(G - V(H)) - {l,r}` is known to meet the avoiding path
only strictly between the consecutive attachment/end vertices `l,r`, the
endpoint and attachment-back-to-`H` exclusions are immediate.  This is the
usable final form of the source interval contradiction; the remaining hard
source lemma is precisely the confinement statement. -/
theorem GM21SeparationObstruction.of_caught_complement_deleted_pair_component_of_confined
    [Fintype V]
    [DecidableEq V]
    {S : GeneralSociety V}
    {s t l r : V}
    {H : S.graph.Subgraph}
    {p : S.graph.Walk s t}
    (hH :
      GMIX21.GM21Candidate
        (G := S.graph) (S.boundarySet \ ({s, t} : Set V)) s t H)
    (hHmax :
      forall H' : S.graph.Subgraph,
        GMIX21.GM21Candidate
          (G := S.graph) (S.boundarySet \ ({s, t} : Set V)) s t H' ->
          H ≤ H' -> H' ≤ H)
    (hp_path : p.IsPath)
    (hp_avoid : GMIX21.Walk.AvoidsSet (G := S.graph) p H.verts)
    (C :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)}).ConnectedComponent)
    (hrP : r ∈ p.support)
    (hgap :
      forall x : V,
        x ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ->
          Walk.supportIndex p l < Walk.supportIndex p x ->
            Walk.supportIndex p x < Walk.supportIndex p r ->
              False)
    (hconfined :
      forall y : V,
        y ∈ induceComponentSupport (G := S.graph) C ->
          y ∈ p.support ->
            Walk.supportIndex p l < Walk.supportIndex p y ∧
              Walk.supportIndex p y < Walk.supportIndex p r)
    (hK_active :
      (induceComponentSupport (G := S.graph) C ∩ S.activeSet).Nonempty) :
    GM21SeparationObstruction S s t H := by
  classical
  have hZH : S.boundarySet \ ({s, t} : Set V) ⊆ H.verts :=
    hH.1.subset_verts
  have hsK : s ∉ induceComponentSupport (G := S.graph) C := by
    intro hsC
    have hs_between := hconfined s hsC p.start_mem_support
    have hs_idx : Walk.supportIndex p s = 0 := by
      rw [Walk.supportIndex, Walk.idxOf_start_support]
    omega
  have htK : t ∉ induceComponentSupport (G := S.graph) C := by
    intro htC
    have ht_between := hconfined t htC p.end_mem_support
    have hr_le_t : Walk.supportIndex p r <= Walk.supportIndex p t :=
      Walk.IsPath.supportIndex_le_end hp_path hrP
    omega
  have hno_H_adj :
      forall {a b : V},
        a ∈ induceComponentSupport (G := S.graph) C ->
          b ∈ H.verts -> Not (S.graph.Adj a b) := by
    intro a b haC hbH hab
    have haA :
        a ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
      induceComponentSupport_subset (G := S.graph) C haC
    have ha_attach : a ∈ GMIX21.GM21AttachmentSet (G := S.graph) H := by
      refine ⟨haA.1, ?_⟩
      exact ⟨b, hbH, hab⟩
    have haP : a ∈ p.support :=
      hH.maximal_attachment_mem_every_avoiding_path
        hHmax hp_path hp_avoid ha_attach
    have ha_between := hconfined a haC haP
    exact hgap a (Or.inl ha_attach) ha_between.1 ha_between.2
  exact GM21SeparationObstruction.of_caught_complement_deleted_pair_component
    (S := S) (s := s) (t := t) (l := l) (r := r) (H := H)
    C hZH hsK htK hno_H_adj hK_active

/-- An off-path component with at most two neighbours on the path gives the
GM IX `(2.1)` separation alternative in the exact form eliminated by
`ThreeConnected.not_GM21SeparationObstruction`. -/
theorem GM21SeparationObstruction.of_offPath_component_boundary
    [Fintype V]
    {S : GeneralSociety V}
    {s t : V}
    {H : S.graph.Subgraph}
    {p : S.graph.Walk s t}
    (hH :
      GMIX21.GM21Candidate
        (G := S.graph) (S.boundarySet \ ({s, t} : Set V)) s t H)
    (hHmax :
      forall H' : S.graph.Subgraph,
        GMIX21.GM21Candidate
          (G := S.graph) (S.boundarySet \ ({s, t} : Set V)) s t H' ->
          H ≤ H' -> H' ≤ H)
    (hp_path : p.IsPath)
    (hp_avoid : GMIX21.Walk.AvoidsSet (G := S.graph) p H.verts)
    (C :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (hK_active :
      (induceComponentSupport (G := S.graph) C ∩ S.activeSet).Nonempty)
    (hB_card :
      (relativeVertexBoundary S.graph
        (induceComponentSupport (G := S.graph) C)
        {v : V | v ∈ p.support}).ncard <= 2) :
    GM21SeparationObstruction S s t H := by
  classical
  let K : Set V := induceComponentSupport (G := S.graph) C
  let B : Set V :=
    relativeVertexBoundary S.graph K {v : V | v ∈ p.support}
  have hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B ->
        Not (S.graph.Adj a b) := by
    intro a b ha hbK hbB
    exact hH.offPath_component_closed_with_path_boundary
      hHmax hp_path hp_avoid C (by simpa [K] using ha)
      (by simpa [K] using hbK) (by simpa [B, K] using hbB)
  refine GM21SeparationObstruction.of_closed_region
    (S := S) (s := s) (t := t) (H := H) (K := K) (B := B)
    hclosed ?_ ?_ ?_ ?_ ?_ ?_
  · intro hsK
    have hs_off :
        s ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
      induceComponentSupport_subset (G := S.graph) C
        (by simpa [K] using hsK)
    exact hs_off.2 p.start_mem_support
  · intro htK
    have ht_off :
        t ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
      induceComponentSupport_subset (G := S.graph) C
        (by simpa [K] using htK)
    exact ht_off.2 p.end_mem_support
  · intro z hz zK
    have hzH : z ∈ H.verts := hH.1.subset_verts hz
    have hz_off :
        z ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
      induceComponentSupport_subset (G := S.graph) C
        (by simpa [K] using zK)
    exact hz_off.1 hzH
  · intro z hzH zK
    have hz_off :
        z ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
      induceComponentSupport_subset (G := S.graph) C
        (by simpa [K] using zK)
    exact hz_off.1 hzH
  · simpa [K] using hK_active
  · simpa [B, K] using hB_card

theorem ThreeConnected.offPath_component_path_boundary_ncard_ge_three
    [Fintype V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    {s t : V}
    {H : S.graph.Subgraph}
    {p : S.graph.Walk s t}
    (hH :
      GMIX21.GM21Candidate
        (G := S.graph) (S.boundarySet \ ({s, t} : Set V)) s t H)
    (hHmax :
      forall H' : S.graph.Subgraph,
        GMIX21.GM21Candidate
          (G := S.graph) (S.boundarySet \ ({s, t} : Set V)) s t H' ->
          H ≤ H' -> H' ≤ H)
    (hp_path : p.IsPath)
    (hp_avoid : GMIX21.Walk.AvoidsSet (G := S.graph) p H.verts)
    (C :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (hK_active :
      (induceComponentSupport (G := S.graph) C ∩ S.activeSet).Nonempty) :
    3 <=
      (relativeVertexBoundary S.graph
        (induceComponentSupport (G := S.graph) C)
        {v : V | v ∈ p.support}).ncard := by
  by_contra hnot
  have hB_card :
      (relativeVertexBoundary S.graph
        (induceComponentSupport (G := S.graph) C)
        {v : V | v ∈ p.support}).ncard <= 2 := by
    omega
  exact hthree.not_GM21SeparationObstruction H
    (GM21SeparationObstruction.of_offPath_component_boundary
      hH hHmax hp_path hp_avoid C hK_active hB_card)

end GeneralSociety

end Schematic.Math.GraphTheory
