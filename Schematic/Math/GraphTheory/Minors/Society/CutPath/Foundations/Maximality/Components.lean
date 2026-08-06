import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.Maximality.Separation

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- In a 3-connected society, every active off-path component from the maximal
GM IX `(2.1)` setup is confined between two consecutive attachment/end vertices
of the avoiding path.  This packages the direct-boundary lower bound with the
ordered-gap lemma from `GMIX21`. -/
theorem ThreeConnected.exists_consecutive_attachment_bounds_for_active_offPath_component
    [Fintype V]
    [DecidableEq V]
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
    Exists fun l : V =>
      Exists fun r : V =>
        l ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ∧
          r ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ∧
          l ∈ p.support ∧ r ∈ p.support ∧
          Walk.supportIndex p l <= Walk.supportIndex p r ∧
          (forall b : V,
            b ∈ relativeVertexBoundary S.graph
              (induceComponentSupport (G := S.graph) C)
              {v : V | v ∈ p.support} ->
              Walk.supportIndex p l <= Walk.supportIndex p b ∧
                Walk.supportIndex p b <= Walk.supportIndex p r) ∧
          forall x : V,
            x ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ->
              Walk.supportIndex p l < Walk.supportIndex p x ->
                Walk.supportIndex p x < Walk.supportIndex p r ->
                  False := by
  classical
  let B : Set V :=
    relativeVertexBoundary S.graph (induceComponentSupport (G := S.graph) C)
      {v : V | v ∈ p.support}
  have hB_ge_three : 3 <= B.ncard := by
    simpa [B] using
      hthree.offPath_component_path_boundary_ncard_ge_three
        hH hHmax hp_path hp_avoid C hK_active
  have hB_nonempty : B.Nonempty := by
    exact (Set.ncard_pos (s := B)).mp (by omega)
  simpa [B] using
    hH.exists_consecutive_attachment_bounds_for_offPath_boundary
      hHmax hp_path hp_avoid C hB_nonempty

/-- The interval data from GM IX `(2.1)` together with the corresponding
component of `G - {l,r}`.

This is the assembled object immediately preceding the final contradiction in
the source proof of `(2.1)`: an active off-path component is contained in an
active component after deleting the two consecutive attachment/end vertices
`l,r`. -/
theorem ThreeConnected.exists_deleted_pair_component_for_active_offPath_component
    [Fintype V]
    [DecidableEq V]
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
    Exists fun l : V =>
      Exists fun r : V =>
        Exists fun Cdel :
          (S.graph.induce (({l, r} : Set V)ᶜ)).ConnectedComponent =>
          l ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ∧
          r ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ∧
          l ∈ p.support ∧ r ∈ p.support ∧
          Walk.supportIndex p l <= Walk.supportIndex p r ∧
          (forall b : V,
            b ∈ relativeVertexBoundary S.graph
              (induceComponentSupport (G := S.graph) C)
              {v : V | v ∈ p.support} ->
              Walk.supportIndex p l <= Walk.supportIndex p b ∧
                Walk.supportIndex p b <= Walk.supportIndex p r) ∧
          (forall x : V,
            x ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ->
              Walk.supportIndex p l < Walk.supportIndex p x ->
                Walk.supportIndex p x < Walk.supportIndex p r ->
                  False) ∧
          induceComponentSupport (G := S.graph) C ⊆
            induceComponentSupport (G := S.graph) Cdel ∧
          (induceComponentSupport (G := S.graph) Cdel ∩ S.activeSet).Nonempty := by
  classical
  obtain ⟨l, r, hlA, hrA, hlP, hrP, hlr, hboundary_between, hgap⟩ :=
    hthree.exists_consecutive_attachment_bounds_for_active_offPath_component
      hH hHmax hp_path hp_avoid C hK_active
  obtain ⟨Cdel, hC_subset⟩ :=
    GMIX21.offPath_component_subset_deleted_pair_component
      (G := S.graph) (H := H) (p := p) C hlP hrP
  have hCdel_active :
      (induceComponentSupport (G := S.graph) Cdel ∩ S.activeSet).Nonempty := by
    rcases hK_active with ⟨v, hvC, hvActive⟩
    exact ⟨v, hC_subset hvC, hvActive⟩
  exact ⟨l, r, Cdel, hlA, hrA, hlP, hrP, hlr, hboundary_between,
    hgap, hC_subset, hCdel_active⟩

/-- Source-aligned version of
`exists_deleted_pair_component_for_active_offPath_component`.

The component returned here lives in `(G - V(H)) - {l,r}`, matching the graph
`K - {x_{i-1},x_i}` used in GM IX `(2.1)`.  This is the component on which the
remaining endpoint/attachment-exclusion facts must be proved before invoking
`GM21SeparationObstruction.of_caught_complement_deleted_pair_component`. -/
theorem ThreeConnected.exists_caught_complement_deleted_pair_component_for_active_offPath_component
    [Fintype V]
    [DecidableEq V]
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
    Exists fun l : V =>
      Exists fun r : V =>
        Exists fun Cdel :
          (S.graph.induce
            {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)}).ConnectedComponent =>
          l ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ∧
          r ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ∧
          l ∈ p.support ∧ r ∈ p.support ∧
          Walk.supportIndex p l <= Walk.supportIndex p r ∧
          (forall b : V,
            b ∈ relativeVertexBoundary S.graph
              (induceComponentSupport (G := S.graph) C)
              {v : V | v ∈ p.support} ->
            Walk.supportIndex p l <= Walk.supportIndex p b ∧
              Walk.supportIndex p b <= Walk.supportIndex p r) ∧
          (forall x : V,
            x ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V) ->
              Walk.supportIndex p l < Walk.supportIndex p x ->
                Walk.supportIndex p x < Walk.supportIndex p r ->
                  False) ∧
          induceComponentSupport (G := S.graph) C ⊆
            induceComponentSupport (G := S.graph) Cdel ∧
          (induceComponentSupport (G := S.graph) Cdel ∩ S.activeSet).Nonempty := by
  classical
  obtain ⟨l, r, hlA, hrA, hlP, hrP, hlr, hboundary_between, hgap⟩ :=
    hthree.exists_consecutive_attachment_bounds_for_active_offPath_component
      hH hHmax hp_path hp_avoid C hK_active
  obtain ⟨Cdel, hC_subset⟩ :=
    GMIX21.offPath_component_subset_deleted_pair_caught_complement_component
      (G := S.graph) (H := H) (p := p) C hlP hrP
  have hCdel_active :
      (induceComponentSupport (G := S.graph) Cdel ∩ S.activeSet).Nonempty := by
    rcases hK_active with ⟨v, hvC, hvActive⟩
    exact ⟨v, hC_subset hvC, hvActive⟩
  exact ⟨l, r, Cdel, hlA, hrA, hlP, hrP, hlr, hboundary_between,
    hgap, hC_subset, hCdel_active⟩

/-- If a path-boundary contact of the original off-path component lies inside
the deleted-pair component for `{l,r}`, then its path index is strictly between
`l` and `r`.

The weak inequalities come from the GM IX `(2.1)` interval choice; strictness
uses the fact that components of `G - {l,r}` contain neither deleted endpoint. -/
theorem offPath_boundary_mem_deleted_pair_component_strict_between
    [DecidableEq V]
    {S : GeneralSociety V}
    {s t l r b : V}
    {H : S.graph.Subgraph}
    {p : S.graph.Walk s t}
    (hlP : l ∈ p.support)
    (C :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (Cdel :
      (S.graph.induce (({l, r} : Set V)ᶜ)).ConnectedComponent)
    (hbetween :
      forall b : V,
        b ∈ relativeVertexBoundary S.graph
          (induceComponentSupport (G := S.graph) C)
          {v : V | v ∈ p.support} ->
        Walk.supportIndex p l <= Walk.supportIndex p b ∧
          Walk.supportIndex p b <= Walk.supportIndex p r)
    (hbB :
      b ∈ relativeVertexBoundary S.graph
        (induceComponentSupport (G := S.graph) C)
        {v : V | v ∈ p.support})
    (hbCdel : b ∈ induceComponentSupport (G := S.graph) Cdel) :
    Walk.supportIndex p l < Walk.supportIndex p b ∧
      Walk.supportIndex p b < Walk.supportIndex p r := by
  classical
  have hbP : b ∈ p.support := hbB.1
  have hb_not_pair : b ∈ (({l, r} : Set V)ᶜ) :=
    induceComponentSupport_subset (G := S.graph) Cdel hbCdel
  have hbl : b ≠ l := by
    intro h
    exact hb_not_pair (by simp [h])
  have hbr : b ≠ r := by
    intro h
    exact hb_not_pair (by simp [h])
  have hb_between := hbetween b hbB
  constructor
  · exact Walk.supportIndex_lt_of_le_of_mem_of_ne
      (G := S.graph) hlP hb_between.1 (by
        intro hlb
        exact hbl hlb.symm)
  · exact Walk.supportIndex_lt_of_le_of_mem_of_ne
      (G := S.graph) hbP hb_between.2 hbr

/-- General form of
`offPath_boundary_mem_deleted_pair_component_strict_between`.

Only the fact that the containing component omits `l` and `r` is used.  This
lets the strictness argument apply both to ambient components of `G - {l,r}`
and to the source-aligned components of `(G - V(H)) - {l,r}`. -/
theorem offPath_boundary_mem_component_excluding_pair_strict_between
    [DecidableEq V]
    {S : GeneralSociety V}
    {s t l r b : V}
    {H : S.graph.Subgraph}
    {p : S.graph.Walk s t}
    {A : Set V}
    (hlP : l ∈ p.support)
    (D :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (Cdel : (S.graph.induce A).ConnectedComponent)
    (hCdel_pair :
      induceComponentSupport (G := S.graph) Cdel ⊆ (({l, r} : Set V)ᶜ))
    (hbetween :
      forall b : V,
        b ∈ relativeVertexBoundary S.graph
          (induceComponentSupport (G := S.graph) D)
          {v : V | v ∈ p.support} ->
        Walk.supportIndex p l <= Walk.supportIndex p b ∧
          Walk.supportIndex p b <= Walk.supportIndex p r)
    (hbB :
      b ∈ relativeVertexBoundary S.graph
        (induceComponentSupport (G := S.graph) D)
        {v : V | v ∈ p.support})
    (hbCdel : b ∈ induceComponentSupport (G := S.graph) Cdel) :
    Walk.supportIndex p l < Walk.supportIndex p b ∧
      Walk.supportIndex p b < Walk.supportIndex p r := by
  classical
  have hbP : b ∈ p.support := hbB.1
  have hb_not_pair : b ∈ (({l, r} : Set V)ᶜ) :=
    hCdel_pair hbCdel
  have hbl : b ≠ l := by
    intro h
    exact hb_not_pair (by simp [h])
  have hbr : b ≠ r := by
    intro h
    exact hb_not_pair (by simp [h])
  have hb_between := hbetween b hbB
  constructor
  · exact Walk.supportIndex_lt_of_le_of_mem_of_ne
      (G := S.graph) hlP hb_between.1 (by
        intro hlb
        exact hbl hlb.symm)
  · exact Walk.supportIndex_lt_of_le_of_mem_of_ne
      (G := S.graph) hbP hb_between.2 hbr

/-- If the deleted-pair component containing an active off-path component
reaches the caught subgraph or the avoiding path, then it contains one of the
original path-boundary contacts strictly between the chosen consecutive
attachment/end vertices.

This composes the first-contact lemma from `GMIX21` with the strictness fact
for components of `G - {l,r}`. -/
theorem exists_strict_between_offPath_boundary_in_deleted_pair_component_of_mem_caught_or_path
    [DecidableEq V]
    {S : GeneralSociety V}
    {s t l r y : V}
    {H : S.graph.Subgraph}
    {p : S.graph.Walk s t}
    {Z : Set V}
    (hH : GMIX21.GM21Candidate (G := S.graph) Z s t H)
    (hHmax :
      forall H' : S.graph.Subgraph,
        GMIX21.GM21Candidate (G := S.graph) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    (hp_path : p.IsPath)
    (hp_avoid : GMIX21.Walk.AvoidsSet (G := S.graph) p H.verts)
    (D :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (Cdel :
      (S.graph.induce (({l, r} : Set V)ᶜ)).ConnectedComponent)
    (hD_subset :
      induceComponentSupport (G := S.graph) D ⊆
        induceComponentSupport (G := S.graph) Cdel)
    (hlP : l ∈ p.support)
    (hbetween :
      forall b : V,
        b ∈ relativeVertexBoundary S.graph
          (induceComponentSupport (G := S.graph) D)
          {v : V | v ∈ p.support} ->
        Walk.supportIndex p l <= Walk.supportIndex p b ∧
          Walk.supportIndex p b <= Walk.supportIndex p r)
    (hyCdel : y ∈ induceComponentSupport (G := S.graph) Cdel)
    (hyA : y ∈ H.verts ∨ y ∈ p.support) :
    Exists fun b : V =>
      b ∈ relativeVertexBoundary S.graph
        (induceComponentSupport (G := S.graph) D)
        {v : V | v ∈ p.support} ∧
        b ∈ induceComponentSupport (G := S.graph) Cdel ∧
          Walk.supportIndex p l < Walk.supportIndex p b ∧
            Walk.supportIndex p b < Walk.supportIndex p r := by
  classical
  obtain ⟨b, hbB, hbCdel⟩ :=
    hH.exists_offPath_boundary_in_component_of_mem_caught_or_path
      hHmax hp_path hp_avoid D Cdel hD_subset hyCdel hyA
  have hstrict :
      Walk.supportIndex p l < Walk.supportIndex p b ∧
        Walk.supportIndex p b < Walk.supportIndex p r :=
    offPath_boundary_mem_deleted_pair_component_strict_between
      (S := S) (H := H) (p := p) hlP D Cdel
      hbetween hbB hbCdel
  exact ⟨b, hbB, hbCdel, hstrict.1, hstrict.2⟩

/-- Source-aligned variant of
`exists_strict_between_offPath_boundary_in_deleted_pair_component_of_mem_caught_or_path`.

The containing component is a component of `(G - V(H)) - {l,r}`, exactly as in
the printed GM IX `(2.1)` proof. -/
theorem exists_strict_between_offPath_boundary_in_caught_complement_deleted_pair_component_of_mem_caught_or_path
    [DecidableEq V]
    {S : GeneralSociety V}
    {s t l r y : V}
    {H : S.graph.Subgraph}
    {p : S.graph.Walk s t}
    {Z : Set V}
    (hH : GMIX21.GM21Candidate (G := S.graph) Z s t H)
    (hHmax :
      forall H' : S.graph.Subgraph,
        GMIX21.GM21Candidate (G := S.graph) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    (hp_path : p.IsPath)
    (hp_avoid : GMIX21.Walk.AvoidsSet (G := S.graph) p H.verts)
    (D :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (Cdel :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)}).ConnectedComponent)
    (hD_subset :
      induceComponentSupport (G := S.graph) D ⊆
        induceComponentSupport (G := S.graph) Cdel)
    (hlP : l ∈ p.support)
    (hbetween :
      forall b : V,
        b ∈ relativeVertexBoundary S.graph
          (induceComponentSupport (G := S.graph) D)
          {v : V | v ∈ p.support} ->
        Walk.supportIndex p l <= Walk.supportIndex p b ∧
          Walk.supportIndex p b <= Walk.supportIndex p r)
    (hyCdel : y ∈ induceComponentSupport (G := S.graph) Cdel)
    (hyA : y ∈ H.verts ∨ y ∈ p.support) :
    Exists fun b : V =>
      b ∈ relativeVertexBoundary S.graph
        (induceComponentSupport (G := S.graph) D)
        {v : V | v ∈ p.support} ∧
        b ∈ induceComponentSupport (G := S.graph) Cdel ∧
          Walk.supportIndex p l < Walk.supportIndex p b ∧
            Walk.supportIndex p b < Walk.supportIndex p r := by
  classical
  obtain ⟨b, hbB, hbCdel⟩ :=
    hH.exists_offPath_boundary_in_component_of_mem_caught_or_path
      hHmax hp_path hp_avoid D Cdel hD_subset hyCdel hyA
  have hCdel_pair :
      induceComponentSupport (G := S.graph) Cdel ⊆ (({l, r} : Set V)ᶜ) := by
    intro v hvCdel hvPair
    have hvA :
        v ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
      induceComponentSupport_subset (G := S.graph) Cdel hvCdel
    exact hvA.2 hvPair
  have hstrict :
      Walk.supportIndex p l < Walk.supportIndex p b ∧
        Walk.supportIndex p b < Walk.supportIndex p r :=
    offPath_boundary_mem_component_excluding_pair_strict_between
      (S := S) (H := H) (p := p) hlP D Cdel
      hCdel_pair hbetween hbB hbCdel
  exact ⟨b, hbB, hbCdel, hstrict.1, hstrict.2⟩

/-- The source interval component is confined to the open `l`--`r` segment of
the avoiding path.

This is the formal version of the GM IX `(2.1)` sentence "From (1), there are
subgraphs `K_i`..." for the one component containing an off-path piece.  If a
path vertex in the component lay before `l` or after `r`, a path inside the
component to the first-contact vertex strictly between `l,r` would bypass the
attachment endpoint `l` or `r`; `GM21Candidate.maximal_attachment_not_bypassed`
rules that out, while the endpoint cases are impossible by path order. -/
theorem caught_complement_deleted_pair_component_confined_to_interval
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
    (D :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (Cdel :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)}).ConnectedComponent)
    (hD_subset :
      induceComponentSupport (G := S.graph) D ⊆
        induceComponentSupport (G := S.graph) Cdel)
    (hlA : l ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V))
    (hrA : r ∈ GMIX21.GM21AttachmentSet (G := S.graph) H ∪ ({s, t} : Set V))
    (hlP : l ∈ p.support)
    (hrP : r ∈ p.support)
    (hbetween :
      forall b : V,
        b ∈ relativeVertexBoundary S.graph
          (induceComponentSupport (G := S.graph) D)
          {v : V | v ∈ p.support} ->
        Walk.supportIndex p l <= Walk.supportIndex p b ∧
          Walk.supportIndex p b <= Walk.supportIndex p r)
    {y : V}
    (hyCdel : y ∈ induceComponentSupport (G := S.graph) Cdel)
    (hyP : y ∈ p.support) :
    Walk.supportIndex p l < Walk.supportIndex p y ∧
      Walk.supportIndex p y < Walk.supportIndex p r := by
  classical
  have hy_pair :
      y ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
    induceComponentSupport_subset (G := S.graph) Cdel hyCdel
  have hy_ne_l : y ≠ l := by
    intro h
    exact hy_pair.2 (by simp [h])
  have hy_ne_r : y ≠ r := by
    intro h
    exact hy_pair.2 (by simp [h])
  obtain ⟨b, hbB, hbCdel, hbl, hbr⟩ :=
    exists_strict_between_offPath_boundary_in_caught_complement_deleted_pair_component_of_mem_caught_or_path
      (S := S) (H := H) (p := p) hH hHmax hp_path hp_avoid
      D Cdel hD_subset hlP hbetween hyCdel (Or.inr hyP)
  have hbP : b ∈ p.support := hbB.1
  have hb_le_t : Walk.supportIndex p b <= Walk.supportIndex p t :=
    Walk.IsPath.supportIndex_le_end hp_path hbP
  have hy_le_t : Walk.supportIndex p y <= Walk.supportIndex p t :=
    Walk.IsPath.supportIndex_le_end hp_path hyP
  have hs_le_b : Walk.supportIndex p s <= Walk.supportIndex p b :=
    Walk.supportIndex_start_le (p := p)
  have hs_le_y : Walk.supportIndex p s <= Walk.supportIndex p y :=
    Walk.supportIndex_start_le (p := p)
  have hidx_ne_l : Walk.supportIndex p y ≠ Walk.supportIndex p l := by
    intro hidx
    have hyl : y = l := by
      exact (List.idxOf_inj hyP).mp (by
        simpa [Walk.supportIndex] using hidx)
    exact hy_ne_l hyl
  have hidx_ne_r : Walk.supportIndex p y ≠ Walk.supportIndex p r := by
    intro hidx
    have hyr : y = r := by
      exact (List.idxOf_inj hyP).mp (by
        simpa [Walk.supportIndex] using hidx)
    exact hy_ne_r hyr
  by_cases hly : Walk.supportIndex p l < Walk.supportIndex p y
  · by_cases hyr : Walk.supportIndex p y < Walk.supportIndex p r
    · exact ⟨hly, hyr⟩
    · have hry : Walk.supportIndex p r < Walk.supportIndex p y := by
        omega
      have hright_false : False := by
        rcases hrA with hr_attach | hr_end
        · obtain ⟨q, _hq_path, hq_support⟩ :=
            connected_induce_exists_path_support_subset
              (G := S.graph)
              (induceComponentSupport_connected (G := S.graph) Cdel)
              hbCdel hyCdel
          have hq_avoid_H :
              forall z : V, z ∈ q.support -> z ∉ H.verts := by
            intro z hz
            have hzC := hq_support z hz
            have hzA :
                z ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
              induceComponentSupport_subset (G := S.graph) Cdel hzC
            exact hzA.1
          have hq_avoid_r : r ∉ q.support := by
            intro hrq
            have hrC := hq_support r hrq
            have hrAset :
                r ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
              induceComponentSupport_subset (G := S.graph) Cdel hrC
            exact hrAset.2 (by simp)
          exact hH.maximal_attachment_not_bypassed_between_path_vertices
            hHmax hp_path hp_avoid hr_attach hbP hyP hbr hry
            q hq_avoid_H hq_avoid_r
        · rcases hr_end with hrs | hrt
          · subst r
            have hs_idx : Walk.supportIndex p s = 0 := by
              rw [Walk.supportIndex, Walk.idxOf_start_support]
            omega
          · subst r
            omega
      exact False.elim hright_false
  · have hyl : Walk.supportIndex p y < Walk.supportIndex p l := by
      omega
    have hleft_false : False := by
      rcases hlA with hl_attach | hl_end
      · obtain ⟨q, _hq_path, hq_support⟩ :=
          connected_induce_exists_path_support_subset
            (G := S.graph)
            (induceComponentSupport_connected (G := S.graph) Cdel)
            hyCdel hbCdel
        have hq_avoid_H :
            forall z : V, z ∈ q.support -> z ∉ H.verts := by
          intro z hz
          have hzC := hq_support z hz
          have hzA :
              z ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
            induceComponentSupport_subset (G := S.graph) Cdel hzC
          exact hzA.1
        have hq_avoid_l : l ∉ q.support := by
          intro hlq
          have hlC := hq_support l hlq
          have hlAset :
              l ∈ {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} :=
            induceComponentSupport_subset (G := S.graph) Cdel hlC
          exact hlAset.2 (by simp)
        exact hH.maximal_attachment_not_bypassed_between_path_vertices
          hHmax hp_path hp_avoid hl_attach hyP hbP hyl hbl
          q hq_avoid_H hq_avoid_l
      · rcases hl_end with hls | hlt
        · subst l
          have hs_idx : Walk.supportIndex p s = 0 := by
            rw [Walk.supportIndex, Walk.idxOf_start_support]
          omega
        · subst l
          omega
    exact False.elim hleft_false

/-- In the maximal GM IX `(2.1)` setup inside a 3-connected society, there is
no active component outside both the caught subgraph and the chosen path.

This completes the local source contradiction after the interval confinement
lemma: an active off-path component produces the consecutive endpoints `l,r`,
the source component of `(G - V(H)) - {l,r}`, a confined interval side, and
therefore the forbidden order-two separation. -/
theorem ThreeConnected.no_active_offPath_component_for_maximal_candidate
    [Fintype V]
    [DecidableEq V]
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
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent) :
    Not ((induceComponentSupport (G := S.graph) C ∩ S.activeSet).Nonempty) := by
  classical
  intro hK_active
  obtain ⟨l, r, Cdel, hlA, hrA, hlP, hrP, _hlr, hbetween, hgap,
      hD_subset, hCdel_active⟩ :=
    hthree.exists_caught_complement_deleted_pair_component_for_active_offPath_component
      hH hHmax hp_path hp_avoid C hK_active
  have hconfined :
      forall y : V,
        y ∈ induceComponentSupport (G := S.graph) Cdel ->
          y ∈ p.support ->
            Walk.supportIndex p l < Walk.supportIndex p y ∧
              Walk.supportIndex p y < Walk.supportIndex p r := by
    intro y hyCdel hyP
    exact caught_complement_deleted_pair_component_confined_to_interval
      (S := S) (H := H) (p := p) hH hHmax hp_path hp_avoid
      C Cdel hD_subset hlA hrA hlP hrP hbetween hyCdel hyP
  have hsep : GM21SeparationObstruction S s t H :=
    GM21SeparationObstruction.of_caught_complement_deleted_pair_component_of_confined
      (S := S) (s := s) (t := t) (l := l) (r := r) (H := H)
      (p := p) hH hHmax hp_path hp_avoid Cdel hrP hgap
      hconfined hCdel_active
  exact hthree.not_GM21SeparationObstruction H hsep

/-- In the maximal GM IX `(2.1)` setup, the caught subgraph contains every
active society vertex outside the avoiding path.

This is the formal replacement for the paper sentence that, after the
interval-separation contradiction, the maximal caught subgraph is the whole
graph outside the induced path.  In Lean we state the conclusion over
`S.activeSet`, because inactive isolated ambient vertices are not part of the
society represented by `S`. -/
theorem ThreeConnected.active_outside_path_subset_maximal_caught
    [Fintype V]
    [DecidableEq V]
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
    (hp_avoid : GMIX21.Walk.AvoidsSet (G := S.graph) p H.verts) :
    {v : V | v ∈ S.activeSet ∧ v ∉ p.support} ⊆ H.verts := by
  classical
  intro v hv
  by_contra hvH
  let C :
      (S.graph.induce
        {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent :=
    (S.graph.induce
      {v : V | v ∉ H.verts ∧ v ∉ p.support}).connectedComponentMk
        (⟨v, hvH, hv.2⟩ :
          {v : V | v ∉ H.verts ∧ v ∉ p.support})
  have hvC : v ∈ induceComponentSupport (G := S.graph) C := by
    exact ⟨⟨hvH, hv.2⟩, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hK_active :
      (induceComponentSupport (G := S.graph) C ∩ S.activeSet).Nonempty :=
    ⟨v, hvC, hv.1⟩
  exact
    hthree.no_active_offPath_component_for_maximal_candidate
      hH hHmax hp_path hp_avoid C hK_active

/-- The caught-subgraph conclusion from the maximal GM IX `(2.1)` setup,
converted into the vertex-set catching predicate needed by the GM IX `(2.4)`
split.

The target is the active outside of the cut path.  A component of that induced
region starts at a vertex of `H`; the `H`-component is caught by the boundary
set, and the witnessing walk in `H` stays inside the active outside because its
edges are graph edges and the avoiding path is disjoint from `H`. -/
theorem ThreeConnected.catches_active_outside_path_of_maximal_candidate
    [Fintype V]
    [DecidableEq V]
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
    (hp_avoid : GMIX21.Walk.AvoidsSet (G := S.graph) p H.verts) :
    Catches S.graph (S.boundarySet \ ({s, t} : Set V))
      {v : V | v ∈ S.activeSet ∧ v ∉ p.support} := by
  classical
  let X : Set V := {v : V | v ∈ S.activeSet ∧ v ∉ p.support}
  have hX_subset_H : X ⊆ H.verts :=
    hthree.active_outside_path_subset_maximal_caught
      hH hHmax hp_path hp_avoid
  constructor
  · intro z hz
    have hzH : z ∈ H.verts := hH.1.subset_verts hz
    exact ⟨Or.inr hz.1, by
      intro hzP
      exact hp_avoid z hzP hzH⟩
  · intro C
    obtain ⟨uX, huC⟩ := C.nonempty_supp
    have huX : (uX : V) ∈ X := uX.2
    have huH : (uX : V) ∈ H.verts := hX_subset_H huX
    let CH : H.coe.ConnectedComponent :=
      H.coe.connectedComponentMk ⟨(uX : V), huH⟩
    obtain ⟨z, hzZ, hzCH⟩ := hH.1.component_meets CH
    obtain ⟨hzH, hzCH_supp⟩ := hzCH
    have hzX : z ∈ X := by
      exact ⟨Or.inr hzZ.1, by
        intro hzP
        exact hp_avoid z hzP hzH⟩
    have hreachH :
        H.coe.Reachable
          (⟨(uX : V), huH⟩ : H.verts) (⟨z, hzH⟩ : H.verts) :=
      CH.reachable_of_mem_supp
        (by exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
        hzCH_supp
    obtain ⟨qH⟩ := hreachH
    have hqH_active :
        forall yH : H.verts,
          yH ∈ qH.support -> (yH : V) ∈ S.activeSet := by
      intro yH hyH
      by_cases hnil : qH.Nil
      · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hnil
        have hy_start : yH = (⟨(uX : V), huH⟩ : H.verts) := by
          have hy_single : yH ∈ [(⟨(uX : V), huH⟩ : H.verts)] := by
            simpa [hsupport] using hyH
          simpa using hy_single
        simpa [hy_start] using huX.1
      · obtain ⟨y', _hy'_support, hy_adj⟩ :=
          SimpleGraph.adj_of_mem_walk_support qH hnil hyH
        exact Or.inl (H.adj_sub hy_adj).left_mem_support
    let qG : S.graph.Walk (uX : V) z := qH.map H.hom
    have hqG_support_X :
        forall y : V, y ∈ qG.support -> y ∈ X := by
      intro y hy
      rcases (Walk.mem_support_map_subgraph_hom_iff qH).mp (by
          simpa [qG] using hy) with ⟨yH, hyH, rfl⟩
      exact ⟨hqH_active yH hyH, by
        intro hyP
        exact hp_avoid (yH : V) hyP yH.2⟩
    have hreachX :
        (S.graph.induce X).Reachable uX (⟨z, hzX⟩ : X) := by
      simpa [qG] using
        Walk.reachable_induce_of_support_subset qG hqG_support_X
    have hC_u :
        (S.graph.induce X).connectedComponentMk uX = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C uX).mp huC
    have hzC : (⟨z, hzX⟩ : X) ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound hreachX).symm.trans hC_u
    exact ⟨z, hzX, hzZ, hzC⟩

end GeneralSociety

end Schematic.Math.GraphTheory
