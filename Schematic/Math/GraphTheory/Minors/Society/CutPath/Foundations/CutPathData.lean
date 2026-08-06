import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.Maximality

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The pair of boundary vertices and the induced path selected in the first
paragraph of GM IX `(2.4)`.

The paper obtains this package from GM IX `(2.1)`: for distinct boundary
vertices `s,t`, the remaining boundary vertices catch the graph outside an
induced `s`--`t` path. -/
structure GMIX24CutPath (S : GeneralSociety V) where
  s : V
  t : V
  s_mem_boundary : s ∈ S.boundarySet
  t_mem_boundary : t ∈ S.boundarySet
  s_ne_t : s ≠ t
  path : S.graph.Walk s t
  path_isPath : path.IsPath
  path_induced : path.IsChordless
  internal_disjoint_boundary :
    Walk.InternalVertices path ∩ S.boundarySet = ∅
  caught_outside :
    Catches S.graph (S.boundarySet \ ({s, t} : Set V))
      {v : V | v ∈ S.activeSet ∧ v ∉ path.support}

namespace GMIX24CutPath

def ofCaughtChordlessPath {S : GeneralSociety V}
    {s t : V}
    (hs : s ∈ S.boundarySet)
    (ht : t ∈ S.boundarySet)
    (hst : s ≠ t)
    (p : S.graph.Walk s t)
    (hp_path : p.IsPath)
    (hp_chordless : p.IsChordless)
    (hp_internal_boundary :
      Walk.InternalVertices p ∩ S.boundarySet = ∅)
    (hp_caught :
      Catches S.graph (S.boundarySet \ ({s, t} : Set V))
        {v : V | v ∈ S.activeSet ∧ v ∉ p.support}) :
    GMIX24CutPath S where
  s := s
  t := t
  s_mem_boundary := hs
  t_mem_boundary := ht
  s_ne_t := hst
  path := p
  path_isPath := hp_path
  path_induced := hp_chordless
  internal_disjoint_boundary := hp_internal_boundary
  caught_outside := hp_caught

def reverse {S : GeneralSociety V} (P : GMIX24CutPath S) :
    GMIX24CutPath S where
  s := P.t
  t := P.s
  s_mem_boundary := P.t_mem_boundary
  t_mem_boundary := P.s_mem_boundary
  s_ne_t := P.s_ne_t.symm
  path := P.path.reverse
  path_isPath := P.path_isPath.reverse
  path_induced := by
    rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
    intro u v hu hv huv
    have hu' : u ∈ P.path.support := by
      rw [SimpleGraph.Walk.support_reverse] at hu
      exact List.mem_reverse.mp hu
    have hv' : v ∈ P.path.support := by
      rw [SimpleGraph.Walk.support_reverse] at hv
      exact List.mem_reverse.mp hv
    have huv_edge : s(u, v) ∈ P.path.edges :=
      P.path_induced.mem_edges hu' hv' huv
    rw [SimpleGraph.Walk.edges_reverse]
    exact List.mem_reverse.mpr huv_edge
  internal_disjoint_boundary := by
    simpa [Walk.internalVertices_reverse] using P.internal_disjoint_boundary
  caught_outside := by
    have hA :
        S.boundarySet \ ({P.t, P.s} : Set V) =
          S.boundarySet \ ({P.s, P.t} : Set V) := by
      ext v
      simp [or_comm]
    have hX :
        {v : V | v ∈ S.activeSet ∧ v ∉ P.path.reverse.support} =
          {v : V | v ∈ S.activeSet ∧ v ∉ P.path.support} := by
      ext v
      simp [SimpleGraph.Walk.support_reverse]
    simpa [hA, hX] using P.caught_outside

@[simp]
theorem reverse_path {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.reverse.path = P.path.reverse := by
  rfl

@[simp]
theorem reverse_s {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.reverse.s = P.t := rfl

@[simp]
theorem reverse_t {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.reverse.t = P.s := rfl

/-- Convert the completed GM IX `(2.1)` caught-subgraph conclusion into the
cut-path object used by the GM IX `(2.4)` induction. -/
def ofGM21CandidateComplement {S : GeneralSociety V}
    {s t : V}
    (hs : s ∈ S.boundarySet)
    (ht : t ∈ S.boundarySet)
    (hst : s ≠ t)
    {H : S.graph.Subgraph}
    {p : S.graph.Walk s t}
    (hH :
      GMIX21.GM21Candidate
        (G := S.graph) (S.boundarySet \ ({s, t} : Set V)) s t H)
    (hp_path : p.IsPath)
    (hp_chordless : p.IsChordless)
    (hp_internal_boundary :
      Walk.InternalVertices p ∩ S.boundarySet = ∅)
    (hverts : H.verts = {v : V | v ∈ S.activeSet ∧ v ∉ p.support}) :
    GMIX24CutPath S :=
  ofCaughtChordlessPath hs ht hst p hp_path hp_chordless
    hp_internal_boundary
    (Catches.of_GMIX21_catchesSubgraph_of_verts_eq
      (G := S.graph) (Z := S.boundarySet \ ({s, t} : Set V))
      (X := {v : V | v ∈ S.activeSet ∧ v ∉ p.support}) hH.1 hverts)

/-- Construct the GM IX `(2.4)` cut path from the completed GM IX `(2.1)`
maximal-caught-subgraph argument.

This is the first paragraph of the source proof packaged as a reusable
constructor: choose two boundary vertices, take the maximal subgraph caught by
the remaining boundary vertices, use the source `(2.1)` interval argument to
show it catches the active complement of the chosen induced path, and return
the cut-path object used for the canonical split. -/
theorem exists_of_threeConnected_preconnected_boundary
    (S : GeneralSociety V)
    [Fintype V] [DecidableEq V] [DecidableRel S.graph.Adj]
    (hpre : S.graph.Preconnected)
    (hthree : S.ThreeConnected)
    (hboundary_card : 2 <= S.boundarySet.ncard) :
    Nonempty (GMIX24CutPath S) := by
  classical
  obtain ⟨s, t, hs, ht, hst, H, p, hH, hp_path, hp_chordless,
      hp_avoid_H, hp_clean, _hp_avoid_remainder, hHmax⟩ :=
    S.exists_GM21_maximal_candidate_with_chordless_boundary_path
      hpre hboundary_card
  have hp_caught :
      Catches S.graph (S.boundarySet \ ({s, t} : Set V))
        {v : V | v ∈ S.activeSet ∧ v ∉ p.support} :=
    hthree.catches_active_outside_path_of_maximal_candidate
      hH hHmax hp_path hp_avoid_H
  exact ⟨ofCaughtChordlessPath hs ht hst p hp_path hp_chordless
    hp_clean hp_caught⟩

/-- Source-step version of `exists_of_threeConnected_preconnected_boundary`
when the initial boundary-to-boundary path has already been selected.

This is the form needed by the three-boundary RST specialization: its
no-two-separation hypothesis supplies a concrete path between two boundary
vertices avoiding the third one, so the literal GM IX `(2.4)` proof should not
need a global `Preconnected` assumption on irrelevant isolated vertices. -/
theorem exists_of_threeConnected_boundary_path
    (S : GeneralSociety V)
    [Fintype V] [DecidableEq V] [DecidableRel S.graph.Adj]
    (hthree : S.ThreeConnected)
    {s t : V}
    (hs : s ∈ S.boundarySet)
    (ht : t ∈ S.boundarySet)
    (hst : s ≠ t)
    (q0 : S.graph.Walk s t)
    (hq0_path : q0.IsPath)
    (hq0_avoid_remainder :
      forall z : V,
        z ∈ q0.support ->
          z ∈ S.boundarySet \ ({s, t} : Set V) ->
            False) :
    Nonempty (GMIX24CutPath S) := by
  classical
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
    exact hp_avoid_Z z hz_internal.1 ⟨hz_boundary, hz_not_end⟩
  have hp_caught :
      Catches S.graph (S.boundarySet \ ({s, t} : Set V))
        {v : V | v ∈ S.activeSet ∧ v ∉ p.support} :=
    hthree.catches_active_outside_path_of_maximal_candidate
      hH hHmax hp_path hp_avoid_H
  exact ⟨ofCaughtChordlessPath hs ht hst p hp_path hp_chordless
    hp_clean hp_caught⟩

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
