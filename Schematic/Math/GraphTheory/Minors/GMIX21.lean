import Schematic.Math.GraphTheory.Planarity.Basic

/-!
Reusable Graph Minors IX `(2.1)` caught-subgraph machinery.

GM IX `(2.4)` uses `(2.1)` to choose an induced `s`--`t` path whose
complement is caught by the remaining boundary vertices.  The same maximal
caught-subgraph argument is also useful in the three-boundary RST adapter, so
it lives in the background project rather than in the article-facing files.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}
variable {G : SimpleGraph V}

namespace GMIX21

/-- Finite ordered-gap lemma used by GM IX `(2.1)`.

If `A` is the ordered list of attachment/end vertices and `B` is the set of
path-neighbours of one off-path piece, the source proof uses the fact that no
member of `A` can lie strictly between two members of `B`.  This purely
arithmetic lemma extracts the corresponding consecutive interval of `A`. -/
theorem Finset.Nat.exists_consecutive_bounds_of_no_between
    (A B : Finset Nat)
    (hB_nonempty : B.Nonempty)
    {low high : Nat}
    (hlowA : low ∈ A)
    (hhighA : high ∈ A)
    (hB_bounds : forall b : Nat, b ∈ B -> low <= b ∧ b <= high)
    (hno_between :
      forall x : Nat, x ∈ A ->
        forall b : Nat, b ∈ B ->
          forall c : Nat, c ∈ B ->
            b < x -> x < c -> False) :
    Exists fun l : Nat =>
      Exists fun r : Nat =>
        l ∈ A ∧ r ∈ A ∧ l <= r ∧
          (forall b : Nat, b ∈ B -> l <= b ∧ b <= r) ∧
            forall x : Nat, x ∈ A -> l < x -> x < r -> False := by
  classical
  let m : Nat := B.min' hB_nonempty
  let M : Nat := B.max' hB_nonempty
  have hmB : m ∈ B := by
    simpa [m] using Finset.min'_mem B hB_nonempty
  have hMB : M ∈ B := by
    simpa [M] using Finset.max'_mem B hB_nonempty
  have hm_le_B : forall b : Nat, b ∈ B -> m <= b := by
    intro b hb
    simpa [m] using Finset.min'_le B b hb
  have hB_le_M : forall b : Nat, b ∈ B -> b <= M := by
    intro b hb
    simpa [M] using Finset.le_max' B b hb
  have hm_le_M : m <= M := hB_le_M m hmB
  let Aleft : Finset Nat := A.filter fun x => x <= m
  have hlow_le_m : low <= m := (hB_bounds m hmB).1
  have hAleft_nonempty : Aleft.Nonempty := by
    refine ⟨low, ?_⟩
    simp [Aleft, hlowA, hlow_le_m]
  let l : Nat := Aleft.max' hAleft_nonempty
  have hlAleft : l ∈ Aleft := by
    simpa [l] using Finset.max'_mem Aleft hAleft_nonempty
  have hlA : l ∈ A := by
    exact (Finset.mem_filter.mp hlAleft).1
  have hl_le_m : l <= m := by
    exact (Finset.mem_filter.mp hlAleft).2
  have hA_le_l_of_le_m : forall x : Nat, x ∈ A -> x <= m -> x <= l := by
    intro x hxA hxle
    have hxleft : x ∈ Aleft := by
      simp [Aleft, hxA, hxle]
    simpa [l] using Finset.le_max' Aleft x hxleft
  let Aright : Finset Nat := A.filter fun x => M <= x
  have hM_le_high : M <= high := (hB_bounds M hMB).2
  have hAright_nonempty : Aright.Nonempty := by
    refine ⟨high, ?_⟩
    simp [Aright, hhighA, hM_le_high]
  let r : Nat := Aright.min' hAright_nonempty
  have hrAright : r ∈ Aright := by
    simpa [r] using Finset.min'_mem Aright hAright_nonempty
  have hrA : r ∈ A := by
    exact (Finset.mem_filter.mp hrAright).1
  have hM_le_r : M <= r := by
    exact (Finset.mem_filter.mp hrAright).2
  have hr_le_A_of_M_le : forall x : Nat, x ∈ A -> M <= x -> r <= x := by
    intro x hxA hxle
    have hxright : x ∈ Aright := by
      simp [Aright, hxA, hxle]
    simpa [r] using Finset.min'_le Aright x hxright
  refine ⟨l, r, hlA, hrA, ?_, ?_, ?_⟩
  · omega
  · intro b hb
    exact ⟨by
      have hmb := hm_le_B b hb
      omega, by
      have hbM := hB_le_M b hb
      omega⟩
  · intro x hxA hlx hxr
    have hm_lt_x : m < x := by
      by_contra hnot
      have hx_le_m : x <= m := by omega
      have hx_le_l := hA_le_l_of_le_m x hxA hx_le_m
      omega
    have hx_lt_M : x < M := by
      by_contra hnot
      have hM_le_x : M <= x := by omega
      have hr_le_x := hr_le_A_of_M_le x hxA hM_le_x
      omega
    exact hno_between x hxA m hmB M hMB hm_lt_x hx_lt_M

/-- The vertex set in `G` represented by one connected component of a
subgraph.  This avoids exposing the subtype vertices of `H.coe` at society
theorem boundaries. -/
def subgraphComponentSupport
    (H : G.Subgraph)
    (C : H.coe.ConnectedComponent) :
    Set V :=
  {v | Exists fun hv : v ∈ H.verts =>
    (⟨v, hv⟩ : H.verts) ∈ C.supp}

theorem subgraphComponentSupport_subset
    (H : G.Subgraph)
    (C : H.coe.ConnectedComponent) :
    subgraphComponentSupport (G := G) H C ⊆ H.verts := by
  intro v hv
  exact hv.choose

theorem subgraphComponentSupport_nonempty
    (H : G.Subgraph)
    (C : H.coe.ConnectedComponent) :
    (subgraphComponentSupport (G := G) H C).Nonempty := by
  obtain ⟨u, hu⟩ := C.nonempty_supp
  exact ⟨u, u.2, hu⟩

/-- `Z` catches a subgraph when all vertices of `Z` are present and every
component of the subgraph contains a vertex of `Z`.  This is the
Graph Minors IX definition specialized to local subgraphs. -/
def CatchesSubgraph
    (Z : Set V)
    (H : G.Subgraph) : Prop :=
  Z ⊆ H.verts ∧
    forall C : H.coe.ConnectedComponent,
      Exists fun z : V =>
        z ∈ Z ∧ z ∈ subgraphComponentSupport (G := G) H C

theorem CatchesSubgraph.subset_verts
    {Z : Set V}
    {H : G.Subgraph}
    (hcatch : CatchesSubgraph (G := G) Z H) :
    Z ⊆ H.verts :=
  hcatch.1

theorem CatchesSubgraph.component_meets
    {Z : Set V}
    {H : G.Subgraph}
    (hcatch : CatchesSubgraph (G := G) Z H)
    (C : H.coe.ConnectedComponent) :
    Exists fun z : V =>
      z ∈ Z ∧ z ∈ subgraphComponentSupport (G := G) H C :=
  hcatch.2 C

theorem CatchesSubgraph.connected_of_subset_singleton
    {Z : Set V}
    {H : G.Subgraph}
    (hcatch : CatchesSubgraph (G := G) Z H)
    {z : V}
    (hzZ : z ∈ Z)
    (hZ_subset : Z ⊆ ({z} : Set V)) :
    H.coe.Connected := by
  classical
  have hzH : z ∈ H.verts := hcatch.subset_verts hzZ
  refine { preconnected := ?_, nonempty := ?_ }
  · intro a b
    let Ca : H.coe.ConnectedComponent := H.coe.connectedComponentMk a
    let Cb : H.coe.ConnectedComponent := H.coe.connectedComponentMk b
    obtain ⟨za, hzaZ, hzaCa⟩ := hcatch.component_meets Ca
    obtain ⟨zb, hzbZ, hzbCb⟩ := hcatch.component_meets Cb
    obtain ⟨hzaH, hzaCa_supp⟩ := hzaCa
    obtain ⟨hzbH, hzbCb_supp⟩ := hzbCb
    have hza_eq : za = z := by
      simpa using hZ_subset hzaZ
    have hzb_eq : zb = z := by
      simpa using hZ_subset hzbZ
    have hzCa : (⟨z, hzH⟩ : H.verts) ∈ Ca.supp := by
      have hsub : (⟨za, hzaH⟩ : H.verts) = ⟨z, hzH⟩ :=
        Subtype.ext hza_eq
      simpa [hsub] using hzaCa_supp
    have hzCb : (⟨z, hzH⟩ : H.verts) ∈ Cb.supp := by
      have hsub : (⟨zb, hzbH⟩ : H.verts) = ⟨z, hzH⟩ :=
        Subtype.ext hzb_eq
      simpa [hsub] using hzbCb_supp
    have hCa_eq_Cb : Ca = Cb :=
      SimpleGraph.ConnectedComponent.eq_of_common_vertex hzCa hzCb
    have hbCa : b ∈ Ca.supp := by
      rw [hCa_eq_Cb]
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    exact Ca.reachable_of_mem_supp
      (by exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem) hbCa
  · exact ⟨⟨z, hzH⟩⟩

/-- The edgeless subgraph with exactly the prescribed vertices.  This is the
initial caught subgraph in GM IX `(2.1)`, using the hypothesis that the
selected `s`--`t` path avoids `Z`. -/
def edgelessSubgraphOn
    (G : SimpleGraph V)
    (S : Set V) :
    G.Subgraph where
  verts := S
  Adj _ _ := False
  adj_sub := False.elim
  edge_vert := False.elim
  symm _ _ := False.elim

@[simp]
theorem edgelessSubgraphOn_verts
    (G : SimpleGraph V)
    (S : Set V) :
    (edgelessSubgraphOn G S).verts = S :=
  rfl

@[simp]
theorem edgelessSubgraphOn_adj
    (G : SimpleGraph V)
    (S : Set V)
    (u v : V) :
    Not ((edgelessSubgraphOn G S).Adj u v) := by
  intro h
  exact h

theorem edgelessSubgraphOn_catches
    (G : SimpleGraph V)
    (Z : Set V) :
    CatchesSubgraph (G := G) Z (edgelessSubgraphOn G Z) := by
  constructor
  · intro z hz
    simpa using hz
  · intro C
    obtain ⟨u, hu⟩ := C.nonempty_supp
    exact ⟨u, by simp, by
      exact ⟨by simp, hu⟩⟩

/-- A walk avoids a vertex set when none of the vertices in its support lies
in the set. -/
def Walk.AvoidsSet
    {s t : V}
    (p : G.Walk s t)
    (S : Set V) : Prop :=
  forall v : V, v ∈ p.support -> v ∉ S

theorem Walk.avoidsSet_mono
    {s t : V}
    {p : G.Walk s t}
    {S T : Set V}
    (hST : S ⊆ T)
    (hp : Walk.AvoidsSet p T) :
    Walk.AvoidsSet p S := by
  intro v hv hS
  exact hp v hv (hST hS)

theorem Walk.toSubgraph_le_deleteVerts_of_avoidsSet
    {s t : V}
    {p : G.Walk s t}
    {S : Set V}
    (hp : Walk.AvoidsSet p S) :
    p.toSubgraph ≤ (⊤ : G.Subgraph).deleteVerts S := by
  constructor
  · intro v hv
    rw [SimpleGraph.Subgraph.deleteVerts_verts]
    constructor
    · simp
    · exact hp v (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hv
        exact hv)
  · intro u v huv
    rw [SimpleGraph.Subgraph.deleteVerts_adj]
    have hu_support : u ∈ p.support := by
      rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
      exact p.toSubgraph.edge_vert huv
    have hv_support : v ∈ p.support := by
      rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
      exact p.toSubgraph.edge_vert huv.symm
    exact ⟨by simp, hp u hu_support, by simp, hp v hv_support,
      p.toSubgraph.adj_sub huv⟩

/-- The GM IX `(2.1)` candidate condition: `H` is caught by `Z`, and there is
an `s`--`t` path avoiding all vertices of `H`. -/
def GM21Candidate
    (Z : Set V)
    (s t : V)
    (H : G.Subgraph) : Prop :=
  CatchesSubgraph (G := G) Z H ∧
    Exists fun p : G.Walk s t =>
      p.IsPath ∧ Walk.AvoidsSet p H.verts

theorem GM21Candidate.path_avoids_caught_set
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H) :
    Exists fun p : G.Walk s t =>
      p.IsPath ∧ Walk.AvoidsSet p Z := by
  obtain ⟨hcatch, p, hp_path, hp_avoid⟩ := hH
  exact ⟨p, hp_path, Walk.avoidsSet_mono hcatch.subset_verts hp_avoid⟩

theorem GM21Candidate.caught_vertex_not_mem_avoiding_path
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    {p : G.Walk s t}
    (hp_avoid : Walk.AvoidsSet p H.verts)
    {z : V}
    (hz : z ∈ Z) :
    z ∉ p.support := by
  intro hzP
  exact hp_avoid z hzP (hH.1.subset_verts hz)

theorem GM21Candidate.path_toSubgraph_le_deleteVerts
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H) :
    Exists fun p : G.Walk s t =>
      p.IsPath ∧
        p.toSubgraph ≤ (⊤ : G.Subgraph).deleteVerts H.verts := by
  obtain ⟨_hcatch, p, hp_path, hp_avoid⟩ := hH
  exact ⟨p, hp_path,
    Walk.toSubgraph_le_deleteVerts_of_avoidsSet hp_avoid⟩

theorem GM21Candidate.exists_chordless_path_avoiding
    [DecidableEq V]
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H) :
    Exists fun p : G.Walk s t =>
      p.IsPath ∧ p.IsChordless ∧ Walk.AvoidsSet p H.verts := by
  obtain ⟨_hcatch, p, _hp_path, hp_avoid⟩ := hH
  have hs_not_H : s ∈ (H.verts)ᶜ := by
    exact hp_avoid s p.start_mem_support
  have ht_not_H : t ∈ (H.verts)ᶜ := by
    exact hp_avoid t p.end_mem_support
  have hreach :
      (G.induce (H.verts)ᶜ).Reachable
        (⟨s, hs_not_H⟩ : ((H.verts)ᶜ : Set V))
        (⟨t, ht_not_H⟩ : ((H.verts)ᶜ : Set V)) := by
    exact Walk.reachable_induce_of_support_subset p hp_avoid
  obtain ⟨q, hq_path, hq_chordless, hq_support⟩ :=
    reachable_induce_exists_chordless_path_support_subset
      (G := G) hs_not_H ht_not_H hreach
  exact ⟨q, hq_path, hq_chordless, by
    intro v hv hvH
    exact hq_support v hv hvH⟩

theorem GM21Candidate.edgeless
    {Z : Set V}
    {s t : V}
    (hp : Exists fun p : G.Walk s t =>
      p.IsPath ∧ Walk.AvoidsSet p Z) :
    GM21Candidate (G := G) Z s t (edgelessSubgraphOn G Z) := by
  constructor
  · exact edgelessSubgraphOn_catches G Z
  · obtain ⟨p, hp_path, hp_avoid⟩ := hp
    exact ⟨p, hp_path, by
      simpa using hp_avoid⟩

theorem exists_maximal_GM21Candidate
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {Z : Set V}
    {s t : V}
    (hp : Exists fun p : G.Walk s t =>
      p.IsPath ∧ Walk.AvoidsSet p Z) :
    Exists fun H : G.Subgraph =>
      GM21Candidate (G := G) Z s t H ∧
        forall H' : G.Subgraph,
          GM21Candidate (G := G) Z s t H' ->
            H ≤ H' -> H' ≤ H := by
  classical
  let candidates : Finset G.Subgraph :=
    Finset.univ.filter fun H : G.Subgraph =>
      GM21Candidate (G := G) Z s t H
  have hcandidates_nonempty : candidates.Nonempty := by
    refine ⟨edgelessSubgraphOn G Z, ?_⟩
    simp [candidates, GM21Candidate.edgeless (G := G) hp]
  obtain ⟨H, hH_mem, hH_max⟩ :=
    Finset.exists_maximal (s := candidates) hcandidates_nonempty
  have hH_candidate : GM21Candidate (G := G) Z s t H := by
    simpa [candidates] using hH_mem
  refine ⟨H, hH_candidate, ?_⟩
  intro H' hH' hle
  exact hH_max (by simp [candidates, hH']) hle

theorem exists_maximal_GM21Candidate_with_path
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {Z : Set V}
    {s t : V}
    (hp : Exists fun p : G.Walk s t =>
      p.IsPath ∧ Walk.AvoidsSet p Z) :
    Exists fun H : G.Subgraph =>
      Exists fun p : G.Walk s t =>
        GM21Candidate (G := G) Z s t H ∧
          p.IsPath ∧
            Walk.AvoidsSet p H.verts ∧
              forall H' : G.Subgraph,
                GM21Candidate (G := G) Z s t H' ->
                  H ≤ H' -> H' ≤ H := by
  obtain ⟨H, hH, hH_max⟩ :=
    exists_maximal_GM21Candidate (G := G) hp
  have hH_candidate := hH
  obtain ⟨_hcatch, p, hp_path, hp_avoid⟩ := hH
  exact ⟨H, p, hH_candidate, hp_path, hp_avoid, hH_max⟩

theorem exists_maximal_GM21Candidate_with_chordless_path
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {Z : Set V}
    {s t : V}
    (hp : Exists fun p : G.Walk s t =>
      p.IsPath ∧ Walk.AvoidsSet p Z) :
    Exists fun H : G.Subgraph =>
      Exists fun p : G.Walk s t =>
        GM21Candidate (G := G) Z s t H ∧
          p.IsPath ∧ p.IsChordless ∧
            Walk.AvoidsSet p H.verts ∧
              forall H' : G.Subgraph,
                GM21Candidate (G := G) Z s t H' ->
                  H ≤ H' -> H' ≤ H := by
  obtain ⟨H, _p, hH, _hp_path, _hp_avoid, hHmax⟩ :=
    exists_maximal_GM21Candidate_with_path (G := G) hp
  obtain ⟨p, hp_path, hp_chordless, hp_avoid⟩ :=
    hH.exists_chordless_path_avoiding
  exact ⟨H, p, hH, hp_path, hp_chordless, hp_avoid, hHmax⟩

theorem subgraphComponentSupport_sup_edge_meets_left
    {H : G.Subgraph}
    {x y : V}
    (hyH : y ∈ H.verts)
    (hxy : G.Adj x y)
    (C : (H ⊔ G.subgraphOfAdj hxy).coe.ConnectedComponent) :
    Exists fun a : V =>
      a ∈ H.verts ∧
        a ∈ subgraphComponentSupport
          (G := G) (H ⊔ G.subgraphOfAdj hxy) C := by
  classical
  let K : G.Subgraph := H ⊔ G.subgraphOfAdj hxy
  have hyK : y ∈ K.verts := Or.inl hyH
  have hxK : x ∈ K.verts := by
    change x ∈ (H ⊔ G.subgraphOfAdj hxy).verts
    right
    simp [SimpleGraph.subgraphOfAdj]
  have hKxy : K.Adj x y := by
    change (H ⊔ G.subgraphOfAdj hxy).Adj x y
    right
    simp [SimpleGraph.subgraphOfAdj]
  obtain ⟨u, huC⟩ := C.nonempty_supp
  have huK : (u : V) ∈ K.verts := u.2
  change (u : V) ∈ (H ⊔ G.subgraphOfAdj hxy).verts at huK
  rcases huK with huH | huEdge
  · exact ⟨u, huH, ⟨by simpa [K] using u.2, by
      simpa [K] using huC⟩⟩
  · have hu_x_or_y : (u : V) = x ∨ (u : V) = y := by
      simpa [SimpleGraph.subgraphOfAdj] using huEdge
    rcases hu_x_or_y with hu_eq_x | hu_eq_y
    · have hxC : (⟨x, hxK⟩ : K.verts) ∈ C.supp := by
        have hu_sub : u = (⟨x, hxK⟩ : K.verts) :=
          Subtype.ext hu_eq_x
        simpa [hu_sub] using huC
      have hyC : (⟨y, hyK⟩ : K.verts) ∈ C.supp :=
        C.mem_supp_of_adj_mem_supp hxC
          (show K.coe.Adj ⟨x, hxK⟩ ⟨y, hyK⟩ from hKxy)
      exact ⟨y, hyH, ⟨by simp, by
        simpa [K] using hyC⟩⟩
    · exact ⟨y, hyH, ⟨by simp, by
        have hu_sub : u = (⟨y, hyK⟩ : K.verts) :=
          Subtype.ext hu_eq_y
        simpa [hu_sub] using huC⟩⟩

theorem CatchesSubgraph.sup_edge_of_right_endpoint_mem
    {Z : Set V}
    {H : G.Subgraph}
    (hcatch : CatchesSubgraph (G := G) Z H)
    {x y : V}
    (hyH : y ∈ H.verts)
    (hxy : G.Adj x y) :
    CatchesSubgraph (G := G) Z (H ⊔ G.subgraphOfAdj hxy) := by
  classical
  let K : G.Subgraph := H ⊔ G.subgraphOfAdj hxy
  constructor
  · intro z hz
    exact Or.inl (hcatch.subset_verts hz)
  · intro C
    obtain ⟨a, haH, haC⟩ :=
      subgraphComponentSupport_sup_edge_meets_left
        (G := G) hyH hxy C
    let CH : H.coe.ConnectedComponent :=
      H.coe.connectedComponentMk ⟨a, haH⟩
    obtain ⟨z, hzZ, hzCH⟩ := hcatch.component_meets CH
    obtain ⟨hzH, hzCH_supp⟩ := hzCH
    obtain ⟨haK, haC_supp⟩ := haC
    have hHK : H ≤ K := by
      exact le_sup_left
    let f : H.coe →g K.coe :=
      SimpleGraph.Subgraph.inclusion hHK
    have hreachH :
        H.coe.Reachable ⟨a, haH⟩ ⟨z, hzH⟩ :=
      CH.reachable_of_mem_supp
        (by exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
        hzCH_supp
    have hreachK :
        K.coe.Reachable
          (f ⟨a, haH⟩)
          (f ⟨z, hzH⟩) :=
      hreachH.map f
    have hzK : z ∈ K.verts := hHK.left hzH
    have hcomp_a :
        K.coe.connectedComponentMk ⟨a, haK⟩ = C := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨a, haK⟩).mp haC_supp
    have hcomp_az :
        K.coe.connectedComponentMk ⟨a, haK⟩ =
          K.coe.connectedComponentMk ⟨z, hzK⟩ := by
      have hreachK' :
          K.coe.Reachable ⟨a, haK⟩ ⟨z, hzK⟩ := by
        simpa [f, K] using hreachK
      exact SimpleGraph.ConnectedComponent.sound hreachK'
    have hzC_supp : (⟨z, hzK⟩ : K.verts) ∈ C.supp := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨z, hzK⟩).mpr
        (hcomp_az.symm.trans hcomp_a)
    exact ⟨z, hzZ, ⟨by simpa [K] using hzK, by
      simpa [K] using hzC_supp⟩⟩

theorem GM21Candidate.maximal_adjacent_vertex_mem_path
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    {x y : V}
    (hx_not_H : x ∉ H.verts)
    (hyH : y ∈ H.verts)
    (hxy : G.Adj x y) :
    x ∈ p.support := by
  classical
  by_contra hx_not_support
  let H' : G.Subgraph := H ⊔ G.subgraphOfAdj hxy
  have hcatch' :
      CatchesSubgraph (G := G) Z H' := by
    simpa [H'] using
      hH.1.sup_edge_of_right_endpoint_mem (G := G) hyH hxy
  have hp_avoid_H' : Walk.AvoidsSet p H'.verts := by
    intro v hv_support hvH'
    have hv_cases : v = x ∨ v = y ∨ v ∈ H.verts := by
      simpa [H', SimpleGraph.subgraphOfAdj] using hvH'
    rcases hv_cases with rfl | hv_cases
    · exact hx_not_support hv_support
    · rcases hv_cases with rfl | hvH
      · exact hp_avoid v hv_support (by simpa using hyH)
      · exact hp_avoid v hv_support hvH
  have hH'_candidate : GM21Candidate (G := G) Z s t H' := by
    exact ⟨hcatch', ⟨p, hp_path, hp_avoid_H'⟩⟩
  have hHH' : H ≤ H' := by
    exact le_sup_left
  have hH'H : H' ≤ H := hHmax H' hH'_candidate hHH'
  have hxH' : x ∈ H'.verts := by
    change x ∈ (H ⊔ G.subgraphOfAdj hxy).verts
    right
    simp [SimpleGraph.subgraphOfAdj]
  exact hx_not_H (hH'H.left hxH')

/-- The attachment vertices of `G - V(H)`: outside vertices with a neighbor
in `H`.  This is the set called `X` in the proof of GM IX `(2.1)`. -/
def GM21AttachmentSet
    (H : G.Subgraph) : Set V :=
  {x | x ∉ H.verts ∧
    Exists fun y : V => y ∈ H.verts ∧ G.Adj x y}

theorem GM21Candidate.maximal_attachmentSet_subset_path
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts) :
    GM21AttachmentSet (G := G) H ⊆ {x : V | x ∈ p.support} := by
  intro x hx
  obtain ⟨hx_not_H, y, hyH, hxy⟩ := hx
  exact hH.maximal_adjacent_vertex_mem_path
    hHmax hp_path hp_avoid hx_not_H hyH hxy

theorem GM21Candidate.maximal_attachment_mem_every_avoiding_path
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    {x : V}
    (hx : x ∈ GM21AttachmentSet (G := G) H) :
    x ∈ p.support := by
  exact hH.maximal_attachmentSet_subset_path
    hHmax hp_path hp_avoid hx

theorem GM21Candidate.maximal_attachment_not_between_offPath_component_attachments
    [DecidableEq V]
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    (D :
      (G.induce {y : V | y ∉ H.verts ∧ y ∉ p.support}).ConnectedComponent)
    {x a b u v : V}
    (hx_attach : x ∈ GM21AttachmentSet (G := G) H)
    (haP : a ∈ p.support)
    (hbP : b ∈ p.support)
    (ha_lt_x : Walk.supportIndex p a < Walk.supportIndex p x)
    (hx_lt_b : Walk.supportIndex p x < Walk.supportIndex p b)
    (huD : u ∈ induceComponentSupport (G := G) D)
    (hvD : v ∈ induceComponentSupport (G := G) D)
    (hua : G.Adj u a)
    (hvb : G.Adj v b) :
    False := by
  classical
  have hxP : x ∈ p.support :=
    hH.maximal_attachment_mem_every_avoiding_path
      hHmax hp_path hp_avoid hx_attach
  have hs_le_a :
      Walk.supportIndex p s <= Walk.supportIndex p a := by
    rw [Walk.supportIndex, Walk.idxOf_start_support]
    omega
  have hb_le_t :
      Walk.supportIndex p b <= Walk.supportIndex p t := by
    by_cases hbt : b = t
    · simp [hbt]
    · have hlt :
          p.support.idxOf b < p.support.idxOf t :=
        Walk.IsPath.idxOf_lt_end_of_mem_support_ne_end
          hp_path hbP hbt
      simpa [Walk.supportIndex] using le_of_lt hlt
  let A : Set V := (H.verts ∪ ({x} : Set V))ᶜ
  have hsA : s ∈ A := by
    intro hs_bad
    rcases hs_bad with hsH | hsx
    · exact hp_avoid s p.start_mem_support hsH
    · have hs_eq_x : s = x := by simpa using hsx
      have hx_idx_zero :
          Walk.supportIndex p x = 0 := by
        simpa [Walk.supportIndex, hs_eq_x.symm] using
          Walk.idxOf_start_support p
      omega
  have htA : t ∈ A := by
    intro ht_bad
    rcases ht_bad with htH | htx
    · exact hp_avoid t p.end_mem_support htH
    · have ht_eq_x : t = x := by simpa using htx
      have hb_le_x :
          Walk.supportIndex p b <= Walk.supportIndex p x := by
        simpa [ht_eq_x] using hb_le_t
      omega
  have hu_off :
      u ∈ {y : V | y ∉ H.verts ∧ y ∉ p.support} :=
    induceComponentSupport_subset (G := G) D huD
  have hv_off :
      v ∈ {y : V | y ∉ H.verts ∧ y ∉ p.support} :=
    induceComponentSupport_subset (G := G) D hvD
  have hD_connected :
      (G.induce (induceComponentSupport (G := G) D)).Connected :=
    induceComponentSupport_connected (G := G) D
  obtain ⟨r, _hr_path, _hr_chordless, hr_support⟩ :=
    connected_induce_exists_chordless_path_support_subset
      (G := G) hD_connected huD hvD
  let leftSeg : G.Walk s a :=
    Walk.segmentBetween p p.start_mem_support haP hs_le_a
  let rightSeg : G.Walk b t :=
    Walk.segmentBetween p hbP p.end_mem_support hb_le_t
  let q : G.Walk s t :=
    leftSeg.append
      (hua.symm.toWalk.append
        (r.append (hvb.toWalk.append rightSeg)))
  have hleftSeg_A :
      forall z : V, z ∈ leftSeg.support -> z ∈ A := by
    intro z hz
    have hzP : z ∈ p.support :=
      Walk.segmentBetween_support_subset
        p.start_mem_support haP hs_le_a hz
    have hz_le_a :
        Walk.supportIndex p z <= Walk.supportIndex p a :=
      Walk.segmentBetween_supportIndex_right_le
        p.start_mem_support haP hs_le_a hz
    intro hz_bad
    rcases hz_bad with hzH | hzx
    · exact hp_avoid z hzP hzH
    · have hz_eq_x : z = x := by simpa using hzx
      have hx_le_a :
          Walk.supportIndex p x <= Walk.supportIndex p a := by
        simpa [hz_eq_x] using hz_le_a
      omega
  have hrightSeg_A :
      forall z : V, z ∈ rightSeg.support -> z ∈ A := by
    intro z hz
    have hzP : z ∈ p.support :=
      Walk.segmentBetween_support_subset
        hbP p.end_mem_support hb_le_t hz
    have hb_le_z :
        Walk.supportIndex p b <= Walk.supportIndex p z :=
      Walk.segmentBetween_supportIndex_left_le
        hp_path hbP p.end_mem_support hb_le_t hz
    intro hz_bad
    rcases hz_bad with hzH | hzx
    · exact hp_avoid z hzP hzH
    · have hz_eq_x : z = x := by simpa using hzx
      have hb_le_x :
          Walk.supportIndex p b <= Walk.supportIndex p x := by
        simpa [hz_eq_x] using hb_le_z
      omega
  have hoff_A :
      forall {z : V},
        z ∈ {y : V | y ∉ H.verts ∧ y ∉ p.support} -> z ∈ A := by
    intro z hz_off hz_bad
    rcases hz_bad with hzH | hzx
    · exact hz_off.1 hzH
    · have hz_eq_x : z = x := by simpa using hzx
      exact hz_off.2 (by simpa [hz_eq_x] using hxP)
  have hr_A : forall z : V, z ∈ r.support -> z ∈ A := by
    intro z hz
    exact hoff_A (induceComponentSupport_subset (G := G) D
      (hr_support z hz))
  have hq_support_A : forall z : V, z ∈ q.support -> z ∈ A := by
    intro z hz
    simp only [q, leftSeg, rightSeg, SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz_left | hz
    · exact hleftSeg_A z hz_left
    · rcases hz with hz_edge_a | hz
      · simp at hz_edge_a
        rcases hz_edge_a with hza | hzu
        · exact hleftSeg_A z (by
            simp [hza])
        · exact hoff_A (by
            simpa [hzu] using hu_off)
      · rcases hz with hz_r | hz
        · exact hr_A z hz_r
        · rcases hz with hz_edge_b | hz_right
          · simp at hz_edge_b
            rcases hz_edge_b with hzv | hzb
            · exact hoff_A (by
                simpa [hzv] using hv_off)
            · exact hrightSeg_A z (by
                simp [hzb])
          · exact hrightSeg_A z hz_right
  have hreach :
      (G.induce A).Reachable
        (⟨s, hsA⟩ : A) (⟨t, htA⟩ : A) :=
    Walk.reachable_induce_of_support_subset q hq_support_A
  obtain ⟨qpath, hqpath_path, _hqpath_chordless, hqpath_A⟩ :=
    reachable_induce_exists_chordless_path_support_subset
      (G := G) hsA htA hreach
  have hqpath_avoid_H : Walk.AvoidsSet qpath H.verts := by
    intro z hz hzH
    exact hqpath_A z hz (Or.inl hzH)
  have hx_qpath : x ∈ qpath.support :=
    hH.maximal_attachment_mem_every_avoiding_path
      hHmax hqpath_path hqpath_avoid_H hx_attach
  exact hqpath_A x hx_qpath (Or.inr (by simp))

/-- Bypass form of maximality for a single attachment vertex.

If `x` is an attachment of the maximal caught subgraph and lies strictly between
two vertices `a,b` on the avoiding path, then there is no walk from `a` to `b`
whose support avoids both `V(H)` and `x`.  Otherwise replacing the `a`--`b`
subpath gives an `s`--`t` path avoiding `V(H)` and missing the attachment `x`,
contradicting maximality. -/
theorem GM21Candidate.maximal_attachment_not_bypassed_between_path_vertices
    [DecidableEq V]
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    {x a b : V}
    (hx_attach : x ∈ GM21AttachmentSet (G := G) H)
    (haP : a ∈ p.support)
    (hbP : b ∈ p.support)
    (ha_lt_x : Walk.supportIndex p a < Walk.supportIndex p x)
    (hx_lt_b : Walk.supportIndex p x < Walk.supportIndex p b)
    (q : G.Walk a b)
    (hq_avoid_H : forall z : V, z ∈ q.support -> z ∉ H.verts)
    (hq_avoid_x : x ∉ q.support) :
    False := by
  classical
  have hxP : x ∈ p.support :=
    hH.maximal_attachment_mem_every_avoiding_path
      hHmax hp_path hp_avoid hx_attach
  have hs_le_a :
      Walk.supportIndex p s <= Walk.supportIndex p a := by
    exact Walk.supportIndex_start_le (p := p)
  have hb_le_t :
      Walk.supportIndex p b <= Walk.supportIndex p t :=
    Walk.IsPath.supportIndex_le_end hp_path hbP
  let leftSeg : G.Walk s a :=
    Walk.segmentBetween p p.start_mem_support haP hs_le_a
  let rightSeg : G.Walk b t :=
    Walk.segmentBetween p hbP p.end_mem_support hb_le_t
  let w : G.Walk s t := leftSeg.append (q.append rightSeg)
  let A : Set V := (H.verts ∪ ({x} : Set V))ᶜ
  have hsA : s ∈ A := by
    intro hs_bad
    rcases hs_bad with hsH | hsx
    · exact hp_avoid s p.start_mem_support hsH
    · have hs_eq_x : s = x := by simpa using hsx
      have hx_idx_zero :
          Walk.supportIndex p x = 0 := by
        simpa [Walk.supportIndex, hs_eq_x.symm] using
          Walk.idxOf_start_support p
      have hs_le_a' := hs_le_a
      omega
  have htA : t ∈ A := by
    intro ht_bad
    rcases ht_bad with htH | htx
    · exact hp_avoid t p.end_mem_support htH
    · have ht_eq_x : t = x := by simpa using htx
      have hb_le_x :
          Walk.supportIndex p b <= Walk.supportIndex p x := by
        simpa [ht_eq_x] using hb_le_t
      omega
  have hleft_A : forall z : V, z ∈ leftSeg.support -> z ∈ A := by
    intro z hz
    have hzP : z ∈ p.support :=
      Walk.segmentBetween_support_subset
        p.start_mem_support haP hs_le_a hz
    have hz_le_a :
        Walk.supportIndex p z <= Walk.supportIndex p a :=
      Walk.segmentBetween_supportIndex_right_le
        p.start_mem_support haP hs_le_a hz
    intro hz_bad
    rcases hz_bad with hzH | hzx
    · exact hp_avoid z hzP hzH
    · have hz_eq_x : z = x := by simpa using hzx
      have hx_le_a :
          Walk.supportIndex p x <= Walk.supportIndex p a := by
        simpa [hz_eq_x] using hz_le_a
      omega
  have hright_A : forall z : V, z ∈ rightSeg.support -> z ∈ A := by
    intro z hz
    have hzP : z ∈ p.support :=
      Walk.segmentBetween_support_subset
        hbP p.end_mem_support hb_le_t hz
    have hb_le_z :
        Walk.supportIndex p b <= Walk.supportIndex p z :=
      Walk.segmentBetween_supportIndex_left_le
        hp_path hbP p.end_mem_support hb_le_t hz
    intro hz_bad
    rcases hz_bad with hzH | hzx
    · exact hp_avoid z hzP hzH
    · have hz_eq_x : z = x := by simpa using hzx
      have hb_le_x :
          Walk.supportIndex p b <= Walk.supportIndex p x := by
        simpa [hz_eq_x] using hb_le_z
      omega
  have hq_A : forall z : V, z ∈ q.support -> z ∈ A := by
    intro z hz hz_bad
    rcases hz_bad with hzH | hzx
    · exact hq_avoid_H z hz hzH
    · have hz_eq_x : z = x := by simpa using hzx
      exact hq_avoid_x (by simpa [hz_eq_x] using hz)
  have hw_A : forall z : V, z ∈ w.support -> z ∈ A := by
    intro z hz
    simp only [w, leftSeg, rightSeg, SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz_left | hz
    · exact hleft_A z hz_left
    · rcases hz with hzq | hz_right
      · exact hq_A z hzq
      · exact hright_A z hz_right
  have hreach :
      (G.induce A).Reachable
        (⟨s, hsA⟩ : A) (⟨t, htA⟩ : A) :=
    Walk.reachable_induce_of_support_subset w hw_A
  obtain ⟨qpath, hqpath_path, _hqpath_chordless, hqpath_A⟩ :=
    reachable_induce_exists_chordless_path_support_subset
      (G := G) hsA htA hreach
  have hqpath_avoid_H : Walk.AvoidsSet qpath H.verts := by
    intro z hz hzH
    exact hqpath_A z hz (Or.inl hzH)
  have hx_qpath : x ∈ qpath.support :=
    hH.maximal_attachment_mem_every_avoiding_path
      hHmax hqpath_path hqpath_avoid_H hx_attach
  exact hqpath_A x hx_qpath (Or.inr (by simp))

/-- Relative-boundary version of
`maximal_attachment_not_between_offPath_component_attachments`: an attachment
vertex of the maximal caught subgraph cannot occur strictly between two
vertices where the same off-path component attaches to the avoiding path. -/
theorem GM21Candidate.maximal_attachment_not_between_offPath_component_boundary
    [DecidableEq V]
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    (D :
      (G.induce {y : V | y ∉ H.verts ∧ y ∉ p.support}).ConnectedComponent)
    {x a b : V}
    (hx_attach : x ∈ GM21AttachmentSet (G := G) H)
    (haB :
      a ∈ relativeVertexBoundary G (induceComponentSupport (G := G) D)
        {v : V | v ∈ p.support})
    (hbB :
      b ∈ relativeVertexBoundary G (induceComponentSupport (G := G) D)
        {v : V | v ∈ p.support})
    (ha_lt_x : Walk.supportIndex p a < Walk.supportIndex p x)
    (hx_lt_b : Walk.supportIndex p x < Walk.supportIndex p b) :
    False := by
  rcases haB with ⟨haP, u, huD, hua⟩
  rcases hbB with ⟨hbP, v, hvD, hvb⟩
  exact hH.maximal_attachment_not_between_offPath_component_attachments
    hHmax hp_path hp_avoid D hx_attach haP hbP ha_lt_x hx_lt_b
    huD hvD hua hvb

/-- Source interval extraction for GM IX `(2.1)`.

For one off-path component `D`, let `B` be the set of vertices of the path
adjacent to `D`, and let `A` be `X ∪ {s,t}`, where `X` is the attachment set of
the maximal caught subgraph.  The maximality argument shows that no attachment
vertex lies strictly between two members of `B`; the endpoints `s,t` cannot do
so by path order.  Hence all of `B` lies in one consecutive interval of `A`.
-/
theorem GM21Candidate.exists_consecutive_attachment_bounds_for_offPath_boundary
    [Fintype V]
    [DecidableEq V]
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    (D :
      (G.induce {y : V | y ∉ H.verts ∧ y ∉ p.support}).ConnectedComponent)
    (hB_nonempty :
      (relativeVertexBoundary G (induceComponentSupport (G := G) D)
        {v : V | v ∈ p.support}).Nonempty) :
    Exists fun l : V =>
      Exists fun r : V =>
        l ∈ GM21AttachmentSet (G := G) H ∪ ({s, t} : Set V) ∧
          r ∈ GM21AttachmentSet (G := G) H ∪ ({s, t} : Set V) ∧
          l ∈ p.support ∧ r ∈ p.support ∧
          Walk.supportIndex p l <= Walk.supportIndex p r ∧
          (forall b : V,
            b ∈ relativeVertexBoundary G (induceComponentSupport (G := G) D)
              {v : V | v ∈ p.support} ->
              Walk.supportIndex p l <= Walk.supportIndex p b ∧
                Walk.supportIndex p b <= Walk.supportIndex p r) ∧
          forall x : V,
            x ∈ GM21AttachmentSet (G := G) H ∪ ({s, t} : Set V) ->
              Walk.supportIndex p l < Walk.supportIndex p x ->
                Walk.supportIndex p x < Walk.supportIndex p r ->
                  False := by
  classical
  let Aset : Set V := GM21AttachmentSet (G := G) H ∪ ({s, t} : Set V)
  let Bset : Set V :=
    relativeVertexBoundary G (induceComponentSupport (G := G) D)
      {v : V | v ∈ p.support}
  let Aidx : Finset Nat := Aset.toFinset.image (Walk.supportIndex p)
  let Bidx : Finset Nat := Bset.toFinset.image (Walk.supportIndex p)
  have hA_path : Aset ⊆ {v : V | v ∈ p.support} := by
    intro x hx
    rcases hx with hxAttach | hxst
    · exact hH.maximal_attachment_mem_every_avoiding_path
        hHmax hp_path hp_avoid hxAttach
    · rcases hxst with hxs | hxt
      · subst x
        exact p.start_mem_support
      · subst x
        exact p.end_mem_support
  have hBidx_nonempty : Bidx.Nonempty := by
    rcases hB_nonempty with ⟨b, hb⟩
    refine ⟨Walk.supportIndex p b, ?_⟩
    change Walk.supportIndex p b ∈
      Bset.toFinset.image (Walk.supportIndex p)
    exact Finset.mem_image.mpr ⟨b, by simpa [Bset] using hb, rfl⟩
  have hlowA : Walk.supportIndex p s ∈ Aidx := by
    change Walk.supportIndex p s ∈
      Aset.toFinset.image (Walk.supportIndex p)
    exact Finset.mem_image.mpr ⟨s, by simp [Aset], rfl⟩
  have hhighA : Walk.supportIndex p t ∈ Aidx := by
    change Walk.supportIndex p t ∈
      Aset.toFinset.image (Walk.supportIndex p)
    exact Finset.mem_image.mpr ⟨t, by simp [Aset], rfl⟩
  have hB_bounds :
      forall b : Nat, b ∈ Bidx ->
        Walk.supportIndex p s <= b ∧ b <= Walk.supportIndex p t := by
    intro n hn
    rcases (by
      simpa [Bidx] using hn :
        Exists fun b : V => b ∈ Bset ∧ Walk.supportIndex p b = n) with
      ⟨b, hbB, hbEq⟩
    have hbP : b ∈ p.support := hbB.1
    constructor
    · rw [← hbEq]
      exact Walk.supportIndex_start_le (p := p)
    · rw [← hbEq]
      exact Walk.IsPath.supportIndex_le_end hp_path hbP
  have hno_between_idx :
      forall x : Nat, x ∈ Aidx ->
        forall b : Nat, b ∈ Bidx ->
          forall c : Nat, c ∈ Bidx ->
            b < x -> x < c -> False := by
    intro xi hxi bi hbi ci hci hbi_lt hxi_lt
    rcases (by
      simpa [Aidx] using hxi :
        Exists fun x : V => x ∈ Aset ∧ Walk.supportIndex p x = xi) with
      ⟨x, hxA, hxEq⟩
    rcases (by
      simpa [Bidx] using hbi :
        Exists fun b : V => b ∈ Bset ∧ Walk.supportIndex p b = bi) with
      ⟨b, hbB, hbEq⟩
    rcases (by
      simpa [Bidx] using hci :
        Exists fun c : V => c ∈ Bset ∧ Walk.supportIndex p c = ci) with
      ⟨c, hcB, hcEq⟩
    have hb_lt_x : Walk.supportIndex p b < Walk.supportIndex p x := by
      omega
    have hx_lt_c : Walk.supportIndex p x < Walk.supportIndex p c := by
      omega
    rcases hxA with hxAttach | hxst
    · exact hH.maximal_attachment_not_between_offPath_component_boundary
        hHmax hp_path hp_avoid D hxAttach hbB hcB hb_lt_x hx_lt_c
    · rcases hxst with hxs | hxt
      · subst x
        have hs_le_b : Walk.supportIndex p s <= Walk.supportIndex p b :=
          Walk.supportIndex_start_le (p := p)
        omega
      · subst x
        have hc_le_t : Walk.supportIndex p c <= Walk.supportIndex p t :=
          Walk.IsPath.supportIndex_le_end hp_path hcB.1
        omega
  obtain ⟨li, ri, hliA, hriA, hli_le_ri, hB_between, hA_gap⟩ :=
    Finset.Nat.exists_consecutive_bounds_of_no_between
      Aidx Bidx hBidx_nonempty
      (low := Walk.supportIndex p s) (high := Walk.supportIndex p t)
      hlowA hhighA hB_bounds hno_between_idx
  rcases (by
    simpa [Aidx] using hliA :
      Exists fun l : V => l ∈ Aset ∧ Walk.supportIndex p l = li) with
    ⟨l, hlAset, hlEq⟩
  rcases (by
    simpa [Aidx] using hriA :
      Exists fun r : V => r ∈ Aset ∧ Walk.supportIndex p r = ri) with
    ⟨r, hrAset, hrEq⟩
  refine ⟨l, r, by simpa [Aset] using hlAset, by simpa [Aset] using hrAset,
    hA_path hlAset, hA_path hrAset, ?_, ?_, ?_⟩
  · omega
  · intro b hbB
    have hbidx : Walk.supportIndex p b ∈ Bidx := by
      change Walk.supportIndex p b ∈
        Bset.toFinset.image (Walk.supportIndex p)
      exact Finset.mem_image.mpr ⟨b, by simpa [Bset] using hbB, rfl⟩
    have hbetween := hB_between (Walk.supportIndex p b) hbidx
    constructor <;> omega
  · intro x hxA hlx hxr
    have hxidx : Walk.supportIndex p x ∈ Aidx := by
      change Walk.supportIndex p x ∈
        Aset.toFinset.image (Walk.supportIndex p)
      exact Finset.mem_image.mpr ⟨x, by simpa [Aset] using hxA, rfl⟩
    exact hA_gap (Walk.supportIndex p x) hxidx (by omega) (by omega)

/-- An off-path component embeds into a component of the graph obtained by
deleting any two vertices of the avoiding path.  This is the formal component
version of passing from the source `K_i` interval to a side of
`G - {x_{i-1}, x_i}`. -/
theorem offPath_component_subset_deleted_pair_component
    {s t l r : V}
    {H : G.Subgraph}
    {p : G.Walk s t}
    (D :
      (G.induce {y : V | y ∉ H.verts ∧ y ∉ p.support}).ConnectedComponent)
    (hlP : l ∈ p.support)
    (hrP : r ∈ p.support) :
    Exists fun C : (G.induce (({l, r} : Set V)ᶜ)).ConnectedComponent =>
      induceComponentSupport (G := G) D ⊆
        induceComponentSupport (G := G) C := by
  classical
  have hD_connected :
      (G.induce (induceComponentSupport (G := G) D)).Connected :=
    induceComponentSupport_connected (G := G) D
  have hD_subset_pair_compl :
      induceComponentSupport (G := G) D ⊆ (({l, r} : Set V)ᶜ) := by
    intro v hvD hvPair
    have hvOff :
        v ∈ {y : V | y ∉ H.verts ∧ y ∉ p.support} :=
      induceComponentSupport_subset (G := G) D hvD
    rcases hvPair with hvl | hvr
    · subst v
      exact hvOff.2 hlP
    · subst v
      exact hvOff.2 hrP
  exact connected_set_subset_induceComponentSupport
    (G := G) hD_connected hD_subset_pair_compl

/-- An off-path component embeds into a component of
`(G - V(H)) - {l,r}` for any two vertices `l,r` on the avoiding path.

This is closer to the actual GM IX `(2.1)` proof than the ambient
`G - {l,r}` version: the source decomposes `K = G - V(H)`, so the separated
interval side is a component of `K` after deleting the two consecutive
attachment/end vertices. -/
theorem offPath_component_subset_deleted_pair_caught_complement_component
    {s t l r : V}
    {H : G.Subgraph}
    {p : G.Walk s t}
    (D :
      (G.induce {y : V | y ∉ H.verts ∧ y ∉ p.support}).ConnectedComponent)
    (hlP : l ∈ p.support)
    (hrP : r ∈ p.support) :
    Exists fun C :
      (G.induce {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)}).ConnectedComponent =>
      induceComponentSupport (G := G) D ⊆
        induceComponentSupport (G := G) C := by
  classical
  have hD_connected :
      (G.induce (induceComponentSupport (G := G) D)).Connected :=
    induceComponentSupport_connected (G := G) D
  have hD_subset :
      induceComponentSupport (G := G) D ⊆
        {v : V | v ∉ H.verts ∧ v ∉ ({l, r} : Set V)} := by
    intro v hvD
    have hvOff :
        v ∈ {y : V | y ∉ H.verts ∧ y ∉ p.support} :=
      induceComponentSupport_subset (G := G) D hvD
    refine ⟨hvOff.1, ?_⟩
    intro hvPair
    rcases hvPair with hvl | hvr
    · subst v
      exact hvOff.2 hlP
    · subst v
      exact hvOff.2 hrP
  exact connected_set_subset_induceComponentSupport
    (G := G) hD_connected hD_subset

/-- If a path starts in an off-path component and first reaches the caught
subgraph or the avoiding path at its endpoint, then the penultimate vertex is
still in the original off-path component.

This is the reusable first-contact kernel for the interval step in GM IX
`(2.1)`. -/
theorem offPath_component_penultimate_mem_of_clean_walk_to_caught_or_path
    {s t u y : V}
    {H : G.Subgraph}
    {p : G.Walk s t}
    (D :
      (G.induce {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (huD : u ∈ induceComponentSupport (G := G) D)
    (hyA : y ∈ H.verts ∨ y ∈ p.support)
    (q : G.Walk u y)
    (hq_path : q.IsPath)
    (hclean :
      forall z : V, z ∈ q.support ->
        (z ∈ H.verts ∨ z ∈ p.support) -> z = y) :
    q.penultimate ∈ induceComponentSupport (G := G) D ∧
      G.Adj q.penultimate y := by
  classical
  have huOff :
      u ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
    induceComponentSupport_subset (G := G) D huD
  have huy : u ≠ y := by
    intro huy
    subst y
    rcases hyA with hyH | hyP
    · exact huOff.1 hyH
    · exact huOff.2 hyP
  have hq_not_nil : Not q.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := q) huy
  have hpen_adj : G.Adj q.penultimate y :=
    q.adj_penultimate hq_not_nil
  have hpen_support_drop :
      q.penultimate ∈ q.dropLast.support := by
    simpa [SimpleGraph.Walk.support_dropLast hq_not_nil] using
      (SimpleGraph.Walk.penultimate_mem_dropLast_support hq_not_nil)
  have hdrop_support_off :
      forall z : V, z ∈ q.dropLast.support ->
        z ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} := by
    intro z hz
    have hzq : z ∈ q.support := by
      rw [SimpleGraph.Walk.support_dropLast hq_not_nil] at hz
      exact List.mem_of_mem_dropLast hz
    have hz_ne_y : z ≠ y := by
      intro hzy
      exact Walk.IsPath.end_notMem_walk_dropLast_support hq_path hq_not_nil
        (by simpa [hzy] using hz)
    constructor
    · intro hzH
      exact hz_ne_y (hclean z hzq (Or.inl hzH))
    · intro hzP
      exact hz_ne_y (hclean z hzq (Or.inr hzP))
  have hpenOff :
      q.penultimate ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
    hdrop_support_off q.penultimate hpen_support_drop
  have hpenD :
      q.penultimate ∈ induceComponentSupport (G := G) D :=
    induceComponentSupport_mem_of_walk
      (G := G) D huD hpenOff q.dropLast hdrop_support_off
  exact ⟨hpenD, hpen_adj⟩

/-- Clean first contact with the avoiding path is a relative-boundary vertex
of the off-path component. -/
theorem offPath_component_path_boundary_of_clean_walk_to_path
    {s t u b : V}
    {H : G.Subgraph}
    {p : G.Walk s t}
    (D :
      (G.induce {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (huD : u ∈ induceComponentSupport (G := G) D)
    (hbP : b ∈ p.support)
    (q : G.Walk u b)
    (hq_path : q.IsPath)
    (hclean :
      forall z : V, z ∈ q.support ->
        (z ∈ H.verts ∨ z ∈ p.support) -> z = b) :
    b ∈ relativeVertexBoundary G
      (induceComponentSupport (G := G) D)
      {v : V | v ∈ p.support} := by
  obtain ⟨wD, hwb⟩ :=
    offPath_component_penultimate_mem_of_clean_walk_to_caught_or_path
      (G := G) D huD (Or.inr hbP) q hq_path hclean
  exact ⟨hbP, q.penultimate, wD, hwb⟩

/-- A clean first contact from an off-path component to the caught subgraph is
impossible for a maximal GM IX `(2.1)` candidate. -/
theorem GM21Candidate.no_clean_walk_from_offPath_component_to_caught
    {Z : Set V}
    {s t u y : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    (D :
      (G.induce {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (huD : u ∈ induceComponentSupport (G := G) D)
    (hyH : y ∈ H.verts)
    (q : G.Walk u y)
    (hq_path : q.IsPath)
    (hclean :
      forall z : V, z ∈ q.support ->
        (z ∈ H.verts ∨ z ∈ p.support) -> z = y) :
    False := by
  obtain ⟨wD, hwy⟩ :=
    offPath_component_penultimate_mem_of_clean_walk_to_caught_or_path
      (G := G) D huD (Or.inl hyH) q hq_path hclean
  have hwOff :
      q.penultimate ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
    induceComponentSupport_subset (G := G) D wD
  exact hwOff.2
    (hH.maximal_adjacent_vertex_mem_path
      hHmax hp_path hp_avoid hwOff.1 hyH hwy)

/-- Any path from an off-path component to the caught subgraph or to the
avoiding path has a first contact on the avoiding path.

The first contact cannot be in the caught subgraph by maximality, so it is a
relative-boundary vertex of the off-path component on the avoiding path. -/
theorem GM21Candidate.exists_offPath_component_path_boundary_of_walk_to_caught_or_path
    [DecidableEq V]
    {Z : Set V}
    {s t u y : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    (D :
      (G.induce {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (huD : u ∈ induceComponentSupport (G := G) D)
    (hyA : y ∈ H.verts ∨ y ∈ p.support)
    (q : G.Walk u y)
    (hq_path : q.IsPath) :
    Exists fun b : V =>
      b ∈ relativeVertexBoundary G
        (induceComponentSupport (G := G) D)
        {v : V | v ∈ p.support} ∧
        b ∈ q.support := by
  classical
  let A : Set V := H.verts ∪ {v : V | v ∈ p.support}
  have hyA' : y ∈ A := by
    rcases hyA with hyH | hyP
    · exact Or.inl hyH
    · exact Or.inr hyP
  obtain ⟨x, hxq, hxA, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem
      (G := G) hq_path A hyA'
  let qx : G.Walk u x := q.takeUntil x hxq
  have hqx_path : qx.IsPath := by
    simpa [qx] using hq_path.takeUntil hxq
  have hclean :
      forall z : V, z ∈ qx.support ->
        (z ∈ H.verts ∨ z ∈ p.support) -> z = x := by
    intro z hz hzA
    exact hfirst z (by simpa [qx] using hz) (by
      rcases hzA with hzH | hzP
      · exact Or.inl hzH
      · exact Or.inr hzP)
  rcases hxA with hxH | hxP
  · exact False.elim
      (hH.no_clean_walk_from_offPath_component_to_caught
        hHmax hp_path hp_avoid D huD hxH qx hqx_path hclean)
  · refine ⟨x, ?_, hxq⟩
    exact offPath_component_path_boundary_of_clean_walk_to_path
      (G := G) D huD hxP qx hqx_path hclean

/-- Component version of
`exists_offPath_component_path_boundary_of_walk_to_caught_or_path`.

If a connected component containing an off-path component also contains a
vertex of `V(H) ∪ V(P)`, then one of the original off-path component's
path-boundary vertices lies in the containing component. -/
theorem GM21Candidate.exists_offPath_boundary_in_component_of_mem_caught_or_path
    [DecidableEq V]
    {Z K : Set V}
    {s t y : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    (D :
      (G.induce {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent)
    (C : (G.induce K).ConnectedComponent)
    (hD_subset :
      induceComponentSupport (G := G) D ⊆
        induceComponentSupport (G := G) C)
    (hyC : y ∈ induceComponentSupport (G := G) C)
    (hyA : y ∈ H.verts ∨ y ∈ p.support) :
    Exists fun b : V =>
      b ∈ relativeVertexBoundary G
        (induceComponentSupport (G := G) D)
        {v : V | v ∈ p.support} ∧
        b ∈ induceComponentSupport (G := G) C := by
  classical
  obtain ⟨u, huD⟩ := induceComponentSupport_nonempty (G := G) D
  have huC : u ∈ induceComponentSupport (G := G) C :=
    hD_subset huD
  obtain ⟨q, hq_path, hq_support⟩ :=
    connected_induce_exists_path_support_subset
      (G := G) (induceComponentSupport_connected (G := G) C)
      huC hyC
  obtain ⟨b, hbBoundary, hbq⟩ :=
    hH.exists_offPath_component_path_boundary_of_walk_to_caught_or_path
      hHmax hp_path hp_avoid D huD hyA q hq_path
  exact ⟨b, hbBoundary, hq_support b hbq⟩

theorem GM21Candidate.attachmentSet_disjoint_caught_set_of_maximal
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts) :
    Disjoint (GM21AttachmentSet (G := G) H) Z := by
  rw [Set.disjoint_left]
  intro x hx hz
  have hxP : x ∈ p.support :=
    hH.maximal_attachmentSet_subset_path hHmax hp_path hp_avoid hx
  exact hH.caught_vertex_not_mem_avoiding_path hp_avoid hz hxP

theorem GM21Candidate.maximal_no_adjacent_off_path_to_caught
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    {x y : V}
    (hx_not_H : x ∉ H.verts)
    (hx_not_p : x ∉ p.support)
    (hyH : y ∈ H.verts)
    (hxy : G.Adj x y) :
    False := by
  exact hx_not_p
    (hH.maximal_adjacent_vertex_mem_path hHmax hp_path hp_avoid
      hx_not_H hyH hxy)

theorem GM21Candidate.offPath_component_closed_with_path_boundary
    {Z : Set V}
    {s t : V}
    {H : G.Subgraph}
    (hH : GM21Candidate (G := G) Z s t H)
    (hHmax :
      forall H' : G.Subgraph,
        GM21Candidate (G := G) Z s t H' ->
          H ≤ H' -> H' ≤ H)
    {p : G.Walk s t}
    (hp_path : p.IsPath)
    (hp_avoid : Walk.AvoidsSet p H.verts)
    (C :
      (G.induce {v : V | v ∉ H.verts ∧ v ∉ p.support}).ConnectedComponent) :
    forall {a b : V},
      a ∈ induceComponentSupport (G := G) C ->
        b ∉ induceComponentSupport (G := G) C ->
          b ∉
            relativeVertexBoundary G
              (induceComponentSupport (G := G) C)
              {v : V | v ∈ p.support} ->
            Not (G.Adj a b) := by
  intro a b ha hbK hb_boundary hab
  have haA :
      a ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
    induceComponentSupport_subset (G := G) C ha
  by_cases hbP : b ∈ p.support
  · exact hb_boundary ⟨hbP, a, ha, hab⟩
  · by_cases hbH : b ∈ H.verts
    · exact hH.maximal_no_adjacent_off_path_to_caught
        hHmax hp_path hp_avoid haA.1 haA.2 hbH hab
    · have hbA : b ∈ {v : V | v ∉ H.verts ∧ v ∉ p.support} :=
        ⟨hbH, hbP⟩
      exact hbK
        (induceComponentSupport_mem_of_adj (G := G) C ha hbA hab)

end GMIX21

end Schematic.Math.GraphTheory
