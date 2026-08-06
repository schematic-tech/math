import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.EndpointReplacements

/-! Full and partial three-vertex linkage interfaces. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

structure VertexDisjointLinkage
    {V : Type u} (G : SimpleGraph V) (left right : Fin 3 -> V) where
  path : forall i : Fin 3, G.Walk (left i) (right i)
  isPath : forall i : Fin 3, (path i).IsPath
  pairwise_internally_vertex_disjoint :
    forall i j : Fin 3,
      i ≠ j ->
      Disjoint (Walk.InternalVertices (path i)) (Walk.InternalVertices (path j))

def HasVertexDisjointLinkage
    {V : Type u} (G : SimpleGraph V) (left right : Fin 3 -> V) : Prop :=
  Nonempty (VertexDisjointLinkage G left right)

/--
A stronger linkage package for the set-to-set form of the three-path Menger
application used in the main induction.  The paper only needs three paths
between two triples of vertices, and the matching of the target triple may be
chosen after applying Menger.

The reference form is the finite vertex version of Menger's theorem; see
Diestel, *Graph Theory*, 5th ed., Theorem 3.3.1, and the use in
`2605.10112_tex/main.tex`, line 450.
-/
structure ThreeVertexLinkage
    {V : Type u} (G : SimpleGraph V) (left right : Fin 3 -> V) where
  targetEquiv : Fin 3 ≃ Fin 3
  path : forall i : Fin 3, G.Walk (left i) (right (targetEquiv i))
  isPath : forall i : Fin 3, (path i).IsPath
  pairwise_vertex_disjoint :
    forall i j : Fin 3,
      i ≠ j ->
        Disjoint {v : V | v ∈ (path i).support}
          {v : V | v ∈ (path j).support}

def HasThreeVertexLinkage
    {V : Type u} (G : SimpleGraph V) (left right : Fin 3 -> V) : Prop :=
  Nonempty (ThreeVertexLinkage G left right)

theorem ThreeVertexLinkage.right_injective
    {V : Type u} {G : SimpleGraph V} {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right) :
    Function.Injective right := by
  intro a b hab
  by_contra hne
  let i : Fin 3 := L.targetEquiv.symm a
  let j : Fin 3 := L.targetEquiv.symm b
  have hij : i ≠ j := by
    intro hij
    exact hne (by
      have h := congrArg L.targetEquiv hij
      simpa [i, j] using h)
  have hi_end : right a ∈ (L.path i).support := by
    simpa [i] using (L.path i).end_mem_support
  have hj_end : right a ∈ (L.path j).support := by
    simpa [j, hab] using (L.path j).end_mem_support
  exact
    Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij)
      hi_end hj_end

/-- Map a three-vertex linkage in a subgraph to the ambient graph.

This is the graph-theoretic bridge needed for the GM IX `(2.2)` step in
`GeneralSociety`: the augmenting/linkage argument is most naturally applied
after deleting the forbidden rim interiors.  Once the linkage is found in that
subgraph, this constructor forgets the subtype vertices while preserving the
permuted target matching and full vertex-disjointness. -/
def ThreeVertexLinkage.mapSubgraph
    {V : Type u} {G : SimpleGraph V}
    {H : G.Subgraph}
    {left right : Fin 3 -> H.verts}
    (L : ThreeVertexLinkage H.coe left right) :
    ThreeVertexLinkage G
      (fun i : Fin 3 => (left i : V))
      (fun i : Fin 3 => (right i : V)) where
  targetEquiv := L.targetEquiv
  path i := (L.path i).map H.hom
  isPath i :=
    SimpleGraph.Walk.map_isPath_of_injective
      (f := H.hom) SimpleGraph.Subgraph.hom_injective (L.isPath i)
  pairwise_vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := H) (L.path i)).mp hzi with
      ⟨zi, hzi_support, hzi_eq⟩
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := H) (L.path j)).mp hzj with
      ⟨zj, hzj_support, hzj_eq⟩
    have hzij : zi = zj := by
      apply Subtype.ext
      exact hzi_eq.trans hzj_eq.symm
    exact Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij)
      hzi_support (by simpa [hzij] using hzj_support)

/-- If the subgraph used for a transported linkage meets each forbidden set
only in the three left terminals, then every transported linkage path meets
those forbidden sets only at its own left terminal.

The last sentence is stronger than the raw subgraph hypothesis because the
linkage paths are pairwise vertex-disjoint: a path cannot pass through another
path's left terminal, since that terminal is on the other path. -/
theorem ThreeVertexLinkage.mapSubgraph_meets_sets_only_at_left
    {V : Type u} {G : SimpleGraph V}
    {H : G.Subgraph}
    {left right : Fin 3 -> H.verts}
    (L : ThreeVertexLinkage H.coe left right)
    (sets : Fin 3 -> Set V)
    (hH_meets_sets_only_at_left :
      forall (v : H.verts) (s : Fin 3),
        (v : V) ∈ sets s ->
          Exists fun r : Fin 3 => (v : V) = (left r : V)) :
    forall r s : Fin 3, forall z : V,
      z ∈ ((L.mapSubgraph).path r).support ->
        z ∈ sets s ->
          z = (left r : V) := by
  intro r s z hz_path hz_set
  rcases (Walk.mem_support_map_subgraph_hom_iff
    (H := H) (L.path r)).mp hz_path with
    ⟨zH, hzH_support, hzH_eq⟩
  rcases hH_meets_sets_only_at_left zH s (by simpa [hzH_eq] using hz_set) with
    ⟨m, hm⟩
  by_cases hmr : m = r
  · simpa [hzH_eq, hmr] using hm
  · have hzH_left_m : zH = left m := by
      apply Subtype.ext
      exact hm
    have hleft_m_on_path_m : left m ∈ (L.path m).support :=
      (L.path m).start_mem_support
    exact False.elim
      (Set.disjoint_left.mp (L.pairwise_vertex_disjoint r m (fun hrm => hmr hrm.symm))
        hzH_support
        (hzH_left_m.symm ▸ hleft_m_on_path_m))

structure PartialThreeVertexLinkage
    {V : Type u} (G : SimpleGraph V) (left right : Fin 3 -> V) (n : Nat) where
  leftIndex : Fin n -> Fin 3
  rightIndex : Fin n -> Fin 3
  leftIndex_injective : Function.Injective leftIndex
  rightIndex_injective : Function.Injective rightIndex
  path : forall i : Fin n, G.Walk (left (leftIndex i)) (right (rightIndex i))
  isPath : forall i : Fin n, (path i).IsPath
  pairwise_vertex_disjoint :
    forall i j : Fin n, i ≠ j ->
      Disjoint {v : V | v ∈ (path i).support}
        {v : V | v ∈ (path j).support}

def HasPartialThreeVertexLinkage
    {V : Type u} (G : SimpleGraph V) (left right : Fin 3 -> V) (n : Nat) : Prop :=
  Nonempty (PartialThreeVertexLinkage G left right n)

def PartialThreeVertexLinkage.symm
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    PartialThreeVertexLinkage G right left n where
  leftIndex := L.rightIndex
  rightIndex := L.leftIndex
  leftIndex_injective := L.rightIndex_injective
  rightIndex_injective := L.leftIndex_injective
  path i := (L.path i).reverse
  isPath i := (L.isPath i).reverse
  pairwise_vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij)
      (by simpa [SimpleGraph.Walk.support_reverse] using hxi)
      (by simpa [SimpleGraph.Walk.support_reverse] using hxj)

theorem HasPartialThreeVertexLinkage.symm
    {left right : Fin 3 -> V} {n : Nat}
    (h : HasPartialThreeVertexLinkage G left right n) :
    HasPartialThreeVertexLinkage G right left n := by
  rcases h with ⟨L⟩
  exact ⟨L.symm⟩

def PartialThreeVertexLinkage.empty
    {left right : Fin 3 -> V} :
    PartialThreeVertexLinkage G left right 0 where
  leftIndex i := Fin.elim0 i
  rightIndex i := Fin.elim0 i
  leftIndex_injective := by intro i; exact Fin.elim0 i
  rightIndex_injective := by intro i; exact Fin.elim0 i
  path i := Fin.elim0 i
  isPath i := Fin.elim0 i
  pairwise_vertex_disjoint i := Fin.elim0 i

def PartialThreeVertexLinkage.ofOnePath
    {left right : Fin 3 -> V}
    {i j : Fin 3}
    (p : G.Walk (left i) (right j))
    (hp : p.IsPath) :
    PartialThreeVertexLinkage G left right 1 where
  leftIndex _ := i
  rightIndex _ := j
  leftIndex_injective := by
    intro a b _
    exact Subsingleton.elim a b
  rightIndex_injective := by
    intro a b _
    exact Subsingleton.elim a b
  path _ := p
  isPath _ := hp
  pairwise_vertex_disjoint := by
    intro a b hab
    exact False.elim (hab (Subsingleton.elim a b))

/-- Build a two-path partial linkage from two explicitly disjoint paths.

This is the concrete partial-linkage constructor used by the GM IX `(2.2)`
endpoint cases, where one or two endpoint paths are fixed before running the
augmenting-path extension. -/
def PartialThreeVertexLinkage.ofTwoPaths
    {left right : Fin 3 -> V}
    {i₀ i₁ j₀ j₁ : Fin 3}
    (hi : i₀ ≠ i₁)
    (hj : j₀ ≠ j₁)
    (p₀ : G.Walk (left i₀) (right j₀))
    (p₁ : G.Walk (left i₁) (right j₁))
    (hp₀ : p₀.IsPath)
    (hp₁ : p₁.IsPath)
    (hdisj :
      Disjoint {v : V | v ∈ p₀.support}
        {v : V | v ∈ p₁.support}) :
    PartialThreeVertexLinkage G left right 2 where
  leftIndex
    | 0 => i₀
    | 1 => i₁
  rightIndex
    | 0 => j₀
    | 1 => j₁
  leftIndex_injective := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · exact False.elim (hi hab)
    · exact False.elim (hi hab.symm)
  rightIndex_injective := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · exact False.elim (hj hab)
    · exact False.elim (hj hab.symm)
  path
    | 0 => p₀
    | 1 => p₁
  isPath
    | 0 => hp₀
    | 1 => hp₁
  pairwise_vertex_disjoint := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact False.elim (hab rfl)
    · simpa using hdisj
    · simpa using hdisj.symm
    · exact False.elim (hab rfl)

def PartialThreeVertexLinkage.usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) : Set V :=
  {v : V | Exists fun i : Fin n => v ∈ (L.path i).support}

theorem PartialThreeVertexLinkage.symm_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.symm.usedVertices = L.usedVertices := by
  ext v
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by
      simpa [PartialThreeVertexLinkage.symm,
        SimpleGraph.Walk.support_reverse] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by
      simpa [PartialThreeVertexLinkage.symm,
        SimpleGraph.Walk.support_reverse] using hi⟩

theorem PartialThreeVertexLinkage.left_mem_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (i : Fin n) :
    left (L.leftIndex i) ∈ L.usedVertices :=
  ⟨i, (L.path i).start_mem_support⟩

theorem PartialThreeVertexLinkage.right_mem_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (i : Fin n) :
    right (L.rightIndex i) ∈ L.usedVertices :=
  ⟨i, (L.path i).end_mem_support⟩

theorem PartialThreeVertexLinkage.eq_of_mem_path_supports
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {i j : Fin n} {v : V}
    (hvi : v ∈ (L.path i).support)
    (hvj : v ∈ (L.path j).support) :
    i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij) hvi hvj

theorem PartialThreeVertexLinkage.card_le_usedVertices_ncard_of_left_injective
    [Fintype V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hleft : Function.Injective left) :
    n <= L.usedVertices.ncard := by
  classical
  let f : Fin n -> L.usedVertices := fun k =>
    ⟨left (L.leftIndex k), L.left_mem_usedVertices k⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply L.leftIndex_injective
    apply hleft
    exact congrArg Subtype.val hab
  have hcard : Fintype.card (Fin n) <= Fintype.card L.usedVertices :=
    Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hcard
  rwa [Set.fintypeCard_eq_ncard] at hcard

theorem PartialThreeVertexLinkage.card_le_usedVertices_ncard_of_right_injective
    [Fintype V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hright : Function.Injective right) :
    n <= L.usedVertices.ncard := by
  classical
  let f : Fin n -> L.usedVertices := fun k =>
    ⟨right (L.rightIndex k), L.right_mem_usedVertices k⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply L.rightIndex_injective
    apply hright
    exact congrArg Subtype.val hab
  have hcard : Fintype.card (Fin n) <= Fintype.card L.usedVertices :=
    Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hcard
  rwa [Set.fintypeCard_eq_ncard] at hcard

theorem Walk.IsPath.dart_snd_eq_of_fst_eq
    [DecidableEq V]
    {a b : V} {p : G.Walk a b}
    (hp : p.IsPath)
    {d e : G.Dart}
    (hd : d ∈ p.darts)
    (he : e ∈ p.darts)
    (hfst : d.fst = e.fst) :
    d.snd = e.snd := by
  obtain ⟨m, hm, hgetm⟩ := List.getElem_of_mem hd
  obtain ⟨r, hr, hgetr⟩ := List.getElem_of_mem he
  have hm_len : m < p.length := by
    simpa [SimpleGraph.Walk.length_darts] using hm
  have hr_len : r < p.length := by
    simpa [SimpleGraph.Walk.length_darts] using hr
  have hm_support : m < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hr_support : r < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hm_succ_support : m + 1 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hr_succ_support : r + 1 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hdm := p.darts_getElem_eq_getVert m hm
  have hdr := p.darts_getElem_eq_getVert r hr
  have hfst_m : p.getVert m = d.fst := by
    have hfst_get : (p.darts[m]'hm).fst = d.fst := by
      rw [hgetm]
    rw [hdm] at hfst_get
    exact hfst_get
  have hfst_r : p.getVert r = e.fst := by
    have hfst_get : (p.darts[r]'hr).fst = e.fst := by
      rw [hgetr]
    rw [hdr] at hfst_get
    exact hfst_get
  have hsnd_m : p.getVert (m + 1) = d.snd := by
    have hsnd_get : (p.darts[m]'hm).snd = d.snd := by
      rw [hgetm]
    rw [hdm] at hsnd_get
    exact hsnd_get
  have hsnd_r : p.getVert (r + 1) = e.snd := by
    have hsnd_get : (p.darts[r]'hr).snd = e.snd := by
      rw [hgetr]
    rw [hdr] at hsnd_get
    exact hsnd_get
  have hsupport_m : p.support[m]'hm_support = d.fst := by
    rw [← p.getVert_eq_support_getElem (n := m) (by omega)]
    exact hfst_m
  have hsupport_r : p.support[r]'hr_support = e.fst := by
    rw [← p.getVert_eq_support_getElem (n := r) (by omega)]
    exact hfst_r
  have hm_eq_r : m = r := by
    have hsame :
        p.support[m]'hm_support = p.support[r]'hr_support := by
      rw [hsupport_m, hsupport_r, hfst]
    exact hp.support_nodup.getElem_inj_iff.mp hsame
  have hsupport_ms :
      p.support[m + 1]'hm_succ_support = d.snd := by
    rw [← p.getVert_eq_support_getElem (n := m + 1) (by omega)]
    exact hsnd_m
  have hsupport_rs :
      p.support[r + 1]'hr_succ_support = e.snd := by
    rw [← p.getVert_eq_support_getElem (n := r + 1) (by omega)]
    exact hsnd_r
  have hs :
      p.support[m + 1]'hm_succ_support =
        p.support[r + 1]'hr_succ_support := by
    subst r
    rfl
  simpa [hsupport_ms, hsupport_rs] using hs

theorem Walk.IsPath.dart_fst_eq_of_snd_eq
    [DecidableEq V]
    {a b : V} {p : G.Walk a b}
    (hp : p.IsPath)
    {d e : G.Dart}
    (hd : d ∈ p.darts)
    (he : e ∈ p.darts)
    (hsnd : d.snd = e.snd) :
    d.fst = e.fst := by
  have hsnd_rev :
      d.symm.fst = e.symm.fst := by
    simpa using hsnd
  have hd_rev : d.symm ∈ p.reverse.darts := by
    rw [SimpleGraph.Walk.mem_darts_reverse]
    exact hd
  have he_rev : e.symm ∈ p.reverse.darts := by
    rw [SimpleGraph.Walk.mem_darts_reverse]
    exact he
  have h := Walk.IsPath.dart_snd_eq_of_fst_eq
    (G := G) hp.reverse hd_rev he_rev hsnd_rev
  simpa using h

def PartialThreeVertexLinkage.ForwardPathDart
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (u v : V) : Prop :=
  Exists fun i : Fin n =>
    Exists fun h : G.Adj u v =>
      (⟨(u, v), h⟩ : G.Dart) ∈ (L.path i).darts

theorem PartialThreeVertexLinkage.ForwardPathDart.adj
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : L.ForwardPathDart u v) :
    G.Adj u v := by
  rcases h with ⟨_i, huv, _hdart⟩
  exact huv

theorem PartialThreeVertexLinkage.ForwardPathDart.fst_mem_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : L.ForwardPathDart u v) :
    u ∈ L.usedVertices := by
  rcases h with ⟨i, huv, hdart⟩
  exact ⟨i, (L.path i).dart_fst_mem_support_of_mem_darts
    (d := (⟨(u, v), huv⟩ : G.Dart)) hdart⟩

theorem PartialThreeVertexLinkage.ForwardPathDart.snd_mem_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : L.ForwardPathDart u v) :
    v ∈ L.usedVertices := by
  rcases h with ⟨i, huv, hdart⟩
  exact ⟨i, (L.path i).dart_snd_mem_support_of_mem_darts
    (d := (⟨(u, v), huv⟩ : G.Dart)) hdart⟩

theorem PartialThreeVertexLinkage.symm_forwardPathDart_iff
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) {u v : V} :
    L.symm.ForwardPathDart u v ↔ L.ForwardPathDart v u := by
  constructor
  · rintro ⟨i, huv, hdart⟩
    refine ⟨i, huv.symm, ?_⟩
    have hdart' :
        ((⟨(u, v), huv⟩ : G.Dart).symm) ∈ (L.path i).darts := by
      simpa [PartialThreeVertexLinkage.symm] using
        (SimpleGraph.Walk.mem_darts_reverse.mp hdart)
    simpa using hdart'
  · rintro ⟨i, hvu, hdart⟩
    refine ⟨i, hvu.symm, ?_⟩
    have hdart' :
        ((⟨(v, u), hvu⟩ : G.Dart).symm) ∈
          ((L.path i).reverse).darts := by
      rw [SimpleGraph.Walk.mem_darts_reverse]
      simpa using hdart
    simpa [PartialThreeVertexLinkage.symm] using hdart'

theorem PartialThreeVertexLinkage.ForwardPathDart.snd_mem_path_of_fst_mem
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : L.ForwardPathDart u v)
    {k : Fin n}
    (hu : u ∈ (L.path k).support) :
    v ∈ (L.path k).support := by
  rcases h with ⟨i, huv, hdart⟩
  by_cases hik : i = k
  · subst k
    exact (L.path i).dart_snd_mem_support_of_mem_darts
      (d := (⟨(u, v), huv⟩ : G.Dart)) hdart
  · have hui : u ∈ (L.path i).support :=
      (L.path i).dart_fst_mem_support_of_mem_darts
        (d := (⟨(u, v), huv⟩ : G.Dart)) hdart
    exact False.elim
      (Set.disjoint_left.mp (L.pairwise_vertex_disjoint i k hik) hui hu)

theorem PartialThreeVertexLinkage.ForwardPathDart.fst_mem_path_of_snd_mem
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : L.ForwardPathDart u v)
    {k : Fin n}
    (hv : v ∈ (L.path k).support) :
    u ∈ (L.path k).support := by
  rcases h with ⟨i, huv, hdart⟩
  by_cases hik : i = k
  · subst k
    exact (L.path i).dart_fst_mem_support_of_mem_darts
      (d := (⟨(u, v), huv⟩ : G.Dart)) hdart
  · have hvi : v ∈ (L.path i).support :=
      (L.path i).dart_snd_mem_support_of_mem_darts
        (d := (⟨(u, v), huv⟩ : G.Dart)) hdart
    exact False.elim
      (Set.disjoint_left.mp (L.pairwise_vertex_disjoint i k hik) hvi hv)

theorem PartialThreeVertexLinkage.ForwardPathDart.snd_unique_of_fst
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v w : V}
    (hv : L.ForwardPathDart u v)
    (hw : L.ForwardPathDart u w) :
    v = w := by
  rcases hv with ⟨i, huv, hdartv⟩
  rcases hw with ⟨j, huw, hdartw⟩
  have hui : u ∈ (L.path i).support :=
    (L.path i).dart_fst_mem_support_of_mem_darts
      (d := (⟨(u, v), huv⟩ : G.Dart)) hdartv
  have huj : u ∈ (L.path j).support :=
    (L.path j).dart_fst_mem_support_of_mem_darts
      (d := (⟨(u, w), huw⟩ : G.Dart)) hdartw
  have hij : i = j := L.eq_of_mem_path_supports hui huj
  subst j
  have h :=
    Walk.IsPath.dart_snd_eq_of_fst_eq
      (G := G) (L.isPath i)
      (d := (⟨(u, v), huv⟩ : G.Dart))
      (e := (⟨(u, w), huw⟩ : G.Dart))
      hdartv hdartw (by simp)
  simpa using h

theorem PartialThreeVertexLinkage.ForwardPathDart.fst_unique_of_snd
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v w : V}
    (hu : L.ForwardPathDart u w)
    (hv : L.ForwardPathDart v w) :
    u = v := by
  rcases hu with ⟨i, huw, hdartu⟩
  rcases hv with ⟨j, hvw, hdartv⟩
  have hwi : w ∈ (L.path i).support :=
    (L.path i).dart_snd_mem_support_of_mem_darts
      (d := (⟨(u, w), huw⟩ : G.Dart)) hdartu
  have hwj : w ∈ (L.path j).support :=
    (L.path j).dart_snd_mem_support_of_mem_darts
      (d := (⟨(v, w), hvw⟩ : G.Dart)) hdartv
  have hij : i = j := L.eq_of_mem_path_supports hwi hwj
  subst j
  have h :=
    Walk.IsPath.dart_fst_eq_of_snd_eq
      (G := G) (L.isPath i)
      (d := (⟨(u, w), huw⟩ : G.Dart))
      (e := (⟨(v, w), hvw⟩ : G.Dart))
      hdartu hdartv (by simp)
  simpa using h

theorem PartialThreeVertexLinkage.ForwardPathDart.idxOf_fst_lt_idxOf_snd_of_fst_mem
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : L.ForwardPathDart u v)
    {k : Fin n}
    (hu : u ∈ (L.path k).support) :
    (L.path k).support.idxOf u < (L.path k).support.idxOf v := by
  rcases h with ⟨i, huv, hdart⟩
  by_cases hik : i = k
  · subst k
    simpa using
      Walk.IsPath.idxOf_fst_lt_idxOf_snd_of_mem_darts
        (G := G) (L.isPath i)
        (d := (⟨(u, v), huv⟩ : G.Dart)) hdart
  · have hui : u ∈ (L.path i).support :=
      (L.path i).dart_fst_mem_support_of_mem_darts
        (d := (⟨(u, v), huv⟩ : G.Dart)) hdart
    exact False.elim
      (Set.disjoint_left.mp (L.pairwise_vertex_disjoint i k hik) hui hu)


end Schematic.Math.GraphTheory
