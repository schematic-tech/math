import Schematic.Math.GraphTheory.Minors.Rerouting.SetLinkages

/-! Constructing partial set linkages and their residual reachability. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace PartialSetLinkage

def empty (G : SimpleGraph V) (X Y : Set V) :
    PartialSetLinkage G X Y 0 where
  source i := Fin.elim0 i
  target i := Fin.elim0 i
  source_mem i := Fin.elim0 i
  target_mem i := Fin.elim0 i
  source_injective i := Fin.elim0 i
  target_injective i := Fin.elim0 i
  path i := Fin.elim0 i
  isPath i := Fin.elim0 i
  pairwise_vertex_disjoint i := Fin.elim0 i
  source_clean i := Fin.elim0 i
  target_clean i := Fin.elim0 i

/-- A single endpoint-clean `X -> Y` path as a partial linkage. -/
def ofOnePath
    {X Y : Set V} {x y : V}
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hx : x ∈ X)
    (hy : y ∈ Y)
    (hsource :
      forall z : V, z ∈ p.support -> z ∈ X -> z = x)
    (htarget :
      forall z : V, z ∈ p.support -> z ∈ Y -> z = y) :
    PartialSetLinkage G X Y 1 where
  source _ := x
  target _ := y
  source_mem _ := hx
  target_mem _ := hy
  source_injective i j _ := Subsingleton.elim i j
  target_injective i j _ := Subsingleton.elim i j
  path _ := p
  isPath _ := hp
  pairwise_vertex_disjoint i j hij :=
    False.elim (hij (Subsingleton.elim i j))
  source_clean _ := hsource
  target_clean _ := htarget

/-- Two disjoint endpoint-clean `X -> Y` paths as a partial set linkage.

This is the order-two input used in GM IX `(2.2)`: both selected source and
target pairs are retained when the augmenting-path construction completes the
family to order three. -/
def ofTwoPaths
    {X Y : Set V} {x0 y0 x1 y1 : V}
    (p0 : G.Walk x0 y0) (p1 : G.Walk x1 y1)
    (hp0 : p0.IsPath) (hp1 : p1.IsPath)
    (hx0 : x0 ∈ X) (hx1 : x1 ∈ X)
    (hy0 : y0 ∈ Y) (hy1 : y1 ∈ Y)
    (hx_ne : x0 ≠ x1) (hy_ne : y0 ≠ y1)
    (hdisjoint :
      Disjoint {z : V | z ∈ p0.support} {z : V | z ∈ p1.support})
    (hsource0 :
      forall z : V, z ∈ p0.support -> z ∈ X -> z = x0)
    (hsource1 :
      forall z : V, z ∈ p1.support -> z ∈ X -> z = x1)
    (htarget0 :
      forall z : V, z ∈ p0.support -> z ∈ Y -> z = y0)
    (htarget1 :
      forall z : V, z ∈ p1.support -> z ∈ Y -> z = y1) :
    PartialSetLinkage G X Y 2 where
  source
    | 0 => x0
    | 1 => x1
  target
    | 0 => y0
    | 1 => y1
  source_mem i := by fin_cases i <;> assumption
  target_mem i := by fin_cases i <;> assumption
  source_injective i j hij := by
    fin_cases i <;> fin_cases j <;> simp_all
  target_injective i j hij := by
    fin_cases i <;> fin_cases j <;> simp_all
  path
    | 0 => p0
    | 1 => p1
  isPath i := by fin_cases i <;> assumption
  pairwise_vertex_disjoint i j hij := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact False.elim (hij rfl)
  source_clean i := by
    fin_cases i
    · exact hsource0
    · exact hsource1
  target_clean i := by
    fin_cases i
    · exact htarget0
    · exact htarget1

def usedVertices
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) : Set V :=
  {v : V | Exists fun i : Fin n => v ∈ (L.path i).support}

def sourceSet
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) : Set V :=
  Set.range L.source

def targetSet
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) : Set V :=
  Set.range L.target

theorem sourceSet_subset_endpointSet
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    L.sourceSet ⊆ X := by
  rintro _ ⟨i, rfl⟩
  exact L.source_mem i

theorem targetSet_subset_endpointSet
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    L.targetSet ⊆ Y := by
  rintro _ ⟨i, rfl⟩
  exact L.target_mem i

theorem source_mem_usedVertices
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) (i : Fin n) :
    L.source i ∈ L.usedVertices :=
  ⟨i, (L.path i).start_mem_support⟩

theorem target_mem_usedVertices
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) (i : Fin n) :
    L.target i ∈ L.usedVertices :=
  ⟨i, (L.path i).end_mem_support⟩

/--
Endpoint cleanliness identifies exactly which source-set vertices are already
used by a partial linkage.
-/
theorem usedVertices_inter_sourceSet
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    L.usedVertices ∩ X = L.sourceSet := by
  ext z
  constructor
  · rintro ⟨⟨i, hzi⟩, hzX⟩
    exact ⟨i, (L.source_clean i z hzi hzX).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨L.source_mem_usedVertices i, L.source_mem i⟩

/--
Endpoint cleanliness identifies exactly which target-set vertices are already
used by a partial linkage.
-/
theorem usedVertices_inter_targetSet
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    L.usedVertices ∩ Y = L.targetSet := by
  ext z
  constructor
  · rintro ⟨⟨i, hzi⟩, hzY⟩
    exact ⟨i, (L.target_clean i z hzi hzY).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨L.target_mem_usedVertices i, L.target_mem i⟩

theorem source_not_used_iff_not_selected
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) {x : V}
    (hx : x ∈ X) :
    x ∉ L.usedVertices ↔ x ∉ L.sourceSet := by
  constructor
  · intro hunused hselected
    exact hunused
      ((Set.ext_iff.mp L.usedVertices_inter_sourceSet x).mpr hselected).1
  · intro hnotSelected hused
    exact hnotSelected ((Set.ext_iff.mp L.usedVertices_inter_sourceSet x).mp
      ⟨hused, hx⟩)

theorem target_not_used_iff_not_selected
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) {y : V}
    (hy : y ∈ Y) :
    y ∉ L.usedVertices ↔ y ∉ L.targetSet := by
  constructor
  · intro hunused hselected
    exact hunused
      ((Set.ext_iff.mp L.usedVertices_inter_targetSet y).mpr hselected).1
  · intro hnotSelected hused
    exact hnotSelected ((Set.ext_iff.mp L.usedVertices_inter_targetSet y).mp
      ⟨hused, hy⟩)

/-- A directed edge currently used by one of the partial linkage paths. -/
def ForwardPathDart
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) (u v : V) : Prop :=
  Exists fun i : Fin n =>
    Exists fun h : G.Adj u v =>
      (⟨(u, v), h⟩ : G.Dart) ∈ (L.path i).darts

theorem ForwardPathDart.adj
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n} {u v : V}
    (h : L.ForwardPathDart u v) :
    G.Adj u v := by
  rcases h with ⟨_i, huv, _⟩
  exact huv

theorem ForwardPathDart.fst_mem_usedVertices
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n} {u v : V}
    (h : L.ForwardPathDart u v) :
    u ∈ L.usedVertices := by
  rcases h with ⟨i, huv, hd⟩
  exact ⟨i, (L.path i).dart_fst_mem_support_of_mem_darts
    (d := (⟨(u, v), huv⟩ : G.Dart)) hd⟩

theorem ForwardPathDart.snd_mem_usedVertices
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n} {u v : V}
    (h : L.ForwardPathDart u v) :
    v ∈ L.usedVertices := by
  rcases h with ⟨i, huv, hd⟩
  exact ⟨i, (L.path i).dart_snd_mem_support_of_mem_darts
    (d := (⟨(u, v), huv⟩ : G.Dart)) hd⟩

theorem eq_of_mem_path_supports
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    {i j : Fin n} {v : V}
    (hvi : v ∈ (L.path i).support)
    (hvj : v ∈ (L.path j).support) :
    i = j := by
  by_contra hij
  exact
    Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij) hvi hvj

/--
The endpoint-clean split residual network for a partial `X -> Y` linkage.

The capacity and reverse-flow arcs are the usual vertex-disjoint-linkage
residual arcs.  A fresh graph edge may be traversed only away from `Y` and
into a vertex outside `X`.  Thus a residual chain can start at an unused
source and end at an unused target, but cannot pass through another endpoint
of either set.
-/
def SplitResidualStep
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    VertexSplitState V -> VertexSplitState V -> Prop
  | .inn u, .out v =>
      (u = v ∧ u ∉ L.usedVertices) ∨ L.ForwardPathDart v u
  | .out u, .inn v =>
      (u = v ∧ u ∈ L.usedVertices) ∨
        (G.Adj u v ∧ u ∉ Y ∧ v ∉ X)
  | _, _ => False

theorem SplitResidualStep.not_self
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n}
    (s : VertexSplitState V) :
    Not (L.SplitResidualStep s s) := by
  cases s <;> simp [SplitResidualStep]

theorem SplitResidualStep.forget_eq_or_adj
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n}
    {a b : VertexSplitState V}
    (h : L.SplitResidualStep a b) :
    a.vertex = b.vertex ∨ G.Adj a.vertex b.vertex := by
  cases a with
  | inn u =>
      cases b with
      | inn v => simp [SplitResidualStep] at h
      | out v =>
          simp [SplitResidualStep] at h
          rcases h with hcap | hd
          · exact Or.inl hcap.1
          · exact Or.inr hd.adj.symm
  | out u =>
      cases b with
      | inn v =>
          simp [SplitResidualStep] at h
          rcases h with hcap | hedge
          · exact Or.inl hcap.1
          · exact Or.inr hedge.1
      | out v => simp [SplitResidualStep] at h

def SplitResidualReachableFromUnusedSource
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (s : VertexSplitState V) : Prop :=
  Exists fun x : V =>
    x ∈ X ∧ x ∉ L.usedVertices ∧
      Relation.ReflTransGen L.SplitResidualStep
        (VertexSplitState.inn x) s

def SplitResidualReachesUnusedTarget
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) : Prop :=
  Exists fun y : V =>
    y ∈ Y ∧ y ∉ L.usedVertices ∧
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.out y)

theorem unused_source_reachable
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    {x : V} (hxX : x ∈ X) (hxUnused : x ∉ L.usedVertices) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.inn x) :=
  ⟨x, hxX, hxUnused, Relation.ReflTransGen.refl⟩

theorem SplitResidualReachableFromUnusedSource.step
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n}
    {a b : VertexSplitState V}
    (ha : L.SplitResidualReachableFromUnusedSource a)
    (hab : L.SplitResidualStep a b) :
    L.SplitResidualReachableFromUnusedSource b := by
  rcases ha with ⟨x, hxX, hxUnused, hreach⟩
  exact
    ⟨x, hxX, hxUnused,
      hreach.trans (Relation.ReflTransGen.single hab)⟩

theorem SplitResidualReachableFromUnusedSource.in_of_out_used
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n} {v : V}
    (hv : v ∈ L.usedVertices)
    (hout :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.out v)) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.inn v) :=
  hout.step (by
    exact Or.inl ⟨rfl, hv⟩)

theorem SplitResidualReachableFromUnusedSource.out_of_in_forwardPathDart
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n} {u v : V}
    (hdart : L.ForwardPathDart u v)
    (hin :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.inn v)) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.out u) :=
  hin.step (by
    exact Or.inr hdart)

theorem Walk.start_splitOutReachable_of_end_splitOutReachable_of_darts_subset
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (k : Fin n)
    {a b : V} (q : G.Walk a b)
    (hsub : q.darts ⊆ (L.path k).darts)
    (hb :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.out b)) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.out a) := by
  induction q with
  | nil =>
      exact hb
  | @cons u v w huv q ih =>
      have hsub_tail : q.darts ⊆ (L.path k).darts := by
        intro d hd
        exact hsub (by
          simp [SimpleGraph.Walk.darts_cons, hd])
      have hv_out := ih hsub_tail hb
      have hforward : L.ForwardPathDart u v := by
        refine ⟨k, huv, hsub ?_⟩
        simp [SimpleGraph.Walk.darts_cons]
      exact
        SplitResidualReachableFromUnusedSource.out_of_in_forwardPathDart
          hforward
          (SplitResidualReachableFromUnusedSource.in_of_out_used
            hforward.snd_mem_usedVertices hv_out)

theorem Walk.start_splitOutReachable_of_end_splitInReachable_of_darts_subset
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (k : Fin n)
    {a b : V} (q : G.Walk a b)
    (hnil : Not q.Nil)
    (hsub : q.darts ⊆ (L.path k).darts)
    (hb :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.inn b)) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.out a) := by
  induction q with
  | nil =>
      exact False.elim (hnil SimpleGraph.Walk.nil_nil)
  | @cons u v w huv q ih =>
      have hforward : L.ForwardPathDart u v := by
        refine ⟨k, huv, hsub ?_⟩
        simp [SimpleGraph.Walk.darts_cons]
      have hv_in :
          L.SplitResidualReachableFromUnusedSource
            (VertexSplitState.inn v) := by
        by_cases hqnil : q.Nil
        · have hvw : v = w := hqnil.eq
          simpa [hvw] using hb
        · have hsub_tail : q.darts ⊆ (L.path k).darts := by
            intro d hd
            exact hsub (by
              simp [SimpleGraph.Walk.darts_cons, hd])
          have hv_out := ih hqnil hsub_tail hb
          exact
            SplitResidualReachableFromUnusedSource.in_of_out_used
              hforward.snd_mem_usedVertices hv_out
      exact
        SplitResidualReachableFromUnusedSource.out_of_in_forwardPathDart
          hforward hv_in

theorem path_getVert_splitOutReachable_of_later_splitInReachable
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (k : Fin n)
    {m r : Nat}
    (hmr : m < r)
    (hr : r <= (L.path k).length)
    (hin :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.inn ((L.path k).getVert r))) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.out ((L.path k).getVert m)) := by
  classical
  let p := L.path k
  let q : G.Walk (p.getVert m) (p.getVert r) :=
    ((p.drop m).take (r - m)).copy rfl (by
      rw [SimpleGraph.Walk.drop_getVert]
      congr 1
      omega)
  have hq_len : q.length = r - m := by
    have hle : r - m <= p.length - m := by
      dsimp [p]
      omega
    simp [q, p, hle]
  have hq_not_nil : Not q.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    rw [hq_len]
    omega
  have hsub : q.darts ⊆ (L.path k).darts := by
    intro d hd
    have hd_take :
        d ∈ ((p.drop m).take (r - m)).darts := by
      simpa [q] using hd
    rw [SimpleGraph.Walk.darts_take] at hd_take
    have hd_drop : d ∈ (p.drop m).darts :=
      List.take_subset (r - m) (p.drop m).darts hd_take
    rw [SimpleGraph.Walk.darts_drop] at hd_drop
    exact List.drop_subset m p.darts hd_drop
  exact
    PartialSetLinkage.Walk.start_splitOutReachable_of_end_splitInReachable_of_darts_subset
      L k q hq_not_nil (by simpa [p] using hsub) (by
        simpa [q, p] using hin)


end PartialSetLinkage

end Schematic.Math.GraphTheory
