import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualCuts

/-! Transporting residual chains to indexed-terminal linkages. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace PartialSetLinkage

/--
View a partial set-linkage as the older indexed-terminal linkage after choosing
ambient triples containing its selected endpoints.
-/
def toPartialThreeVertexLinkage
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (left right : Fin 3 -> V)
    (leftIndex rightIndex : Fin n -> Fin 3)
    (hleftIndex : Function.Injective leftIndex)
    (hrightIndex : Function.Injective rightIndex)
    (hleft : forall i : Fin n, left (leftIndex i) = L.source i)
    (hright : forall i : Fin n, right (rightIndex i) = L.target i) :
    PartialThreeVertexLinkage G left right n where
  leftIndex := leftIndex
  rightIndex := rightIndex
  leftIndex_injective := hleftIndex
  rightIndex_injective := hrightIndex
  path i := (L.path i).copy (hleft i).symm (hright i).symm
  isPath i := by
    simpa using
      (SimpleGraph.Walk.isPath_copy
        (L.path i) (hleft i).symm (hright i).symm).mpr (L.isPath i)
  pairwise_vertex_disjoint := by
    intro i j hij
    simpa using L.pairwise_vertex_disjoint i j hij

theorem toPartialThreeVertexLinkage_usedVertices
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (left right : Fin 3 -> V)
    (leftIndex rightIndex : Fin n -> Fin 3)
    (hleftIndex : Function.Injective leftIndex)
    (hrightIndex : Function.Injective rightIndex)
    (hleft : forall i : Fin n, left (leftIndex i) = L.source i)
    (hright : forall i : Fin n, right (rightIndex i) = L.target i) :
    (L.toPartialThreeVertexLinkage left right leftIndex rightIndex
      hleftIndex hrightIndex hleft hright).usedVertices =
        L.usedVertices := by
  ext z
  simp [PartialThreeVertexLinkage.usedVertices, usedVertices,
    toPartialThreeVertexLinkage]

theorem forwardPathDart_toPartialThreeVertexLinkage
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (left right : Fin 3 -> V)
    (leftIndex rightIndex : Fin n -> Fin 3)
    (hleftIndex : Function.Injective leftIndex)
    (hrightIndex : Function.Injective rightIndex)
    (hleft : forall i : Fin n, left (leftIndex i) = L.source i)
    (hright : forall i : Fin n, right (rightIndex i) = L.target i)
    {u v : V}
    (h : L.ForwardPathDart u v) :
    (L.toPartialThreeVertexLinkage left right leftIndex rightIndex
      hleftIndex hrightIndex hleft hright).ForwardPathDart u v := by
  rcases h with ⟨i, huv, hd⟩
  exact ⟨i, huv, by simpa [toPartialThreeVertexLinkage] using hd⟩

theorem splitResidualStep_toPartialThreeVertexLinkage
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (left right : Fin 3 -> V)
    (leftIndex rightIndex : Fin n -> Fin 3)
    (hleftIndex : Function.Injective leftIndex)
    (hrightIndex : Function.Injective rightIndex)
    (hleft : forall i : Fin n, left (leftIndex i) = L.source i)
    (hright : forall i : Fin n, right (rightIndex i) = L.target i)
    {a b : VertexSplitState V}
    (h : L.SplitResidualStep a b) :
    (L.toPartialThreeVertexLinkage left right leftIndex rightIndex
      hleftIndex hrightIndex hleft hright).SplitResidualStep a b := by
  let L' :=
    L.toPartialThreeVertexLinkage left right leftIndex rightIndex
      hleftIndex hrightIndex hleft hright
  have hused : L'.usedVertices = L.usedVertices :=
    L.toPartialThreeVertexLinkage_usedVertices
      left right leftIndex rightIndex hleftIndex hrightIndex hleft hright
  cases a with
  | inn u =>
      cases b with
      | inn v => simp [SplitResidualStep] at h
      | out v =>
          simp [SplitResidualStep] at h
          rcases h with hcap | hd
          · exact Or.inl ⟨hcap.1, by
              change u ∉ L'.usedVertices
              rw [hused]
              exact hcap.2⟩
          · exact Or.inr
              (L.forwardPathDart_toPartialThreeVertexLinkage
                left right leftIndex rightIndex hleftIndex hrightIndex
                hleft hright hd)
  | out u =>
      cases b with
      | inn v =>
          simp [SplitResidualStep] at h
          rcases h with hcap | hedge
          · exact Or.inl ⟨hcap.1, by
              change u ∈ L'.usedVertices
              rw [hused]
              exact hcap.2⟩
          · exact Or.inr hedge.1
      | out v => simp [SplitResidualStep] at h

theorem isChain_toPartialThreeVertexLinkage
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (left right : Fin 3 -> V)
    (leftIndex rightIndex : Fin n -> Fin 3)
    (hleftIndex : Function.Injective leftIndex)
    (hrightIndex : Function.Injective rightIndex)
    (hleft : forall i : Fin n, left (leftIndex i) = L.source i)
    (hright : forall i : Fin n, right (rightIndex i) = L.target i)
    {l : List (VertexSplitState V)}
    (hchain : l.IsChain L.SplitResidualStep) :
    l.IsChain
      (L.toPartialThreeVertexLinkage left right leftIndex rightIndex
        hleftIndex hrightIndex hleft hright).SplitResidualStep := by
  exact
    hchain.imp (fun _ _ h =>
      L.splitResidualStep_toPartialThreeVertexLinkage
        left right leftIndex rightIndex hleftIndex hrightIndex
        hleft hright h)

theorem splitAugmentedArc_no_incoming_inn_of_unused_source
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (left right : Fin 3 -> V)
    (leftIndex rightIndex : Fin n -> Fin 3)
    (hleftIndex : Function.Injective leftIndex)
    (hrightIndex : Function.Injective rightIndex)
    (hleft : forall i : Fin n, left (leftIndex i) = L.source i)
    (hright : forall i : Fin n, right (rightIndex i) = L.target i)
    {l : List (VertexSplitState V)}
    (hchain : l.IsChain L.SplitResidualStep)
    {z : V}
    (hzX : z ∈ X)
    (hzUnused : z ∉ L.usedVertices) :
    forall a : VertexSplitState V,
      Not
        ((L.toPartialThreeVertexLinkage left right leftIndex rightIndex
          hleftIndex hrightIndex hleft hright).SplitAugmentedArc
            l a (VertexSplitState.inn z)) := by
  let L' :=
    L.toPartialThreeVertexLinkage left right leftIndex rightIndex
      hleftIndex hrightIndex hleft hright
  have hused : L'.usedVertices = L.usedVertices :=
    L.toPartialThreeVertexLinkage_usedVertices
      left right leftIndex rightIndex hleftIndex hrightIndex hleft hright
  intro a haug
  rcases haug with hcurrent | hresidual
  · cases a with
    | inn u =>
        simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcurrent
    | out u =>
        have hzUsed : z ∈ L'.usedVertices :=
          hcurrent.1.snd_mem_usedVertices
        exact hzUnused (by simpa [hused] using hzUsed)
  · have hstep :
        L.SplitResidualStep a (VertexSplitState.inn z) :=
      List.Consecutive.rel_of_isChain hchain hresidual.1
    cases a with
    | inn u =>
        simp [SplitResidualStep] at hstep
    | out u =>
        simp [SplitResidualStep] at hstep
        rcases hstep with hcapacity | hgraph
        · exact hzUnused (by simpa [hcapacity.1] using hcapacity.2)
        · exact hgraph.2.2 hzX

theorem splitAugmentedArc_no_outgoing_out_of_unused_target
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (left right : Fin 3 -> V)
    (leftIndex rightIndex : Fin n -> Fin 3)
    (hleftIndex : Function.Injective leftIndex)
    (hrightIndex : Function.Injective rightIndex)
    (hleft : forall i : Fin n, left (leftIndex i) = L.source i)
    (hright : forall i : Fin n, right (rightIndex i) = L.target i)
    {l : List (VertexSplitState V)}
    (hchain : l.IsChain L.SplitResidualStep)
    {z : V}
    (hzY : z ∈ Y)
    (hzUnused : z ∉ L.usedVertices) :
    forall b : VertexSplitState V,
      Not
        ((L.toPartialThreeVertexLinkage left right leftIndex rightIndex
          hleftIndex hrightIndex hleft hright).SplitAugmentedArc
            l (VertexSplitState.out z) b) := by
  let L' :=
    L.toPartialThreeVertexLinkage left right leftIndex rightIndex
      hleftIndex hrightIndex hleft hright
  have hused : L'.usedVertices = L.usedVertices :=
    L.toPartialThreeVertexLinkage_usedVertices
      left right leftIndex rightIndex hleftIndex hrightIndex hleft hright
  intro b haug
  rcases haug with hcurrent | hresidual
  · cases b with
    | inn v =>
        have hzUsed : z ∈ L'.usedVertices :=
          hcurrent.1.fst_mem_usedVertices
        exact hzUnused (by simpa [hused] using hzUsed)
    | out v =>
        simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcurrent
  · have hstep :
        L.SplitResidualStep (VertexSplitState.out z) b :=
      List.Consecutive.rel_of_isChain hchain hresidual.1
    cases b with
    | inn v =>
        simp [SplitResidualStep] at hstep
        rcases hstep with hcapacity | hgraph
        · exact hzUnused (by simpa [hcapacity.1] using hcapacity.2)
        · exact hgraph.2.1 hzY
    | out v =>
        simp [SplitResidualStep] at hstep

/--
Reachability from a member of a finite chain to its last member.  The
head-to-member version is used by the split-flow construction above; the
reverse form is what endpoint cleanliness at the target side needs.
-/
theorem reflTransGen_of_isChain_mem_getLast?
    {α : Type u} {r : α -> α -> Prop}
    {m : List α} {s terminal : α}
    (hlast : m.getLast? = some terminal)
    (hchain : m.IsChain r)
    (hs : s ∈ m) :
    Relation.ReflTransGen r s terminal := by
  have hheadReverse : m.reverse.head? = some terminal := by
    simpa using hlast
  have hsReverse : s ∈ m.reverse := by
    simpa using hs
  have hreverse :
      Relation.ReflTransGen (flip r) terminal s :=
    reflTransGen_of_isChain_head?_mem
      hheadReverse
      (by
        rw [List.isChain_reverse]
        simpa [flip] using hchain)
      hsReverse
  simpa [flip, Function.swap] using hreverse.swap

/-- A residual walk cannot leave a vertex with no outgoing arc. -/
theorem reflTransGen_eq_of_no_outgoing
    {α : Type u} {r : α -> α -> Prop} {a b : α}
    (hno_out : forall c : α, Not (r a c))
    (h : Relation.ReflTransGen r a b) :
    a = b := by
  rcases Relation.ReflTransGen.cases_head h with hab | ⟨c, hac, _⟩
  · exact hab
  · exact False.elim (hno_out c hac)


end PartialSetLinkage

end Schematic.Math.GraphTheory
