import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualRouting.AugmentedArcs

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
structure PartialThreeVertexLinkage.SplitAugmentedSourceData
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (l : List (VertexSplitState V)) (jNew : Fin 3)
    (source : V) where
  source_no_in :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l a (VertexSplitState.inn source))
  terminal : VertexSplitState V
  terminal_no_out :
    Not (Exists fun u : VertexSplitState V => L.SplitAugmentedArc l terminal u)
  terminal_incoming :
    Exists fun a : VertexSplitState V => L.SplitAugmentedArc l a terminal
  terminal_classified :
    terminal = VertexSplitState.out (right jNew) ∨
      Exists fun k : Fin n =>
        terminal = VertexSplitState.out (right (L.rightIndex k))
  chain : List (VertexSplitState V)
  chain_ne : chain ≠ []
  chain_head : chain.head? = some (VertexSplitState.inn source)
  chain_last : chain.getLast? = some terminal
  chain_aug : chain.IsChain (L.SplitAugmentedArc l)
  path : G.Walk source terminal.vertex
  path_isPath : path.IsPath
  path_support :
    forall x : V, x ∈ path.support ->
      Exists fun s : VertexSplitState V => s ∈ chain ∧ s.vertex = x

noncomputable def PartialThreeVertexLinkage.SplitAugmentedSourceData.fromOldLeft
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    (k : Fin n) :
    L.SplitAugmentedSourceData l jNew (left (L.leftIndex k)) := by
  classical
  let H :=
    PartialThreeVertexLinkage.SplitAugmentedArc.exists_classified_terminal_chain_path_from_old_left
      (L := L) hnodup hlast hchain k
  let terminal : VertexSplitState V := Classical.choose H
  let Hterminal := Classical.choose_spec H
  let Hm := Hterminal.2.2.2
  let m : List (VertexSplitState V) := Classical.choose Hm
  let Hm_spec := Classical.choose_spec Hm
  let Hp := Hm_spec.2.2.2.2
  let p : G.Walk (left (L.leftIndex k)) terminal.vertex := Classical.choose Hp
  let Hp_spec := Classical.choose_spec Hp
  exact {
    source_no_in :=
      PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_left_of_residual_chain
        (L := L) (l := l) k hlast hchain
    terminal := terminal
    terminal_no_out := Hterminal.1
    terminal_incoming := Hterminal.2.1
    terminal_classified := Hterminal.2.2.1
    chain := m
    chain_ne := Hm_spec.1
    chain_head := Hm_spec.2.1
    chain_last := Hm_spec.2.2.1
    chain_aug := Hm_spec.2.2.2.1
    path := p
    path_isPath := Hp_spec.1
    path_support := Hp_spec.2
  }

noncomputable def PartialThreeVertexLinkage.SplitAugmentedSourceData.fromNewLeft
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {iNew jNew : Fin 3}
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    L.SplitAugmentedSourceData l jNew (left iNew) := by
  classical
  let H :=
    PartialThreeVertexLinkage.SplitAugmentedArc.exists_classified_terminal_chain_path_from_new_left
      (L := L) hnodup hhead hlast hchain
  let terminal : VertexSplitState V := Classical.choose H
  let Hterminal := Classical.choose_spec H
  let Hm := Hterminal.2.2.2
  let m : List (VertexSplitState V) := Classical.choose Hm
  let Hm_spec := Classical.choose_spec Hm
  let Hp := Hm_spec.2.2.2.2
  let p : G.Walk (left iNew) terminal.vertex := Classical.choose Hp
  let Hp_spec := Classical.choose_spec Hp
  exact {
    source_no_in :=
      PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_head_inn
        (L := L) (l := l) hnodup hhead hlast hchain
    terminal := terminal
    terminal_no_out := Hterminal.1
    terminal_incoming := Hterminal.2.1
    terminal_classified := Hterminal.2.2.1
    chain := m
    chain_ne := Hm_spec.1
    chain_head := Hm_spec.2.1
    chain_last := Hm_spec.2.2.1
    chain_aug := Hm_spec.2.2.2.1
    path := p
    path_isPath := Hp_spec.1
    path_support := Hp_spec.2
  }

theorem PartialThreeVertexLinkage.SplitAugmentedSourceData.exists_rightIndex
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3} {source : V}
    (D : L.SplitAugmentedSourceData l jNew source) :
    Exists fun j : Fin 3 => D.terminal = VertexSplitState.out (right j) := by
  rcases D.terminal_classified with hnew | hold
  · exact ⟨jNew, hnew⟩
  · rcases hold with ⟨k, hk⟩
    exact ⟨L.rightIndex k, hk⟩

theorem PartialThreeVertexLinkage.SplitAugmentedSourceData.source_eq_of_terminal_eq
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3} {source₁ source₂ : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    (D₁ : L.SplitAugmentedSourceData l jNew source₁)
    (D₂ : L.SplitAugmentedSourceData l jNew source₂)
    (hterminal : D₁.terminal = D₂.terminal) :
    VertexSplitState.inn source₁ = VertexSplitState.inn source₂ := by
  exact
    relation_sources_eq_of_same_terminal_chains_of_left_unique
      (r := L.SplitAugmentedArc l)
      (fun {_a _b _c} hac hbc =>
        PartialThreeVertexLinkage.SplitAugmentedArc.right_unique
          (L := L) (l := l) hnodup hlast hchain hac hbc)
      D₁.source_no_in D₂.source_no_in
      D₁.chain_ne D₁.chain_head D₁.chain_last D₁.chain_aug
      D₂.chain_ne D₂.chain_head (by simpa [hterminal] using D₂.chain_last)
      D₂.chain_aug

theorem PartialThreeVertexLinkage.SplitAugmentedSourceData.paths_disjoint
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3} {source₁ source₂ : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    (D₁ : L.SplitAugmentedSourceData l jNew source₁)
    (D₂ : L.SplitAugmentedSourceData l jNew source₂)
    (hsource_ne : VertexSplitState.inn source₁ ≠ VertexSplitState.inn source₂) :
    Disjoint {x : V | x ∈ D₁.path.support}
      {x : V | x ∈ D₂.path.support} := by
  classical
  exact
    PartialThreeVertexLinkage.SplitAugmentedArc.paths_disjoint_of_sources_ne
      (L := L) (l := l) (m₁ := D₁.chain) (m₂ := D₂.chain)
      (source₁ := source₁) (source₂ := source₂)
      (sinkResidual := right jNew)
      hnodup hlast hchain D₁.source_no_in D₂.source_no_in hsource_ne
      D₁.chain_head D₁.chain_aug D₂.chain_head D₂.chain_aug
      D₁.path_support D₂.path_support

theorem PartialThreeVertexLinkage.hasPartial_succ_of_splitResidualChain_augmented
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hleft : Function.Injective left)
    {iNew jNew : Fin 3} {l : List (VertexSplitState V)}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    HasPartialThreeVertexLinkage G left right (n + 1) := by
  classical
  let sourceIndex : Fin (n + 1) -> Fin 3 := Fin.snoc L.leftIndex iNew
  have hsourceIndex_inj : Function.Injective sourceIndex := by
    simpa [sourceIndex] using
      (Fin.snoc_injective_iff.mpr ⟨L.leftIndex_injective, hiNew⟩)
  let oldData : forall k : Fin n,
      L.SplitAugmentedSourceData l jNew (left (L.leftIndex k)) := fun k =>
    PartialThreeVertexLinkage.SplitAugmentedSourceData.fromOldLeft
      (L := L) (l := l) (jNew := jNew) hnodup hlast hchain k
  let newData : L.SplitAugmentedSourceData l jNew (left iNew) :=
    PartialThreeVertexLinkage.SplitAugmentedSourceData.fromNewLeft
      (L := L) (l := l) (iNew := iNew) (jNew := jNew)
      hnodup hhead hlast hchain
  let data :
      forall a : Fin (n + 1),
        L.SplitAugmentedSourceData l jNew (left (sourceIndex a)) := by
    intro a
    cases a using Fin.lastCases with
    | last =>
        simpa [sourceIndex] using newData
    | cast k =>
        simpa [sourceIndex] using oldData k
  have hterminal_right :
      forall a : Fin (n + 1),
        Exists fun j : Fin 3 =>
          (data a).terminal = VertexSplitState.out (right j) := by
    intro a
    exact (data a).exists_rightIndex
  let rightIndexNew : Fin (n + 1) -> Fin 3 := fun a =>
    Classical.choose (hterminal_right a)
  have hterminal_right_spec :
      forall a : Fin (n + 1),
        (data a).terminal =
          VertexSplitState.out (right (rightIndexNew a)) := by
    intro a
    exact Classical.choose_spec (hterminal_right a)
  have hrightIndexNew_inj : Function.Injective rightIndexNew := by
    intro a b hab
    have hterminal_eq : (data a).terminal = (data b).terminal := by
      calc
        (data a).terminal =
            VertexSplitState.out (right (rightIndexNew a)) :=
          hterminal_right_spec a
        _ = VertexSplitState.out (right (rightIndexNew b)) := by
          simp [hab]
        _ = (data b).terminal := (hterminal_right_spec b).symm
    have hsource_eq :
        VertexSplitState.inn (left (sourceIndex a)) =
          VertexSplitState.inn (left (sourceIndex b)) :=
      PartialThreeVertexLinkage.SplitAugmentedSourceData.source_eq_of_terminal_eq
        (L := L) (l := l) (jNew := jNew)
        hnodup hlast hchain (data a) (data b) hterminal_eq
    injection hsource_eq with hleft_eq
    exact hsourceIndex_inj (hleft hleft_eq)
  exact ⟨{
    leftIndex := sourceIndex
    rightIndex := rightIndexNew
    leftIndex_injective := hsourceIndex_inj
    rightIndex_injective := hrightIndexNew_inj
    path := fun a =>
      ((data a).path).copy rfl (by
        have hvertex :=
          congrArg VertexSplitState.vertex (hterminal_right_spec a)
        simpa using hvertex)
    isPath := by
      intro a
      simpa using (data a).path_isPath
    pairwise_vertex_disjoint := by
      intro a b hab
      have hsource_ne :
          VertexSplitState.inn (left (sourceIndex a)) ≠
            VertexSplitState.inn (left (sourceIndex b)) := by
        intro hsource_eq
        injection hsource_eq with hleft_eq
        exact hab (hsourceIndex_inj (hleft hleft_eq))
      have hdisj :
          Disjoint {x : V | x ∈ (data a).path.support}
            {x : V | x ∈ (data b).path.support} :=
        PartialThreeVertexLinkage.SplitAugmentedSourceData.paths_disjoint
          (L := L) (l := l) (jNew := jNew)
          hnodup hlast hchain (data a) (data b) hsource_ne
      simpa using hdisj
  }⟩


end Schematic.Math.GraphTheory
