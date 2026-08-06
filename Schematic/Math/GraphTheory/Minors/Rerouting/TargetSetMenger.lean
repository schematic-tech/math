import Schematic.Math.GraphTheory.Minors.Rerouting.FiniteTargetMenger

/-! Finite Menger linkages from a triple to a target set. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/--
Set-target finite Menger via the three-sink auxiliary graph.

This is the constructive half of GM IX `(2.2)` needed by the source-aligned
society proof.  The hypothesis rules out every deletion of fewer than three
vertices separating the ordered source triple from the whole target set `Y`;
the conclusion is a genuine three-linkage to three artificial sinks.  The
subsequent extraction step removes the final sink edges and recovers three
disjoint paths ending at vertices of `Y`.
-/
theorem finite_menger_three_vertex_linkage_to_targetSetSinkGraph_of_not_separates_from_set
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {left : Fin 3 -> V} {Y : Set V}
    (hleft : Function.Injective left)
    (hnosep :
      forall S : Set V, S.ncard < 3 ->
        Not (SeparatesVertexTripleFromSetByDeletion G S left Y)) :
    HasThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)) := by
  classical
  exact
    finite_menger_three_vertex_linkage_of_not_separates
      (G := targetSetSinkGraph G Y)
      (left := fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (right := fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3))
      (targetSetSink_left_injective hleft)
      targetSetSink_sink_injective
      (by
        intro S hS
        exact
          targetSetSinkGraph_not_separates_of_not_separates_from_set
            (G := G) (left := left) (Y := Y) hnosep hS)

theorem ThreeVertexLinkage.targetSetSink_path_not_nil
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    (i : Fin 3) :
    Not (L.path i).Nil :=
  SimpleGraph.Walk.not_nil_of_ne (p := L.path i) (by
    intro h
    cases h)

theorem ThreeVertexLinkage.targetSetSink_dropLast_support_subset_original
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    (i : Fin 3) :
    forall z : V ⊕ Fin 3,
      z ∈ (L.path i).dropLast.support ->
        z ∈ Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)) := by
  intro z hz
  cases z with
  | inl v =>
      exact ⟨v, rfl⟩
  | inr j =>
      have hz_drop :
          (Sum.inr j : V ⊕ Fin 3) ∈ (L.path i).support.dropLast := by
        simpa [SimpleGraph.Walk.support_dropLast
          (L.targetSetSink_path_not_nil i)] using hz
      have hz_path :
          (Sum.inr j : V ⊕ Fin 3) ∈ (L.path i).support :=
        List.mem_of_mem_dropLast hz_drop
      let m : Fin 3 := L.targetEquiv.symm j
      have hm : L.targetEquiv m = j := by
        simp [m]
      by_cases him : i = m
      · have hi_target : L.targetEquiv i = j := by
          simpa [him] using hm
        have hend_not :
            (Sum.inr (L.targetEquiv i) : V ⊕ Fin 3) ∉
              (L.path i).dropLast.support :=
          Walk.IsPath.end_notMem_walk_dropLast_support
            (L.isPath i) (L.targetSetSink_path_not_nil i)
        exact False.elim (hend_not (by simpa [hi_target] using hz))
      · have hm_end :
            (Sum.inr j : V ⊕ Fin 3) ∈ (L.path m).support := by
          simpa [hm] using (L.path m).end_mem_support
        exact False.elim
          (Set.disjoint_left.mp (L.pairwise_vertex_disjoint i m him)
            hz_path hm_end)

noncomputable def ThreeVertexLinkage.targetSetRight
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    (i : Fin 3) : V :=
  targetSetSinkOriginalVertex
    (⟨(L.path i).penultimate,
      L.targetSetSink_dropLast_support_subset_original i
        (L.path i).penultimate
        (by
          simpa [SimpleGraph.Walk.support_dropLast
            (L.targetSetSink_path_not_nil i)] using
            (SimpleGraph.Walk.penultimate_mem_dropLast_support
              (L.targetSetSink_path_not_nil i)))⟩ :
      Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)))

theorem ThreeVertexLinkage.targetSetRight_mem
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    (i : Fin 3) :
    L.targetSetRight i ∈ Y := by
  classical
  let hnil : Not (L.path i).Nil := L.targetSetSink_path_not_nil i
  let hpen :
      (L.path i).penultimate ∈
        Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)) :=
    L.targetSetSink_dropLast_support_subset_original i
      (L.path i).penultimate
      (by
        simpa [SimpleGraph.Walk.support_dropLast hnil] using
          (SimpleGraph.Walk.penultimate_mem_dropLast_support hnil))
  let z :
      Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)) :=
    ⟨(L.path i).penultimate, hpen⟩
  have hspec : Sum.inl (targetSetSinkOriginalVertex z) =
      (L.path i).penultimate :=
    targetSetSinkOriginalVertex_spec z
  have hadj :
      (targetSetSinkGraph G Y).Adj
        (L.path i).penultimate
        (Sum.inr (L.targetEquiv i) : V ⊕ Fin 3) :=
    (L.path i).adj_penultimate hnil
  rw [← hspec] at hadj
  change targetSetSinkOriginalVertex z ∈ Y
  simpa [targetSetSinkGraph] using hadj

/-- The path extracted from one artificial target-set sink, packaged together
with the invariants needed by the linkage constructor.  Keeping the dependent
endpoint copies, path proof, and support reflection in one object avoids
reconstructing the same induced walk in every projection theorem. -/
noncomputable def ThreeVertexLinkage.targetSetPathData
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    (i : Fin 3) :
    {q : G.Walk (left i) (L.targetSetRight i) //
      q.IsPath ∧
        ∀ z : V, z ∈ q.support ->
          (Sum.inl z : V ⊕ Fin 3) ∈ (L.path i).support} := by
  classical
  let hsupport :
      forall z : V ⊕ Fin 3, z ∈ (L.path i).dropLast.support ->
        z ∈ Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)) :=
    L.targetSetSink_dropLast_support_subset_original i
  let qInd :
      ((targetSetSinkGraph G Y).induce
        (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)))).Walk
        ⟨Sum.inl (left i), hsupport (Sum.inl (left i))
          (L.path i).dropLast.start_mem_support⟩
        ⟨(L.path i).penultimate, hsupport (L.path i).penultimate
          (L.path i).dropLast.end_mem_support⟩ :=
    (L.path i).dropLast.induce
      (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))) hsupport
  let q : G.Walk
      (targetSetSinkOriginalVertex
        (⟨Sum.inl (left i), hsupport (Sum.inl (left i))
          (L.path i).dropLast.start_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))))
      (targetSetSinkOriginalVertex
        (⟨(L.path i).penultimate, hsupport (L.path i).penultimate
          (L.path i).dropLast.end_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)))) :=
    qInd.map (targetSetSinkOriginalRangeHom G Y)
  have hdrop_path : (L.path i).dropLast.IsPath := by
    simpa [SimpleGraph.Walk.dropLast] using
      (L.isPath i).take ((L.path i).length - 1)
  have hqInd_path : qInd.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map
      (f := (SimpleGraph.Embedding.induce
        (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)))).toHom)
    simpa [qInd] using hdrop_path
  have hq_path : q.IsPath := by
    simpa [q] using
      (SimpleGraph.Walk.map_isPath_of_injective
        (f := targetSetSinkOriginalRangeHom G Y)
        (targetSetSinkOriginalRangeHom_injective G Y) hqInd_path)
  let hstart :
      targetSetSinkOriginalVertex
        (⟨Sum.inl (left i), hsupport (Sum.inl (left i))
          (L.path i).dropLast.start_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))) =
        left i := by
    simp
  let hend :
      targetSetSinkOriginalVertex
        (⟨(L.path i).penultimate, hsupport (L.path i).penultimate
          (L.path i).dropLast.end_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))) =
        L.targetSetRight i := by
    dsimp [ThreeVertexLinkage.targetSetRight]
  let r : G.Walk (left i) (L.targetSetRight i) := q.copy hstart hend
  have hr_path : r.IsPath := by
    simpa [r] using (SimpleGraph.Walk.isPath_copy q hstart hend).mpr hq_path
  have hr_support :
      ∀ z : V, z ∈ r.support ->
        (Sum.inl z : V ⊕ Fin 3) ∈ (L.path i).support := by
    intro z hz
    have hz_q : z ∈ q.support := by
      simpa [r, SimpleGraph.Walk.support_copy] using hz
    change z ∈ (qInd.map (targetSetSinkOriginalRangeHom G Y)).support at hz_q
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz_q
    rcases hz_q with ⟨a, ha_qInd, ha_eq⟩
    have ha_drop :
        (a : V ⊕ Fin 3) ∈ (L.path i).dropLast.support := by
      have ha_map :
          (a : V ⊕ Fin 3) ∈
            (qInd.map (SimpleGraph.Embedding.induce
              (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)))).toHom).support := by
        rw [SimpleGraph.Walk.support_map]
        change (a : V ⊕ Fin 3) ∈
          qInd.support.map
            (fun x :
              Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3)) =>
                (x : V ⊕ Fin 3))
        exact List.mem_map.mpr ⟨a, ha_qInd, rfl⟩
      simpa [qInd] using ha_map
    have ha_val : (a : V ⊕ Fin 3) = Sum.inl z := by
      change targetSetSinkOriginalVertex a = z at ha_eq
      have hspec := targetSetSinkOriginalVertex_spec a
      calc
        (a : V ⊕ Fin 3) = Sum.inl (targetSetSinkOriginalVertex a) := hspec.symm
        _ = Sum.inl z := by rw [ha_eq]
    have hz_drop :
        (Sum.inl z : V ⊕ Fin 3) ∈ (L.path i).support.dropLast := by
      simpa [ha_val, SimpleGraph.Walk.support_dropLast
        (L.targetSetSink_path_not_nil i)] using ha_drop
    exact List.mem_of_mem_dropLast hz_drop
  exact ⟨r, hr_path, hr_support⟩

noncomputable def ThreeVertexLinkage.targetSetPath
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    (i : Fin 3) :
    G.Walk (left i) (L.targetSetRight i) :=
  (L.targetSetPathData i).1

theorem ThreeVertexLinkage.targetSetPath_isPath
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    (i : Fin 3) :
    (L.targetSetPath i).IsPath := by
  simpa [ThreeVertexLinkage.targetSetPath] using
    (L.targetSetPathData i).2.1

theorem ThreeVertexLinkage.targetSetPath_support_lift
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    {i : Fin 3} {z : V}
    (hz : z ∈ (L.targetSetPath i).support) :
    (Sum.inl z : V ⊕ Fin 3) ∈ (L.path i).support := by
  exact (L.targetSetPathData i).2.2 z (by
    simpa [ThreeVertexLinkage.targetSetPath] using hz)

theorem ThreeVertexLinkage.targetSetPath_pairwise_vertex_disjoint
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)))
    (i j : Fin 3) (hij : i ≠ j) :
    Disjoint
      {v : V | v ∈ (L.targetSetPath i).support}
      {v : V | v ∈ (L.targetSetPath j).support} := by
  rw [Set.disjoint_left]
  intro z hz_i hz_j
  exact
    Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij)
      (L.targetSetPath_support_lift hz_i)
      (L.targetSetPath_support_lift hz_j)

noncomputable def ThreeVertexLinkage.extractTargetSet
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3))) :
    ThreeVertexLinkage G left (fun i : Fin 3 => L.targetSetRight i) where
  targetEquiv := Equiv.refl (Fin 3)
  path i := L.targetSetPath i
  isPath i := L.targetSetPath_isPath i
  pairwise_vertex_disjoint i j hij :=
    L.targetSetPath_pairwise_vertex_disjoint i j hij

def HasThreeVertexLinkageToSet
    {V : Type u} (G : SimpleGraph V) (left : Fin 3 -> V) (Y : Set V) :
    Prop :=
  Exists fun right : Fin 3 -> V =>
    (forall i : Fin 3, right i ∈ Y) ∧
      HasThreeVertexLinkage G left right

theorem ThreeVertexLinkage.extract_target_set
    {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {left : Fin 3 -> V}
    (L : ThreeVertexLinkage
      (targetSetSinkGraph G Y)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
      (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3))) :
    HasThreeVertexLinkageToSet G left Y := by
  exact
    ⟨fun i : Fin 3 => L.targetSetRight i,
      (fun i => L.targetSetRight_mem i),
      ⟨L.extractTargetSet⟩⟩

theorem finite_menger_three_vertex_linkage_to_set_of_not_separates_from_set
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {left : Fin 3 -> V} {Y : Set V}
    (hleft : Function.Injective left)
    (hnosep :
      forall S : Set V, S.ncard < 3 ->
        Not (SeparatesVertexTripleFromSetByDeletion G S left Y)) :
    HasThreeVertexLinkageToSet G left Y := by
  classical
  rcases
    finite_menger_three_vertex_linkage_to_targetSetSinkGraph_of_not_separates_from_set
      (G := G) (left := left) (Y := Y) hleft hnosep with
    ⟨L⟩
  exact L.extract_target_set

/--
Finite vertex-Menger in the exact three-terminal form needed in the paper:
in a finite 3-connected graph, any two injective triples can be linked by
three pairwise vertex-disjoint paths, with the right-hand triple permuted.

This is invoked in `2605.10112_tex/main.tex` when the non-adjacent twin of `v`
is introduced.  The 3-connectivity hypothesis supplies the no-small-separator
side of finite Menger.
-/
theorem IsThreeConnected.hasThreeVertexLinkage_fin3_triples
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    (hright : Function.Injective right) :
    HasThreeVertexLinkage G left right := by
  classical
  exact
    finite_menger_three_vertex_linkage_of_not_separates
      (G := G) hleft hright (by
        intro S hS
        exact hG.not_separates_fin3_triples_by_small_deletion
          hleft hright hS)

/--
Set-target form of the finite three-terminal Menger theorem.

This is the exact background shape used in GM IX `(2.2)`: if the target side is
only specified as a set of at least three possible endpoints, choose three
distinct vertices in that set and link the ordered left triple to them.  The
result keeps the chosen target triple explicit so downstream society arguments
can prove the targets are allowed for their local induced subgraph.
-/
theorem IsThreeConnected.exists_hasThreeVertexLinkage_to_set
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    {left : Fin 3 -> V}
    (hleft : Function.Injective left)
    {Y : Set V} (hY : 3 <= Y.ncard) :
    Exists fun right : Fin 3 -> V =>
      Function.Injective right ∧
        (forall i : Fin 3, right i ∈ Y) ∧
          HasThreeVertexLinkage G left right := by
  classical
  rcases exists_injective_fin3_mem_of_ncard_ge_three (V := V) hY with
    ⟨right, hright_inj, hright_mem⟩
  exact
    ⟨right, hright_inj, hright_mem,
      hG.hasThreeVertexLinkage_fin3_triples hleft hright_inj⟩

theorem Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
    {y z : V}
    {p : G.Walk y z}
    (hp : p.IsPath)
    (hnil : Not p.Nil) :
    let H : G.Subgraph := p.dropLast.toSubgraph
    H.coe.Connected ∧ y ∈ H.verts ∧ z ∉ H.verts ∧
      Exists fun w : V => w ∈ H.verts ∧ G.Adj w z := by
  intro H
  refine ⟨p.dropLast.toSubgraph_connected.coe, ?_, ?_, ?_⟩
  · simp [H]
  · intro hz
    have hz_support : z ∈ p.dropLast.support := by
      rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hz
    exact Walk.IsPath.end_notMem_walk_dropLast_support hp hnil hz_support
  · exact ⟨p.penultimate, by simp [H], p.adj_penultimate hnil⟩

theorem Walk.IsPath.collapse_dropLast_adj_end
    {y z : V}
    {p : G.Walk y z}
    (hp : p.IsPath)
    (hnil : Not p.Nil) :
    let H : G.Subgraph := p.dropLast.toSubgraph
    let hH_connected : H.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor hp hnil).1
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G H hH_connected
    C.graph.Adj (C.map y) (C.map z) := by
  intro H hH_connected C
  have hpack := Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor hp hnil
  exact GraphContraction.collapseSubgraph_adj_of_mem_of_adjacent
    G H hH_connected hpack.2.1 hpack.2.2.1 hpack.2.2.2


end Schematic.Math.GraphTheory
