import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.LinkageTransport

/-! Triple and target-set separators and their auxiliary sink graphs. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/--
`S` separates the two triples by deletion if, after deleting `S`, no remaining
left endpoint can reach any remaining right endpoint.  This is the separator
side of the finite three-path Menger application used below.
-/
def SeparatesVertexTriplesByDeletion
    {V : Type u} (G : SimpleGraph V) (S : Set V)
    (left right : Fin 3 -> V) : Prop :=
  forall i j (hli : left i ∉ S) (hrj : right j ∉ S),
    Not ((G.induce Sᶜ).Reachable ⟨left i, hli⟩ ⟨right j, hrj⟩)

/--
`S` separates an ordered triple from a target set by deletion if, after
deleting `S`, no remaining left endpoint can reach any remaining vertex of the
target set.

This is the separator side of GM IX `(2.2)`: the target side in the source
argument is a set `Y` of allowable boundary vertices, not a preselected ordered
triple.  The fixed-triple separator above is recovered by taking
`Y = Set.range right`.
-/
def SeparatesVertexTripleFromSetByDeletion
    {V : Type u} (G : SimpleGraph V) (S : Set V)
    (left : Fin 3 -> V) (Y : Set V) : Prop :=
  forall i y (hli : left i ∉ S) (_hyY : y ∈ Y) (hyS : y ∉ S),
    Not ((G.induce Sᶜ).Reachable ⟨left i, hli⟩ ⟨y, hyS⟩)

theorem SeparatesVertexTripleFromSetByDeletion.to_triples
    {V : Type u} {G : SimpleGraph V} {S : Set V}
    {left right : Fin 3 -> V} {Y : Set V}
    (hsep : SeparatesVertexTripleFromSetByDeletion G S left Y)
    (hrightY : forall j : Fin 3, right j ∈ Y) :
    SeparatesVertexTriplesByDeletion G S left right := by
  intro i j hli hrj
  exact hsep i (right j) hli (hrightY j) hrj

theorem not_separatesVertexTripleFromSetByDeletion_of_reachable
    {V : Type u} {G : SimpleGraph V} {S : Set V}
    {left : Fin 3 -> V} {Y : Set V}
    {i : Fin 3} {y : V}
    (hli : left i ∉ S) (hyY : y ∈ Y) (hyS : y ∉ S)
    (hreach :
      (G.induce Sᶜ).Reachable ⟨left i, hli⟩ ⟨y, hyS⟩) :
    Not (SeparatesVertexTripleFromSetByDeletion G S left Y) := by
  intro hsep
  exact hsep i y hli hyY hyS hreach

theorem SeparatesVertexTripleFromSetByDeletion.mono_target
    {V : Type u} {G : SimpleGraph V} {S : Set V}
    {left : Fin 3 -> V} {Y Z : Set V}
    (hsep : SeparatesVertexTripleFromSetByDeletion G S left Z)
    (hYZ : Y ⊆ Z) :
    SeparatesVertexTripleFromSetByDeletion G S left Y := by
  intro i y hli hyY hyS
  exact hsep i y hli (hYZ hyY) hyS

/--
Auxiliary graph for the set-target form of GM IX `(2.2)`: add three new sink
vertices, each adjacent to every vertex of the target set `Y`.

A three-linkage from `Sum.inl ∘ left` to the three sinks encodes three
vertex-disjoint paths from the ordered source triple to three (not
preselected) vertices of `Y`, after deleting the terminal sink vertices.
-/
def targetSetSinkGraph
    {V : Type u} (G : SimpleGraph V) (Y : Set V) :
    SimpleGraph (V ⊕ Fin 3) where
  Adj a b :=
    match a, b with
    | Sum.inl x, Sum.inl y => G.Adj x y
    | Sum.inl x, Sum.inr _ => x ∈ Y
    | Sum.inr _, Sum.inl y => y ∈ Y
    | Sum.inr _, Sum.inr _ => False
  symm := by
    intro a b h
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            exact h.symm
        | inr j =>
            exact h
    | inr i =>
        cases b with
        | inl y =>
            exact h
        | inr j =>
            exact h
  loopless := by
    constructor
    intro a h
    cases a with
    | inl x =>
        exact G.loopless.irrefl x h
    | inr i =>
        exact h

/-- The target-set sink graph with an arbitrary finite number of sinks.

The older `targetSetSinkGraph` fixes three interchangeable sinks, which is
appropriate for ordinary three-path Menger.  Endpoint-preserving augmentation
also needs one or two *locked* target vertices together with, respectively,
two or one interchangeable sinks.  Keeping the number of sinks explicit makes
those two auxiliary graphs instances of the same construction. -/
def finiteTargetSetSinkGraph
    {V : Type u} (G : SimpleGraph V) (Y : Set V) (n : Nat) :
    SimpleGraph (V ⊕ Fin n) where
  Adj a b :=
    match a, b with
    | Sum.inl x, Sum.inl y => G.Adj x y
    | Sum.inl x, Sum.inr _ => x ∈ Y
    | Sum.inr _, Sum.inl y => y ∈ Y
    | Sum.inr _, Sum.inr _ => False
  symm := by
    intro a b h
    cases a with
    | inl x =>
        cases b with
        | inl y => exact h.symm
        | inr j => exact h
    | inr i =>
        cases b with
        | inl y => exact h
        | inr j => exact h
  loopless := by
    constructor
    intro a h
    cases a with
    | inl x => exact G.loopless.irrefl x h
    | inr i => exact h

def finiteTargetSetSinkOriginalHom
    {V : Type u} (G : SimpleGraph V) (Y : Set V) (n : Nat) :
    G →g finiteTargetSetSinkGraph G Y n where
  toFun v := Sum.inl v
  map_rel' := by
    intro a b h
    simpa [finiteTargetSetSinkGraph] using h

noncomputable def finiteTargetSetSinkOriginalVertex
    {V : Type u} {n : Nat}
    (z : Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) : V :=
  Classical.choose z.2

theorem finiteTargetSetSinkOriginalVertex_spec
    {V : Type u} {n : Nat}
    (z : Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) :
    Sum.inl (finiteTargetSetSinkOriginalVertex z) = z.1 := by
  exact Classical.choose_spec z.2

@[simp] theorem finiteTargetSetSinkOriginalVertex_inl
    {V : Type u} {n : Nat} (v : V) :
    finiteTargetSetSinkOriginalVertex
      (⟨Sum.inl v, ⟨v, rfl⟩⟩ :
        Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) = v := by
  exact Sum.inl.inj
    (finiteTargetSetSinkOriginalVertex_spec
      (⟨Sum.inl v, ⟨v, rfl⟩⟩ :
        Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))))

noncomputable def finiteTargetSetSinkOriginalRangeHom
    {V : Type u} (G : SimpleGraph V) (Y : Set V) (n : Nat) :
    ((finiteTargetSetSinkGraph G Y n).induce
      (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n)))) →g G where
  toFun := finiteTargetSetSinkOriginalVertex
  map_rel' := by
    intro a b hab
    have ha :=
      finiteTargetSetSinkOriginalVertex_spec a
    have hb :=
      finiteTargetSetSinkOriginalVertex_spec b
    change
      (finiteTargetSetSinkGraph G Y n).Adj
        (a : V ⊕ Fin n) (b : V ⊕ Fin n) at hab
    rw [← ha, ← hb] at hab
    simpa [finiteTargetSetSinkGraph] using hab

theorem finiteTargetSetSinkOriginalRangeHom_injective
    {V : Type u} (G : SimpleGraph V) (Y : Set V) (n : Nat) :
    Function.Injective (finiteTargetSetSinkOriginalRangeHom G Y n) := by
  intro a b h
  apply Subtype.ext
  change
    finiteTargetSetSinkOriginalVertex a =
      finiteTargetSetSinkOriginalVertex b at h
  have ha := finiteTargetSetSinkOriginalVertex_spec a
  have hb := finiteTargetSetSinkOriginalVertex_spec b
  calc
    (a : V ⊕ Fin n) =
        Sum.inl (finiteTargetSetSinkOriginalVertex a) := ha.symm
    _ = Sum.inl (finiteTargetSetSinkOriginalVertex b) := by rw [h]
    _ = (b : V ⊕ Fin n) := hb

noncomputable def finiteTargetSetSinkOriginalWalk
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {x y : V}
    (p : (finiteTargetSetSinkGraph G Y n).Walk (Sum.inl x) (Sum.inl y))
    (hsupport :
      forall z : V ⊕ Fin n, z ∈ p.support ->
        z ∈ Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) :
    G.Walk x y := by
  let qInd :=
    p.induce
      (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) hsupport
  let q :=
    qInd.map (finiteTargetSetSinkOriginalRangeHom G Y n)
  let hstart :
      finiteTargetSetSinkOriginalVertex
        (⟨Sum.inl x, hsupport _ p.start_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) = x := by
    exact Sum.inl.inj
      (finiteTargetSetSinkOriginalVertex_spec
        (⟨Sum.inl x, hsupport _ p.start_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))))
  let hend :
      finiteTargetSetSinkOriginalVertex
        (⟨Sum.inl y, hsupport _ p.end_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) = y := by
    exact Sum.inl.inj
      (finiteTargetSetSinkOriginalVertex_spec
        (⟨Sum.inl y, hsupport _ p.end_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))))
  exact q.copy hstart hend

theorem finiteTargetSetSinkOriginalWalk_isPath
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {x y : V}
    {p : (finiteTargetSetSinkGraph G Y n).Walk (Sum.inl x) (Sum.inl y)}
    (hp : p.IsPath)
    (hsupport :
      forall z : V ⊕ Fin n, z ∈ p.support ->
        z ∈ Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) :
    (finiteTargetSetSinkOriginalWalk p hsupport).IsPath := by
  classical
  let qInd :=
    p.induce
      (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) hsupport
  have hqInd : qInd.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map
      (f := (SimpleGraph.Embedding.induce
        (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n)))).toHom)
    simpa [qInd] using hp
  have hq :
      (qInd.map (finiteTargetSetSinkOriginalRangeHom G Y n)).IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective
      (f := finiteTargetSetSinkOriginalRangeHom G Y n)
      (finiteTargetSetSinkOriginalRangeHom_injective G Y n) hqInd
  let q :=
    qInd.map (finiteTargetSetSinkOriginalRangeHom G Y n)
  let hstart :
      finiteTargetSetSinkOriginalVertex
        (⟨Sum.inl x, hsupport _ p.start_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) = x := by
    exact Sum.inl.inj
      (finiteTargetSetSinkOriginalVertex_spec
        (⟨Sum.inl x, hsupport _ p.start_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))))
  let hend :
      finiteTargetSetSinkOriginalVertex
        (⟨Sum.inl y, hsupport _ p.end_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) = y := by
    exact Sum.inl.inj
      (finiteTargetSetSinkOriginalVertex_spec
        (⟨Sum.inl y, hsupport _ p.end_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))))
  change (q.copy hstart hend).IsPath
  exact (SimpleGraph.Walk.isPath_copy q hstart hend).mpr (by
    simpa [q] using hq)

theorem finiteTargetSetSinkOriginalWalk_support_lift
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {x y : V}
    {p : (finiteTargetSetSinkGraph G Y n).Walk (Sum.inl x) (Sum.inl y)}
    (hsupport :
      forall z : V ⊕ Fin n, z ∈ p.support ->
        z ∈ Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n)))
    {z : V}
    (hz : z ∈ (finiteTargetSetSinkOriginalWalk p hsupport).support) :
    (Sum.inl z : V ⊕ Fin n) ∈ p.support := by
  classical
  let qInd :=
    p.induce
      (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) hsupport
  let q :=
    qInd.map (finiteTargetSetSinkOriginalRangeHom G Y n)
  let hstart :
      finiteTargetSetSinkOriginalVertex
        (⟨Sum.inl x, hsupport _ p.start_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) = x := by
    exact Sum.inl.inj
      (finiteTargetSetSinkOriginalVertex_spec
        (⟨Sum.inl x, hsupport _ p.start_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))))
  let hend :
      finiteTargetSetSinkOriginalVertex
        (⟨Sum.inl y, hsupport _ p.end_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))) = y := by
    exact Sum.inl.inj
      (finiteTargetSetSinkOriginalVertex_spec
        (⟨Sum.inl y, hsupport _ p.end_mem_support⟩ :
          Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n))))
  have hzq : z ∈ q.support := by
    simpa [finiteTargetSetSinkOriginalWalk, qInd, q, hstart, hend,
      SimpleGraph.Walk.support_copy] using hz
  rw [SimpleGraph.Walk.support_map] at hzq
  rcases List.mem_map.mp hzq with ⟨a, ha, haz⟩
  have ha_value : (a : V ⊕ Fin n) = Sum.inl z := by
    have hspec := finiteTargetSetSinkOriginalVertex_spec a
    change finiteTargetSetSinkOriginalVertex a = z at haz
    calc
      (a : V ⊕ Fin n) =
          Sum.inl (finiteTargetSetSinkOriginalVertex a) := hspec.symm
      _ = Sum.inl z := by rw [haz]
  have ha_map :
      (a : V ⊕ Fin n) ∈
        (qInd.map
          (SimpleGraph.Embedding.induce
            (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n)))).toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  simpa [qInd, ha_value] using ha_map

def finiteTargetSetSinkOriginalDeleted
    {V : Type u} {n : Nat} (D : Set (V ⊕ Fin n)) : Set V :=
  {v : V | Sum.inl v ∈ D}

@[simp] theorem finiteTargetSetSinkOriginalDeleted_mem
    {V : Type u} {n : Nat} (D : Set (V ⊕ Fin n)) (v : V) :
    v ∈ finiteTargetSetSinkOriginalDeleted D ↔ Sum.inl v ∈ D := by
  rfl

theorem finiteTargetSetSinkOriginalDeleted_ncard_le
    {V : Type u} [Fintype V] {n : Nat}
    (D : Set (V ⊕ Fin n)) :
    (finiteTargetSetSinkOriginalDeleted D).ncard <= D.ncard := by
  classical
  exact Set.ncard_le_ncard_of_injOn
    (s := finiteTargetSetSinkOriginalDeleted D)
    (t := D)
    (f := fun v : V => Sum.inl v)
    (by
      intro v hv
      exact hv)
    (by
      intro a _ha b _hb h
      exact Sum.inl.inj h)

theorem finiteTargetSetSinkOriginalDeleted_ncard_lt_three
    {V : Type u} [Fintype V] {n : Nat}
    {D : Set (V ⊕ Fin n)}
    (hD : D.ncard < 3) :
    (finiteTargetSetSinkOriginalDeleted D).ncard < 3 := by
  have hle :=
    finiteTargetSetSinkOriginalDeleted_ncard_le (V := V) D
  omega

theorem finiteTargetSetSinkGraph_reachable_original_after_delete
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {D : Set (V ⊕ Fin n)} {x y : V}
    (hxD : Sum.inl x ∉ D)
    (hyD : Sum.inl y ∉ D)
    (hreach :
      (G.induce (finiteTargetSetSinkOriginalDeleted D)ᶜ).Reachable
        ⟨x, by simpa [finiteTargetSetSinkOriginalDeleted] using hxD⟩
        ⟨y, by simpa [finiteTargetSetSinkOriginalDeleted] using hyD⟩) :
    ((finiteTargetSetSinkGraph G Y n).induce Dᶜ).Reachable
      ⟨Sum.inl x, hxD⟩ ⟨Sum.inl y, hyD⟩ := by
  classical
  obtain ⟨p, _hp, hp_support⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := (finiteTargetSetSinkOriginalDeleted D)ᶜ)
      (by simpa [finiteTargetSetSinkOriginalDeleted] using hxD)
      (by simpa [finiteTargetSetSinkOriginalDeleted] using hyD)
      hreach
  let q : (finiteTargetSetSinkGraph G Y n).Walk
      (Sum.inl x) (Sum.inl y) :=
    p.map (finiteTargetSetSinkOriginalHom G Y n)
  exact Walk.reachable_induce_of_support_subset q (by
    intro z hz
    change z ∉ D
    change z ∈
      (p.map (finiteTargetSetSinkOriginalHom G Y n)).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact hp_support w hw)

theorem finiteTargetSetSinkGraph_reachable_to_sink_after_delete
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {D : Set (V ⊕ Fin n)} {x y : V} {j : Fin n}
    (hxD : Sum.inl x ∉ D)
    (hyD : Sum.inl y ∉ D)
    (hjD : Sum.inr j ∉ D)
    (hyY : y ∈ Y)
    (hreach :
      (G.induce (finiteTargetSetSinkOriginalDeleted D)ᶜ).Reachable
        ⟨x, by simpa [finiteTargetSetSinkOriginalDeleted] using hxD⟩
        ⟨y, by simpa [finiteTargetSetSinkOriginalDeleted] using hyD⟩) :
    ((finiteTargetSetSinkGraph G Y n).induce Dᶜ).Reachable
      ⟨Sum.inl x, hxD⟩ ⟨Sum.inr j, hjD⟩ := by
  have hreach_original :=
    finiteTargetSetSinkGraph_reachable_original_after_delete
      (G := G) (Y := Y) (n := n) hxD hyD hreach
  have hlast :
      ((finiteTargetSetSinkGraph G Y n).induce Dᶜ).Adj
        ⟨Sum.inl y, hyD⟩ ⟨Sum.inr j, hjD⟩ := by
    simpa [finiteTargetSetSinkGraph] using hyY
  exact hreach_original.trans (SimpleGraph.Adj.reachable hlast)

def targetSetSinkOriginalHom
    {V : Type u} (G : SimpleGraph V) (Y : Set V) :
    G →g targetSetSinkGraph G Y where
  toFun v := Sum.inl v
  map_rel' := by
    intro a b h
    simpa [targetSetSinkGraph] using h

@[simp] theorem targetSetSinkGraph_original_adj_iff
    {V : Type u} (G : SimpleGraph V) (Y : Set V) (a b : V) :
    (targetSetSinkGraph G Y).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := by
  simp [targetSetSinkGraph]

@[simp] theorem targetSetSinkGraph_left_sink_adj_iff
    {V : Type u} (G : SimpleGraph V) (Y : Set V) (a : V) (j : Fin 3) :
    (targetSetSinkGraph G Y).Adj (Sum.inl a) (Sum.inr j) ↔ a ∈ Y := by
  simp [targetSetSinkGraph]

@[simp] theorem targetSetSinkGraph_sink_left_adj_iff
    {V : Type u} (G : SimpleGraph V) (Y : Set V) (j : Fin 3) (a : V) :
    (targetSetSinkGraph G Y).Adj (Sum.inr j) (Sum.inl a) ↔ a ∈ Y := by
  simp [targetSetSinkGraph]

@[simp] theorem targetSetSinkGraph_sink_sink_adj_iff
    {V : Type u} (G : SimpleGraph V) (Y : Set V) (i j : Fin 3) :
    Not ((targetSetSinkGraph G Y).Adj (Sum.inr i) (Sum.inr j)) := by
  simp [targetSetSinkGraph]

def targetSetSinkOriginalDeleted
    {V : Type u} (S : Set (V ⊕ Fin 3)) : Set V :=
  {v : V | Sum.inl v ∈ S}

@[simp] theorem targetSetSinkOriginalDeleted_mem
    {V : Type u} (S : Set (V ⊕ Fin 3)) (v : V) :
    v ∈ targetSetSinkOriginalDeleted S ↔ Sum.inl v ∈ S := by
  rfl

theorem targetSetSinkOriginalDeleted_ncard_le
    {V : Type u} [Fintype V]
    (S : Set (V ⊕ Fin 3)) :
    (targetSetSinkOriginalDeleted S).ncard <= S.ncard := by
  classical
  exact Set.ncard_le_ncard_of_injOn
    (s := targetSetSinkOriginalDeleted S)
    (t := S)
    (f := fun v : V => Sum.inl v)
    (by
      intro v hv
      exact hv)
    (by
      intro a _ha b _hb h
      exact Sum.inl.inj h)

theorem targetSetSinkOriginalDeleted_ncard_lt_three
    {V : Type u} [Fintype V]
    {S : Set (V ⊕ Fin 3)}
    (hS : S.ncard < 3) :
    (targetSetSinkOriginalDeleted S).ncard < 3 := by
  have hle := targetSetSinkOriginalDeleted_ncard_le (V := V) S
  omega

theorem targetSetSink_sink_injective
    {V : Type u} :
    Function.Injective (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3)) := by
  intro i j h
  exact Sum.inr.inj h

theorem targetSetSink_left_injective
    {V : Type u} {left : Fin 3 -> V}
    (hleft : Function.Injective left) :
    Function.Injective
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3)) := by
  intro i j h
  exact hleft (Sum.inl.inj h)

noncomputable def targetSetSinkOriginalVertex
    {V : Type u}
    (z : Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))) : V :=
  Classical.choose z.2

theorem targetSetSinkOriginalVertex_spec
    {V : Type u}
    (z : Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))) :
    Sum.inl (targetSetSinkOriginalVertex z) = z.1 := by
  exact Classical.choose_spec z.2

@[simp] theorem targetSetSinkOriginalVertex_inl
    {V : Type u} (v : V) :
    targetSetSinkOriginalVertex
      (⟨Sum.inl v, ⟨v, rfl⟩⟩ :
        Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))) = v := by
  exact Sum.inl.inj (targetSetSinkOriginalVertex_spec
    (⟨Sum.inl v, ⟨v, rfl⟩⟩ :
      Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))))

noncomputable def targetSetSinkOriginalRangeHom
    {V : Type u} (G : SimpleGraph V) (Y : Set V) :
    (targetSetSinkGraph G Y).induce
        (Set.range (fun v : V => (Sum.inl v : V ⊕ Fin 3))) →g G where
  toFun z := targetSetSinkOriginalVertex z
  map_rel' := by
    intro a b h
    have ha := targetSetSinkOriginalVertex_spec a
    have hb := targetSetSinkOriginalVertex_spec b
    change (targetSetSinkGraph G Y).Adj a.1 b.1 at h
    rw [← ha, ← hb] at h
    simpa [targetSetSinkGraph] using h

theorem targetSetSinkOriginalRangeHom_injective
    {V : Type u} (G : SimpleGraph V) (Y : Set V) :
    Function.Injective (targetSetSinkOriginalRangeHom G Y) := by
  intro a b h
  apply Subtype.ext
  change targetSetSinkOriginalVertex a = targetSetSinkOriginalVertex b at h
  have ha := targetSetSinkOriginalVertex_spec a
  have hb := targetSetSinkOriginalVertex_spec b
  calc
    (a : V ⊕ Fin 3) = Sum.inl (targetSetSinkOriginalVertex a) := ha.symm
    _ = Sum.inl (targetSetSinkOriginalVertex b) := by rw [h]
    _ = (b : V ⊕ Fin 3) := hb

theorem targetSetSink_exists_sink_not_mem_of_ncard_lt_three
    {V : Type u} [Fintype V]
    {S : Set (V ⊕ Fin 3)}
    (hS : S.ncard < 3) :
    Exists fun j : Fin 3 => (Sum.inr j : V ⊕ Fin 3) ∉ S := by
  classical
  by_contra hnone
  have hall : forall j : Fin 3, (Sum.inr j : V ⊕ Fin 3) ∈ S := by
    intro j
    by_contra hj
    exact hnone ⟨j, hj⟩
  let f : Fin 3 -> S := fun j => ⟨Sum.inr j, hall j⟩
  have hf : Function.Injective f := by
    intro i j h
    exact Sum.inr.inj (congrArg Subtype.val h)
  have hcard : Fintype.card (Fin 3) <= Fintype.card S :=
    Fintype.card_le_of_injective f hf
  have hScard : Fintype.card S = S.ncard :=
    Set.fintypeCard_eq_ncard S
  simp only [Fintype.card_fin] at hcard
  omega

theorem targetSetSinkGraph_reachable_to_sink_after_delete
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {Y : Set V}
    {S : Set (V ⊕ Fin 3)} {x y : V} {j : Fin 3}
    (hxS : Sum.inl x ∉ S)
    (hyS : Sum.inl y ∉ S)
    (hjS : Sum.inr j ∉ S)
    (hyY : y ∈ Y)
    (hreach :
      (G.induce (targetSetSinkOriginalDeleted S)ᶜ).Reachable
        ⟨x, by simpa [targetSetSinkOriginalDeleted] using hxS⟩
        ⟨y, by simpa [targetSetSinkOriginalDeleted] using hyS⟩) :
    ((targetSetSinkGraph G Y).induce Sᶜ).Reachable
      ⟨Sum.inl x, hxS⟩ ⟨Sum.inr j, hjS⟩ := by
  classical
  obtain ⟨p, _hp, hp_support⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := (targetSetSinkOriginalDeleted S)ᶜ)
      (by simpa [targetSetSinkOriginalDeleted] using hxS)
      (by simpa [targetSetSinkOriginalDeleted] using hyS)
      hreach
  let q : (targetSetSinkGraph G Y).Walk (Sum.inl x) (Sum.inl y) :=
    p.map (targetSetSinkOriginalHom G Y)
  have hq_support :
      forall z : V ⊕ Fin 3, z ∈ q.support -> z ∈ Sᶜ := by
    intro z hz
    change z ∉ S
    change z ∈ (p.map (targetSetSinkOriginalHom G Y)).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    simp only [List.mem_map] at hz
    rcases hz with ⟨w, hw, rfl⟩
    exact hp_support w hw
  have hreach_left :
      ((targetSetSinkGraph G Y).induce Sᶜ).Reachable
        ⟨Sum.inl x, hxS⟩ ⟨Sum.inl y, hyS⟩ :=
    Walk.reachable_induce_of_support_subset q hq_support
  have hlast :
      ((targetSetSinkGraph G Y).induce Sᶜ).Adj
        ⟨Sum.inl y, hyS⟩ ⟨Sum.inr j, hjS⟩ := by
    simpa [targetSetSinkGraph] using hyY
  exact hreach_left.trans (SimpleGraph.Adj.reachable hlast)

theorem targetSetSinkGraph_not_separates_of_not_separates_from_set
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {left : Fin 3 -> V} {Y : Set V}
    (hnosep :
      forall S : Set V, S.ncard < 3 ->
        Not (SeparatesVertexTripleFromSetByDeletion G S left Y))
    {S : Set (V ⊕ Fin 3)} (hS : S.ncard < 3) :
    Not
      (SeparatesVertexTriplesByDeletion
        (targetSetSinkGraph G Y) S
        (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 3))
        (fun i : Fin 3 => (Sum.inr i : V ⊕ Fin 3))) := by
  classical
  intro hsep
  let S₀ : Set V := targetSetSinkOriginalDeleted S
  have hS₀ : S₀.ncard < 3 :=
    targetSetSinkOriginalDeleted_ncard_lt_three (V := V) (S := S) hS
  have hnot : Not (SeparatesVertexTripleFromSetByDeletion G S₀ left Y) :=
    hnosep S₀ hS₀
  apply hnot
  intro i y hli hyY hyS hreach
  have hli_sum : Sum.inl (left i) ∉ S := by
    simpa [S₀, targetSetSinkOriginalDeleted] using hli
  have hy_sum : Sum.inl y ∉ S := by
    simpa [S₀, targetSetSinkOriginalDeleted] using hyS
  obtain ⟨j, hjS⟩ :=
    targetSetSink_exists_sink_not_mem_of_ncard_lt_three
      (V := V) (S := S) hS
  have hreach_sink :
      ((targetSetSinkGraph G Y).induce Sᶜ).Reachable
        ⟨Sum.inl (left i), hli_sum⟩ ⟨Sum.inr j, hjS⟩ :=
    targetSetSinkGraph_reachable_to_sink_after_delete
      (G := G) (Y := Y) (S := S)
      hli_sum hy_sum hjS hyY (by simpa [S₀] using hreach)
  exact hsep i j hli_sum hjS hreach_sink


end Schematic.Math.GraphTheory
