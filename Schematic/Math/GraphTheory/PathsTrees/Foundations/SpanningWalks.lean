import Schematic.Math.GraphTheory.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
Routine path, cycle, and tree decomposition facts used implicitly in the paper.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The vertex-forgetting homomorphism from a subgraph's subtype graph to
its spanning coercion on the original vertex type. -/
def SimpleGraph.Subgraph.coeToSpanningCoeHom (H : G.Subgraph) :
    H.coe →g H.spanningCoe where
  toFun := Subtype.val
  map_rel' := by
    intro x y hxy
    exact hxy

/-- Regard a walk as a walk in the spanning graph consisting exactly of its
own edges.  This is the canonical common-cycle walk used by graph sums. -/
def SimpleGraph.Walk.toSpanningCoe {u v : V} (p : G.Walk u v) :
    p.toSubgraph.spanningCoe.Walk u v :=
  p.mapToSubgraph.map
    (SimpleGraph.Subgraph.coeToSpanningCoeHom p.toSubgraph)

@[simp]
theorem SimpleGraph.Walk.toSpanningCoe_mapLe {u v : V}
    (p : G.Walk u v) :
    (SimpleGraph.Walk.toSpanningCoe p).mapLe
        p.toSubgraph.spanningCoe_le = p := by
  simpa [SimpleGraph.Walk.toSpanningCoe,
    SimpleGraph.Subgraph.coeToSpanningCoeHom,
    SimpleGraph.Walk.mapLe, SimpleGraph.Walk.map_map] using
    p.map_mapToSubgraph_hom

@[simp]
theorem SimpleGraph.Walk.support_toSpanningCoe {u v : V}
    (p : G.Walk u v) :
    (SimpleGraph.Walk.toSpanningCoe p).support = p.support := by
  calc
    (SimpleGraph.Walk.toSpanningCoe p).support =
        ((SimpleGraph.Walk.toSpanningCoe p).mapLe
          p.toSubgraph.spanningCoe_le).support :=
      (SimpleGraph.Walk.support_mapLe_eq_support
        p.toSubgraph.spanningCoe_le
        (SimpleGraph.Walk.toSpanningCoe p)).symm
    _ = p.support := congrArg
      (fun q : G.Walk u v => q.support)
      (SimpleGraph.Walk.toSpanningCoe_mapLe p)

/-- Walks with the same ordered vertex support span the same simple graph,
even when the walks are typed over different ambient graphs. -/
theorem SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_support_eq
    {H : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (q : H.Walk c d)
    (h : p.support = q.support) :
    p.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe := by
  ext u v
  simp only [SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  rw [p.edges_eq_zipWith_support, q.edges_eq_zipWith_support, h]

/-- Cyclically re-basing the directed dart list of a closed walk does not
change the undirected graph spanned by the walk.  The two walks may live in
different ambient graphs; only their vertex type and rotated dart lists must
agree. -/
theorem SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_edges_isRotated
    {H : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (q : H.Walk c d)
    (h : p.edges ~r q.edges) :
    p.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe := by
  ext u v
  simp only [SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  exact h.mem_iff

/-- Two cyclic rotations of a nodup nonempty list with the same first entry
are equal.  Nodup makes the chosen basepoint unique. -/
theorem List.IsRotated.eq_of_nodup_head_eq
    {alpha : Type u} {l l' : List alpha}
    (hrot : l ~r l') (hlNodup : l.Nodup)
    (hl : l ≠ []) (hl' : l' ≠ [])
    (hhead : l.head hl = l'.head hl') :
    l = l' := by
  rcases hrot with ⟨n, rfl⟩
  have hpos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
  have hrotPos : 0 < (l.rotate n).length := by simpa using hpos
  have hnlt : n % l.length < l.length := Nat.mod_lt n hpos
  have hidx : l[0]'hpos = l[n % l.length]'hnlt := by
    calc
      l[0]'hpos = l.head hl := (List.head_eq_getElem_zero hl).symm
      _ = (l.rotate n).head hl' := hhead
      _ = (l.rotate n)[0]'hrotPos := List.head_eq_getElem_zero hl'
      _ = l[(0 + n) % l.length]'(Nat.mod_lt _ hpos) :=
        List.getElem_rotate l n 0 hrotPos
      _ = l[n % l.length]'hnlt := by simp
  have hnmod : n % l.length = 0 := by
    symm
    exact hlNodup.getElem_inj_iff.mp hidx
  symm
  exact hlNodup.rotate_eq_self_iff.mpr (Or.inl hnmod)

/-- Last-entry version of `List.IsRotated.eq_of_nodup_head_eq`. -/
theorem List.IsRotated.eq_of_nodup_getLast_eq
    {alpha : Type u} {l l' : List alpha}
    (hrot : l ~r l') (hlNodup : l.Nodup)
    (hl : l ≠ []) (hl' : l' ≠ [])
    (hlast : l.getLast hl = l'.getLast hl') :
    l = l' := by
  apply List.reverse_injective
  have hlrev : l.reverse ≠ [] := by
    intro h
    exact hl (List.reverse_eq_nil_iff.mp h)
  have hl'rev : l'.reverse ≠ [] := by
    intro h
    exact hl' (List.reverse_eq_nil_iff.mp h)
  apply List.IsRotated.eq_of_nodup_head_eq hrot.reverse
      (List.nodup_reverse.mpr hlNodup) hlrev hl'rev
  simpa [List.head_reverse] using hlast

/-- Simple closed walks with the same cyclic vertex order span the same
undirected graph, even when they live in different ambient graphs and use
different basepoints. -/
theorem SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_isCycle_tail_isRotated
    {V : Type u} [DecidableEq V] {G H : SimpleGraph V} {a b : V}
    (p : G.Walk a a) (q : H.Walk b b)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hrot : p.support.tail ~r q.support.tail) :
    p.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe := by
  have haTail : a ∈ p.support.tail :=
    p.end_mem_tail_support hp.not_nil
  have haQTail : a ∈ q.support.tail := hrot.mem_iff.mp haTail
  have haQ : a ∈ q.support := List.mem_of_mem_tail haQTail
  let q' : H.Walk a a := q.rotate a haQ
  have hq' : q'.IsCycle := SimpleGraph.Walk.IsCycle.rotate haQ hq
  have hrot' : p.support.tail ~r q'.support.tail :=
    hrot.trans (SimpleGraph.Walk.support_rotate q a haQ).symm
  have hpTailNe : p.support.tail ≠ [] := List.ne_nil_of_mem haTail
  have hq'TailNe : q'.support.tail ≠ [] := by
    exact List.ne_nil_of_mem (q'.end_mem_tail_support hq'.not_nil)
  have hlast :
      p.support.tail.getLast hpTailNe =
        q'.support.tail.getLast hq'TailNe := by
    rw [List.getLast_tail, List.getLast_tail,
      p.getLast_support, q'.getLast_support]
  have htailEq : p.support.tail = q'.support.tail :=
    List.IsRotated.eq_of_nodup_getLast_eq hrot'
      hp.support_nodup hpTailNe hq'TailNe hlast
  have hsupportEq : p.support = q'.support := by
    rw [← p.cons_tail_support, ← q'.cons_tail_support, htailEq]
  calc
    p.toSubgraph.spanningCoe = q'.toSubgraph.spanningCoe :=
      SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_support_eq p q' hsupportEq
    _ = q.toSubgraph.spanningCoe :=
      SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_edges_isRotated
        q' q (SimpleGraph.Walk.rotate_edges q a haQ)

/-- A one-edge walk has exactly its two endpoints as its ordered support. -/
theorem SimpleGraph.Walk.support_eq_pair_of_length_eq_one
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (h : p.length = 1) :
    p.support = [u, v] := by
  cases p with
  | nil => simp at h
  | @cons _ x _ hux q =>
      simp only [SimpleGraph.Walk.length_cons] at h
      have hqLength : q.length = 0 := by omega
      have hxv : x = v :=
        SimpleGraph.Walk.eq_of_length_eq_zero hqLength
      subst x
      have hq : q = SimpleGraph.Walk.nil :=
        SimpleGraph.Walk.length_eq_zero_iff.mp hqLength
      subst q
      rfl

/-- A one-edge walk traverses exactly the unordered edge of its endpoints. -/
theorem SimpleGraph.Walk.edges_eq_singleton_of_length_eq_one
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (h : p.length = 1) :
    p.edges = [s(u, v)] := by
  cases p with
  | nil => simp at h
  | @cons _ x _ hux q =>
      simp only [SimpleGraph.Walk.length_cons] at h
      have hqLength : q.length = 0 := by omega
      have hxv : x = v :=
        SimpleGraph.Walk.eq_of_length_eq_zero hqLength
      subst x
      have hq : q = SimpleGraph.Walk.nil :=
        SimpleGraph.Walk.length_eq_zero_iff.mp hqLength
      subst q
      rfl

/-- If a simple path traverses the edge joining its two endpoints, then that
edge is the whole path. -/
theorem SimpleGraph.Walk.IsPath.length_eq_one_of_endpoints_mem_edges
    {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (hmem : s(u, v) ∈ p.edges) :
    p.length = 1 := by
  have hnil : ¬p.Nil := by
    rw [← SimpleGraph.Walk.edges_eq_nil]
    exact List.ne_nil_of_mem hmem
  have hone_le : 1 ≤ p.length := by
    have := SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil
    omega
  have hsnd : p.getVert 1 = v :=
    (hp.eq_snd_of_mem_edges hmem).symm
  exact ((hp.getVert_eq_end_iff hone_le).mp hsnd).symm

/-- Reindex a walk by the endpoints of another walk with the same ordered
support.  Equality of the first and last support entries supplies the endpoint
equalities; `Walk.copy` changes only the dependent endpoint indices and leaves
the support, darts, and path property unchanged. -/
theorem SimpleGraph.Walk.exists_copy_of_support_eq
    {H : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (q : H.Walk c d)
    (hsupport : q.support = p.support) :
    Exists fun q' : H.Walk a b =>
      q'.support = q.support ∧ q'.darts = q.darts ∧
        (q'.IsPath ↔ q.IsPath) := by
  have hstart : c = a := by
    have hhead := congrArg List.head? hsupport
    simpa [List.head?_eq_some_head] using hhead
  have hend : d = b := by
    have hlast := congrArg List.getLast? hsupport
    simpa [List.getLast?_eq_some_getLast] using hlast
  let q' : H.Walk a b := q.copy hstart hend
  exact ⟨q', by simp [q'], by simp [q'], by simp [q']⟩

theorem list_length_le_of_nodup_subset
    {α : Type u}
    [DecidableEq α]
    {l₁ l₂ : List α}
    (hnd : l₁.Nodup)
    (hsub : forall a : α, a ∈ l₁ -> a ∈ l₂) :
    l₁.length <= l₂.length := by
  have hcard : l₁.toFinset.card <= l₂.toFinset.card := by
    exact Finset.card_le_card (by
      intro a ha
      rw [List.mem_toFinset] at ha ⊢
      exact hsub a ha)
  rw [List.toFinset_card_of_nodup hnd] at hcard
  exact le_trans hcard (List.toFinset_card_le l₂)

/-- A nodup cyclic list splits, when rebased at `s`, into the clockwise open
arc from `s` to `t`, then `t`, then the clockwise open arc back to `s`.

The open arcs are expressed in the same rotate/take/`idxOf` form used by
`CyclicBoundary`, so this lemma supplies the exact ordered-list identity
needed when two disk boundaries are glued along a common path. -/
theorem list_rotate_idxOf_two_arc_decomposition
    {α : Type u} [DecidableEq α]
    (l : List α) (s t : α)
    (hnd : l.Nodup) (hs : s ∈ l) (ht : t ∈ l) (hst : s ≠ t) :
    l.rotate (l.idxOf s) =
      s ::
        (l.rotate (l.idxOf s + 1)).take
            ((l.rotate (l.idxOf s + 1)).idxOf t) ++
          t ::
            (l.rotate (l.idxOf t + 1)).take
              ((l.rotate (l.idxOf t + 1)).idxOf s) := by
  have hidxOfAppendCons (A B : List α) (x : α) (hx : x ∉ A) :
      (A ++ x :: B).idxOf x = A.length := by
    rw [List.idxOf_append_of_notMem hx]
    simp
  have hrotateAtAppendCons (A B : List α) (x : α) :
      (A ++ x :: B).rotate A.length = x :: B ++ A := by
    simp
  have hrotateAfterAppendCons (A B : List α) (x : α) :
      (A ++ x :: B).rotate (A.length + 1) = B ++ A ++ [x] := by
    rw [show A ++ x :: B = (A ++ [x]) ++ B by simp]
    rw [show A.length + 1 = (A ++ [x]).length by simp]
    rw [List.rotate_append_length_eq]
    simp [List.append_assoc]
  have hrotateAtIdxOfAppendCons (A B : List α) (x : α) (hx : x ∉ A) :
      (A ++ x :: B).rotate ((A ++ x :: B).idxOf x) = x :: B ++ A := by
    rw [hidxOfAppendCons A B x hx]
    exact hrotateAtAppendCons A B x
  have hrotateAfterIdxOfAppendCons
      (A B : List α) (x : α) (hx : x ∉ A) :
      (A ++ x :: B).rotate ((A ++ x :: B).idxOf x + 1) =
        B ++ A ++ [x] := by
    rw [hidxOfAppendCons A B x hx]
    exact hrotateAfterAppendCons A B x
  have htakeToAppendCons (A B : List α) (x : α) (hx : x ∉ A) :
      (A ++ x :: B).take ((A ++ x :: B).idxOf x) = A := by
    rw [hidxOfAppendCons A B x hx]
    simp
  rcases (List.mem_iff_append).mp hs with ⟨pre, post, rfl⟩
  have hparts := List.nodup_append'.mp hnd
  have hpreN : pre.Nodup := hparts.1
  have hspostN : (s :: post).Nodup := hparts.2.1
  have hdisjoint : pre.Disjoint (s :: post) := hparts.2.2
  have hsPre : s ∉ pre := by
    intro h
    exact hdisjoint h (by simp)
  have hsPost : s ∉ post :=
    (List.nodup_cons.mp hspostN).1
  have htCases : t ∈ pre ∨ t ∈ post := by
    simpa [hst.symm] using ht
  rcases htCases with htPre | htPost
  · rcases (List.mem_iff_append).mp htPre with ⟨before, middle, rfl⟩
    have hpreParts := List.nodup_append'.mp hpreN
    have htmiddleN : (t :: middle).Nodup := hpreParts.2.1
    have hpreDisjoint : before.Disjoint (t :: middle) := hpreParts.2.2
    have htBefore : t ∉ before := by
      intro h
      exact hpreDisjoint h (by simp)
    have htMiddle : t ∉ middle :=
      (List.nodup_cons.mp htmiddleN).1
    have hsMiddle : s ∉ middle := by
      intro h
      exact hsPre (by simp [h])
    have htPost' : t ∉ post := by
      intro h
      have htLeft : t ∈ before ++ t :: middle := by simp
      have htRight : t ∈ s :: post := by simp [h]
      exact hdisjoint htLeft htRight
    have hrotS :
        (before ++ t :: middle ++ s :: post).rotate
            ((before ++ t :: middle ++ s :: post).idxOf s) =
          s :: post ++ before ++ t :: middle := by
      simpa only [List.append_assoc] using
        hrotateAtIdxOfAppendCons (before ++ t :: middle) post s hsPre
    have hrotAfterS :
        (before ++ t :: middle ++ s :: post).rotate
            ((before ++ t :: middle ++ s :: post).idxOf s + 1) =
          post ++ before ++ t :: middle ++ [s] := by
      simpa only [List.append_assoc] using
        hrotateAfterIdxOfAppendCons (before ++ t :: middle) post s hsPre
    have htakeLeft :
        ((before ++ t :: middle ++ s :: post).rotate
            ((before ++ t :: middle ++ s :: post).idxOf s + 1)).take
              (((before ++ t :: middle ++ s :: post).rotate
                ((before ++ t :: middle ++ s :: post).idxOf s + 1)).idxOf t) =
          post ++ before := by
      rw [hrotAfterS]
      have htPrefix : t ∉ post ++ before := by
        simp [htPost', htBefore]
      simpa only [List.append_assoc] using
        htakeToAppendCons (post ++ before) (middle ++ [s]) t htPrefix
    have hrotAfterT :
        (before ++ t :: middle ++ s :: post).rotate
            ((before ++ t :: middle ++ s :: post).idxOf t + 1) =
          middle ++ s :: post ++ before ++ [t] := by
      simpa only [List.append_assoc] using
        hrotateAfterIdxOfAppendCons before (middle ++ s :: post) t htBefore
    have htakeRight :
        ((before ++ t :: middle ++ s :: post).rotate
            ((before ++ t :: middle ++ s :: post).idxOf t + 1)).take
              (((before ++ t :: middle ++ s :: post).rotate
                ((before ++ t :: middle ++ s :: post).idxOf t + 1)).idxOf s) =
          middle := by
      rw [hrotAfterT]
      simpa only [List.append_assoc] using
        htakeToAppendCons middle (post ++ before ++ [t]) s hsMiddle
    rw [hrotS, htakeLeft, htakeRight]
    simp only [List.cons_append, List.append_assoc]
  · rcases (List.mem_iff_append).mp htPost with ⟨middle, after, rfl⟩
    have hpostN : (middle ++ t :: after).Nodup :=
      (List.nodup_cons.mp hspostN).2
    have hpostParts := List.nodup_append'.mp hpostN
    have htafterN : (t :: after).Nodup := hpostParts.2.1
    have hpostDisjoint : middle.Disjoint (t :: after) := hpostParts.2.2
    have htPre' : t ∉ pre := by
      intro h
      exact hdisjoint h (by simp)
    have htMiddle : t ∉ middle := by
      intro h
      exact hpostDisjoint h (by simp)
    have hsMiddle : s ∉ middle := by
      intro h
      exact hsPost (by simp [h])
    have hsAfter : s ∉ after := by
      intro h
      exact hsPost (by simp [h])
    have hrotS :
        (pre ++ s :: (middle ++ t :: after)).rotate
            ((pre ++ s :: (middle ++ t :: after)).idxOf s) =
          s :: (middle ++ t :: after) ++ pre :=
      hrotateAtIdxOfAppendCons pre (middle ++ t :: after) s hsPre
    have hrotAfterS :
        (pre ++ s :: (middle ++ t :: after)).rotate
            ((pre ++ s :: (middle ++ t :: after)).idxOf s + 1) =
          (middle ++ t :: after) ++ pre ++ [s] :=
      hrotateAfterIdxOfAppendCons pre (middle ++ t :: after) s hsPre
    have htakeLeft :
        ((pre ++ s :: (middle ++ t :: after)).rotate
            ((pre ++ s :: (middle ++ t :: after)).idxOf s + 1)).take
              (((pre ++ s :: (middle ++ t :: after)).rotate
                ((pre ++ s :: (middle ++ t :: after)).idxOf s + 1)).idxOf t) =
          middle := by
      rw [hrotAfterS]
      simpa only [List.append_assoc] using
        htakeToAppendCons middle (after ++ pre ++ [s]) t htMiddle
    have hrotAfterT :
        (pre ++ s :: (middle ++ t :: after)).rotate
            ((pre ++ s :: (middle ++ t :: after)).idxOf t + 1) =
          after ++ pre ++ s :: middle ++ [t] := by
      have htA : t ∉ pre ++ s :: middle := by
        simp [htPre', hst.symm, htMiddle]
      simpa only [List.append_assoc] using
        hrotateAfterIdxOfAppendCons (pre ++ s :: middle) after t htA
    have htakeRight :
        ((pre ++ s :: (middle ++ t :: after)).rotate
            ((pre ++ s :: (middle ++ t :: after)).idxOf t + 1)).take
              (((pre ++ s :: (middle ++ t :: after)).rotate
                ((pre ++ s :: (middle ++ t :: after)).idxOf t + 1)).idxOf s) =
          after ++ pre := by
      rw [hrotAfterT]
      have hsPrefix : s ∉ after ++ pre := by simp [hsAfter, hsPre]
      simpa only [List.append_assoc] using
        htakeToAppendCons (after ++ pre) (middle ++ [t]) s hsPrefix
    rw [hrotS, htakeLeft, htakeRight]
    simp only [List.cons_append, List.append_assoc]

theorem list_le_idxOf_of_mem_drop_of_nodup
    {α : Type u}
    [DecidableEq α]
    {l : List α}
    (hnd : l.Nodup)
    {a : α}
    {n : Nat}
    (ha : a ∈ l.drop n) :
    n <= l.idxOf a := by
  by_contra hnot
  have hlt : l.idxOf a < n := Nat.lt_of_not_ge hnot
  have ha_l : a ∈ l := List.mem_of_mem_drop ha
  have ha_take : a ∈ l.take n := (List.mem_take_iff_idxOf_lt ha_l).mpr hlt
  exact (List.disjoint_take_drop hnd (le_refl n)) ha_take ha

theorem list_idxOf_le_of_mem_drop_take_idxOf_succ_of_nodup
    {α : Type u}
    [DecidableEq α]
    {l : List α}
    {x y z : α}
    (hx : x ∈ l)
    (hy : y ∈ l)
    (hxy : l.idxOf x <= l.idxOf y)
    (hz :
      z ∈
        (l.drop (l.idxOf x)).take
          ((l.drop (l.idxOf x)).idxOf y + 1)) :
    l.idxOf z <= l.idxOf y := by
  let n := l.idxOf x
  let q := l.drop n
  have hn_len : n <= l.length := by
    have hxlt := List.idxOf_lt_length_of_mem hx
    omega
  have hzq : z ∈ q := by
    exact List.mem_of_mem_take (by simpa [q, n] using hz)
  have hzq_idx_le :
      q.idxOf z <= q.idxOf y := by
    have hlt :
        q.idxOf z < q.idxOf y + 1 := by
      exact (List.mem_take_iff_idxOf_lt hzq).mp (by simpa [q, n] using hz)
    omega
  have hnot_y_take : y ∉ l.take n := by
    intro hy_take
    have hy_idx_lt : l.idxOf y < n :=
      (List.mem_take_iff_idxOf_lt hy).mp hy_take
    omega
  have hidx_y :
      l.idxOf y = n + q.idxOf y := by
    have hidx_append :
        (l.take n ++ q).idxOf y = (l.take n).length + q.idxOf y := by
      exact List.idxOf_append_of_notMem hnot_y_take
    have htake_len : (l.take n).length = n := by
      simp [n, Nat.min_eq_left hn_len]
    rw [← List.take_append_drop n l]
    simpa [q, htake_len] using hidx_append
  have hsuffix : q <:+ l := by
    simpa [q] using List.drop_suffix n l
  have hz_l_le :
      l.idxOf z <= n + q.idxOf z := by
    have hle := hsuffix.idxOf_le z
    have hlen_sub : l.length - q.length = n := by
      simp [q]
      omega
    omega
  omega

theorem list_mem_drop_take_idxOf_succ_of_idxOf_between
    {α : Type u}
    [DecidableEq α]
    {l : List α}
    {x y z : α}
    (hx : x ∈ l)
    (hy : y ∈ l)
    (hz : z ∈ l)
    (hxy : l.idxOf x <= l.idxOf y)
    (hyz : l.idxOf y <= l.idxOf z) :
    y ∈
      (l.drop (l.idxOf x)).take
        ((l.drop (l.idxOf x)).idxOf z + 1) := by
  let n := l.idxOf x
  let q := l.drop n
  have hn_len : n <= l.length := by
    have hxlt := List.idxOf_lt_length_of_mem hx
    omega
  have hnot_y_take : y ∉ l.take n := by
    intro hy_take
    have hy_idx_lt : l.idxOf y < n :=
      (List.mem_take_iff_idxOf_lt hy).mp hy_take
    omega
  have hnot_z_take : z ∉ l.take n := by
    intro hz_take
    have hz_idx_lt : l.idxOf z < n :=
      (List.mem_take_iff_idxOf_lt hz).mp hz_take
    omega
  have hidx_y :
      l.idxOf y = n + q.idxOf y := by
    have hidx_append :
        (l.take n ++ q).idxOf y = (l.take n).length + q.idxOf y := by
      exact List.idxOf_append_of_notMem hnot_y_take
    have htake_len : (l.take n).length = n := by
      simp [n, Nat.min_eq_left hn_len]
    rw [← List.take_append_drop n l]
    simpa [q, htake_len] using hidx_append
  have hidx_z :
      l.idxOf z = n + q.idxOf z := by
    have hidx_append :
        (l.take n ++ q).idxOf z = (l.take n).length + q.idxOf z := by
      exact List.idxOf_append_of_notMem hnot_z_take
    have htake_len : (l.take n).length = n := by
      simp [n, Nat.min_eq_left hn_len]
    rw [← List.take_append_drop n l]
    simpa [q, htake_len] using hidx_append
  have hyq : y ∈ q := by
    have hyidx_lt : l.idxOf y < l.length :=
      List.idxOf_lt_length_of_mem hy
    let m := l.idxOf y - n
    have hm_length : m < q.length := by
      simp [q, n]
      omega
    have hnm : n + m = l.idxOf y := by
      simp [m]
      omega
    have hget_idx : l[n + m] = y := by
      simp [hnm]
    have hget : q[m] = y := by
      simp [q, n, List.getElem_drop, hget_idx]
    exact hget ▸ List.getElem_mem hm_length
  have hq_idx : q.idxOf y <= q.idxOf z := by
    omega
  exact (List.mem_take_iff_idxOf_lt hyq).mpr (Nat.lt_succ_of_le hq_idx)


end Schematic.Math.GraphTheory
