import Schematic.Math.GraphTheory.Minors.Rerouting.PartialConstruction

/-! Residual cut sets for partial set linkages. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace PartialSetLinkage

def RawSplitResidualCutSet
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) : Set V :=
  {v : V |
    L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.inn v) ∧
      Not
        (L.SplitResidualReachableFromUnusedSource
          (VertexSplitState.out v))}

theorem RawSplitResidualCutSet.subset_usedVertices
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    L.RawSplitResidualCutSet ⊆ L.usedVertices := by
  intro v hv
  by_contra hvUnused
  exact hv.2
    (hv.1.step (by
      exact Or.inl ⟨rfl, hvUnused⟩))

theorem RawSplitResidualCutSet.eq_of_mem_same_path
    [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    {v w : V}
    (hv : v ∈ L.RawSplitResidualCutSet)
    (hw : w ∈ L.RawSplitResidualCutSet)
    {k : Fin n}
    (hvk : v ∈ (L.path k).support)
    (hwk : w ∈ (L.path k).support) :
    v = w := by
  classical
  let p := L.path k
  let iv := p.support.idxOf v
  let iw := p.support.idxOf w
  have hiv : iv < p.support.length :=
    List.idxOf_lt_length_of_mem (by simpa [p] using hvk)
  have hiw : iw < p.support.length :=
    List.idxOf_lt_length_of_mem (by simpa [p] using hwk)
  have hivLen : iv <= p.length := by
    rw [p.length_support] at hiv
    omega
  have hiwLen : iw <= p.length := by
    rw [p.length_support] at hiw
    omega
  have hgetv : p.getVert iv = v := by
    exact p.getVert_support_idxOf (by simpa [p] using hvk)
  have hgetw : p.getVert iw = w := by
    exact p.getVert_support_idxOf (by simpa [p] using hwk)
  rcases lt_trichotomy iv iw with hivw | hivw | hivw
  · have hout :
        L.SplitResidualReachableFromUnusedSource
          (VertexSplitState.out v) := by
      have :=
        L.path_getVert_splitOutReachable_of_later_splitInReachable
          k hivw hiwLen (by simpa [p, hgetw] using hw.1)
      simpa [p, hgetv] using this
    exact False.elim (hv.2 hout)
  · exact by
      have hidx :
          p.support.idxOf v = p.support.idxOf w := by
        simpa [iv, iw] using hivw
      exact (List.idxOf_inj (by simpa [p] using hvk)).mp hidx
  · have hout :
        L.SplitResidualReachableFromUnusedSource
          (VertexSplitState.out w) := by
      have :=
        L.path_getVert_splitOutReachable_of_later_splitInReachable
          k hivw hivLen (by simpa [p, hgetv] using hv.1)
      simpa [p, hgetw] using this
    exact False.elim (hw.2 hout)

noncomputable def rawCutPathIndex
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (v : L.RawSplitResidualCutSet) : Fin n :=
  Classical.choose
    (RawSplitResidualCutSet.subset_usedVertices L v.property)

theorem rawCutPathIndex_spec
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (v : L.RawSplitResidualCutSet) :
    (v : V) ∈ (L.path (L.rawCutPathIndex v)).support :=
  Classical.choose_spec
    (RawSplitResidualCutSet.subset_usedVertices L v.property)

theorem rawCutPathIndex_injective
    [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    Function.Injective L.rawCutPathIndex := by
  intro v w hi
  apply Subtype.ext
  exact
    RawSplitResidualCutSet.eq_of_mem_same_path L
      v.property w.property
      (L.rawCutPathIndex_spec v)
      (by
        rw [hi]
        exact L.rawCutPathIndex_spec w)

theorem RawSplitResidualCutSet.ncard_le
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    L.RawSplitResidualCutSet.ncard <= n := by
  classical
  have hcard :
      Fintype.card L.RawSplitResidualCutSet <=
        Fintype.card (Fin n) :=
    Fintype.card_le_of_injective L.rawCutPathIndex
      L.rawCutPathIndex_injective
  rw [Set.fintypeCard_eq_ncard, Fintype.card_fin] at hcard
  exact hcard

/--
The canonical cut picks the first vertex on each occupied path whose split
`out` state is not reachable.  If every state on a path is reachable, its
target is used as the harmless fallback.
-/
noncomputable def splitResidualCutVertex
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) (k : Fin n) : V := by
  classical
  exact
    match (L.path k).support.find?
        (fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedSource
                (VertexSplitState.out v))) with
    | some v => v
    | none => L.target k

def splitResidualCutSet
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) : Set V :=
  Set.range L.splitResidualCutVertex

theorem splitResidualCutSet_ncard_le
    [Fintype V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    L.splitResidualCutSet.ncard <= n := by
  classical
  have hcard :
      Fintype.card (Set.range L.splitResidualCutVertex) <=
        Fintype.card (Fin n) :=
    Fintype.card_range_le L.splitResidualCutVertex
  rw [Set.fintypeCard_eq_ncard] at hcard
  simpa [splitResidualCutSet] using hcard

theorem splitResidualCutVertex_mem_support
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) (k : Fin n) :
    L.splitResidualCutVertex k ∈ (L.path k).support := by
  classical
  unfold splitResidualCutVertex
  generalize hfind :
      (L.path k).support.find?
        (fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedSource
                (VertexSplitState.out v))) = o
  cases o with
  | none => simp
  | some v =>
      have hsome :=
        (List.find?_eq_some_iff_getElem.mp hfind).2
      rcases hsome with ⟨i, hi, hget, _⟩
      rw [← hget]
      exact List.getElem_mem hi

theorem splitResidualCutVertex_eq_target_of_target_out_reachable
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) (k : Fin n)
    (htarget :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.out (L.target k))) :
    L.splitResidualCutVertex k = L.target k := by
  classical
  have hall :
      forall x : V, x ∈ (L.path k).support ->
        L.SplitResidualReachableFromUnusedSource
          (VertexSplitState.out x) := by
    intro x hx
    exact
      PartialSetLinkage.Walk.start_splitOutReachable_of_end_splitOutReachable_of_darts_subset
        L k ((L.path k).dropUntil x hx)
        ((L.path k).darts_dropUntil_subset hx) htarget
  unfold splitResidualCutVertex
  have hnone :
      (L.path k).support.find?
          (fun v =>
            ! decide
                (L.SplitResidualReachableFromUnusedSource
                  (VertexSplitState.out v))) =
        none := by
    rw [List.find?_eq_none]
    intro x hx
    simp [hall x hx]
  simp [hnone]

theorem splitResidualCutVertex_eq_source_of_source_out_not_reachable
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) (k : Fin n)
    (hsource :
      Not
        (L.SplitResidualReachableFromUnusedSource
          (VertexSplitState.out (L.source k)))) :
    L.splitResidualCutVertex k = L.source k := by
  classical
  unfold splitResidualCutVertex
  have hfind :
      (L.path k).support.find?
          (fun v =>
            ! decide
                (L.SplitResidualReachableFromUnusedSource
                  (VertexSplitState.out v))) =
        some (L.source k) := by
    let l := (L.path k).support
    have hl_ne : l ≠ [] := by simp [l]
    have hhead : l.head hl_ne = L.source k := by simp [l]
    have hpred :
        (fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedSource
                (VertexSplitState.out v))) (l.head hl_ne) = true := by
      simp [hhead, hsource]
    change l.find?
        (fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedSource
                (VertexSplitState.out v))) =
      some (L.source k)
    rw [← List.cons_head_tail hl_ne]
    simpa [hhead] using
      (List.find?_cons_of_pos
        (p := fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedSource
                (VertexSplitState.out v)))
        (a := l.head hl_ne) (l := l.tail) hpred)
  simp [hfind]

theorem RawSplitResidualCutSet.subset_splitResidualCutSet
    [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    L.RawSplitResidualCutSet ⊆ L.splitResidualCutSet := by
  classical
  intro v hv
  have hvUsed := RawSplitResidualCutSet.subset_usedVertices L hv
  rcases hvUsed with ⟨k, hvk⟩
  refine ⟨k, ?_⟩
  let p := L.path k
  let iv := p.support.idxOf v
  have hiv : iv < p.support.length :=
    List.idxOf_lt_length_of_mem (by simpa [p] using hvk)
  have hivLen : iv <= p.length := by
    rw [p.length_support] at hiv
    omega
  have hgetv : p.getVert iv = v :=
    p.getVert_support_idxOf (by simpa [p] using hvk)
  unfold splitResidualCutVertex
  generalize hfind :
      p.support.find?
        (fun w =>
          ! decide
              (L.SplitResidualReachableFromUnusedSource
                (VertexSplitState.out w))) = o
  cases o with
  | none =>
      have hnone :=
        List.find?_eq_none.mp hfind v (by simpa [p] using hvk)
      simp [hv.2] at hnone
  | some c =>
      have hspec := List.find?_eq_some_iff_getElem.mp hfind
      have hcPred : Not
          (L.SplitResidualReachableFromUnusedSource
            (VertexSplitState.out c)) := by
        simpa using hspec.1
      rcases hspec.2 with ⟨ic, hic, hgetc, hminimal⟩
      have hicLen : ic <= p.length := by
        rw [p.length_support] at hic
        omega
      have hpgetc : p.getVert ic = c := by
        rw [p.getVert_eq_support_getElem hicLen]
        exact hgetc
      have hic_le_iv : ic <= iv := by
        by_contra hnot
        have hiv_lt_ic : iv < ic := by omega
        have hmin := hminimal iv hiv_lt_ic
        have hsupportv : p.support[iv]'hiv = v :=
          List.getElem_idxOf hiv
        simp [hsupportv, hv.2] at hmin
      by_cases hci : ic = iv
      · calc
          c = p.getVert ic := hpgetc.symm
          _ = p.getVert iv := by rw [hci]
          _ = v := hgetv
      · have hic_lt_iv : ic < iv := lt_of_le_of_ne hic_le_iv hci
        have houtc :=
          L.path_getVert_splitOutReachable_of_later_splitInReachable
            k hic_lt_iv hivLen (by simpa [p, hgetv] using hv.1)
        exact False.elim (hcPred (by simpa [p, hpgetc] using houtc))

theorem splitOutReachable_of_splitInReachable_of_not_mem_cut
    [DecidableEq V]
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n} {v : V}
    (hin :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.inn v))
    (hv : v ∉ L.splitResidualCutSet) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.out v) := by
  by_contra hout
  exact hv
    (RawSplitResidualCutSet.subset_splitResidualCutSet L ⟨hin, hout⟩)

theorem source_splitOutReachable_of_not_mem_cut
    [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    {x : V}
    (hxX : x ∈ X)
    (hxCut : x ∉ L.splitResidualCutSet) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.out x) := by
  by_cases hxUnused : x ∉ L.usedVertices
  · exact
      (L.unused_source_reachable hxX hxUnused).step (by
        exact Or.inl ⟨rfl, hxUnused⟩)
  · have hxUsed : x ∈ L.usedVertices := by simpa using hxUnused
    have hxSelected : x ∈ L.sourceSet :=
      (Set.ext_iff.mp L.usedVertices_inter_sourceSet x).mp
        ⟨hxUsed, hxX⟩
    rcases hxSelected with ⟨k, hk⟩
    by_contra hout
    apply hxCut
    refine ⟨k, ?_⟩
    have hcut :=
      L.splitResidualCutVertex_eq_source_of_source_out_not_reachable
        k (by simpa [← hk] using hout)
    simpa [← hk] using hcut

theorem target_not_splitOutReachable_of_not_mem_cut
    [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hno : Not L.SplitResidualReachesUnusedTarget)
    {y : V}
    (hyY : y ∈ Y)
    (hyCut : y ∉ L.splitResidualCutSet) :
    Not
      (L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.out y)) := by
  by_cases hyUnused : y ∉ L.usedVertices
  · intro hyReach
    exact hno ⟨y, hyY, hyUnused, hyReach⟩
  · have hyUsed : y ∈ L.usedVertices := by simpa using hyUnused
    have hySelected : y ∈ L.targetSet :=
      (Set.ext_iff.mp L.usedVertices_inter_targetSet y).mp
        ⟨hyUsed, hyY⟩
    rcases hySelected with ⟨k, hk⟩
    intro hyReach
    apply hyCut
    refine ⟨k, ?_⟩
    have hcut :=
      L.splitResidualCutVertex_eq_target_of_target_out_reachable
        k (by simpa [← hk] using hyReach)
    simpa [← hk] using hcut

theorem Walk.end_splitOutReachable_of_avoids_cut
    [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    {a b : V}
    (p : G.Walk a b)
    (ha :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.out a))
    (hadmissible :
      forall d : G.Dart, d ∈ p.darts ->
        d.fst ∉ Y ∧ d.snd ∉ X)
    (havoid :
      forall v : V, v ∈ p.support ->
        v ∉ L.splitResidualCutSet) :
    L.SplitResidualReachableFromUnusedSource
      (VertexSplitState.out b) := by
  induction p with
  | nil =>
      exact ha
  | @cons u v w huv p ih =>
      let d : G.Dart := ⟨(u, v), huv⟩
      have hd : d ∈ (SimpleGraph.Walk.cons huv p).darts := by
        simp [d, SimpleGraph.Walk.darts_cons]
      have hdAllowed := hadmissible d hd
      have hvIn :
          L.SplitResidualReachableFromUnusedSource
            (VertexSplitState.inn v) :=
        ha.step (by
          exact Or.inr ⟨huv, hdAllowed.1, hdAllowed.2⟩)
      have hvOut :
          L.SplitResidualReachableFromUnusedSource
            (VertexSplitState.out v) :=
        L.splitOutReachable_of_splitInReachable_of_not_mem_cut
          hvIn (havoid v (by simp [SimpleGraph.Walk.support_cons]))
      apply ih hvOut
      · intro e he
        exact hadmissible e (by
          simp [SimpleGraph.Walk.darts_cons, he])
      · intro z hz
        exact havoid z (by
          simp [SimpleGraph.Walk.support_cons, hz])

theorem SetToSetPathData.dart_admissible
    [DecidableEq V]
    {X Y : Set V} {u v : V}
    {p : G.Walk u v}
    (D : SetToSetPathData p X Y)
    (d : G.Dart)
    (hd : d ∈ D.path.darts) :
    d.fst ∉ Y ∧ d.snd ∉ X := by
  constructor
  · intro hdY
    have hfstSupport :
        d.fst ∈ D.path.support :=
      D.path.dart_fst_mem_support_of_mem_darts hd
    have hfstTarget : d.fst = D.target :=
      D.target_clean d.fst hfstSupport hdY
    exact
      (Walk.IsPath.dart_fst_ne_end_of_mem_darts D.isPath hd)
        hfstTarget
  · intro hdX
    have hsndSupport :
        d.snd ∈ D.path.support :=
      D.path.dart_snd_mem_support_of_mem_darts hd
    have hsndSource : d.snd = D.source :=
      D.source_clean d.snd hsndSupport hdX
    have hdReverse : d.symm ∈ D.path.reverse.darts := by
      rw [SimpleGraph.Walk.mem_darts_reverse]
      exact hd
    exact
      (Walk.IsPath.dart_fst_ne_end_of_mem_darts
        D.isPath.reverse hdReverse) (by simpa using hsndSource)

theorem ThreeSetLinkage.exists_path_support_disjoint_of_ncard_lt_three
    [Fintype V] [DecidableEq V]
    {X Y : Set V}
    (L : ThreeSetLinkage G X Y)
    (C : Set V)
    (hC : C.ncard < 3) :
    Exists fun i : Fin 3 =>
      Disjoint {v : V | v ∈ (L.path i).support} C := by
  classical
  by_contra hnone
  push Not at hnone
  have hmeet :
      forall i : Fin 3,
        Exists fun v : V =>
          v ∈ (L.path i).support ∧ v ∈ C := by
    intro i
    exact Set.not_disjoint_iff.mp (hnone i)
  choose c hcPath hcC using hmeet
  let f : Fin 3 -> C := fun i => ⟨c i, hcC i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact
      Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hne)
        (hcPath i)
        (by simpa [show c i = c j from congrArg Subtype.val hij] using
          hcPath j)
  have hcard :
      Fintype.card (Fin 3) <= Fintype.card C :=
    Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Set.fintypeCard_eq_ncard] at hcard
  omega

/--
The separator half of the endpoint-preserving augmentation theorem.

If the endpoint-clean residual network has no augmenting chain, its canonical
cut has at most `n` vertices.  A full three-path `X -> Y` linkage has a path
avoiding that cut when `n < 3`; endpoint cleanliness then propagates residual
reachability to an unused target, a contradiction.
-/
theorem splitResidualReachesUnusedTarget_of_full_three
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n < 3)
    (F : ThreeSetLinkage G X Y) :
    L.SplitResidualReachesUnusedTarget := by
  by_contra hno
  have hcutCard : L.splitResidualCutSet.ncard < 3 :=
    lt_of_le_of_lt L.splitResidualCutSet_ncard_le hn
  obtain ⟨i, hiDisjoint⟩ :=
    ThreeSetLinkage.exists_path_support_disjoint_of_ncard_lt_three
      F L.splitResidualCutSet hcutCard
  let D : SetToSetPathData (F.path i) X Y := {
    source := F.source i
    target := F.target i
    source_mem := F.source_mem i
    target_mem := F.target_mem i
    path := F.path i
    isPath := F.isPath i
    support_subset := Set.Subset.rfl
    source_clean := F.source_clean i
    target_clean := F.target_clean i
  }
  have hsourceReach :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.out D.source) :=
    L.source_splitOutReachable_of_not_mem_cut D.source_mem (by
      intro hcut
      exact Set.disjoint_left.mp hiDisjoint D.path.start_mem_support hcut)
  have htargetReach :
      L.SplitResidualReachableFromUnusedSource
        (VertexSplitState.out D.target) :=
    PartialSetLinkage.Walk.end_splitOutReachable_of_avoids_cut
      L D.path hsourceReach
      (PartialSetLinkage.SetToSetPathData.dart_admissible D) (by
        intro z hz hcut
        exact Set.disjoint_left.mp hiDisjoint hz hcut)
  exact
    (L.target_not_splitOutReachable_of_not_mem_cut hno D.target_mem (by
      intro hcut
      exact Set.disjoint_left.mp hiDisjoint D.path.end_mem_support hcut))
      htargetReach

theorem SplitResidualReachesUnusedTarget.exists_isChain_list
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n}
    (hreach : L.SplitResidualReachesUnusedTarget) :
    Exists fun x : V =>
      Exists fun y : V =>
        x ∈ X ∧ x ∉ L.usedVertices ∧
          y ∈ Y ∧ y ∉ L.usedVertices ∧
            Exists fun l : List (VertexSplitState V) =>
              l ≠ [] ∧
                l.head? = some (VertexSplitState.inn x) ∧
                  l.getLast? = some (VertexSplitState.out y) ∧
                    l.IsChain L.SplitResidualStep := by
  rcases hreach with ⟨y, hyY, hyUnused, x, hxX, hxUnused, hrtg⟩
  rcases reflTransGen_exists_isChain_list hrtg with
    ⟨l, hne, hhead, hlast, hchain⟩
  exact
    ⟨x, y, hxX, hxUnused, hyY, hyUnused,
      l, hne, hhead, hlast, hchain⟩

theorem SplitResidualReachesUnusedTarget.exists_minimal_isChain_list
    {X Y : Set V} {n : Nat}
    {L : PartialSetLinkage G X Y n}
    (hreach : L.SplitResidualReachesUnusedTarget) :
    Exists fun x : V =>
      Exists fun y : V =>
        x ∈ X ∧ x ∉ L.usedVertices ∧
          y ∈ Y ∧ y ∉ L.usedVertices ∧
            Exists fun l : List (VertexSplitState V) =>
              l ≠ [] ∧
                l.head? = some (VertexSplitState.inn x) ∧
                  l.getLast? = some (VertexSplitState.out y) ∧
                    l.IsChain L.SplitResidualStep ∧
                      forall m : List (VertexSplitState V),
                        m ≠ [] ->
                          m.head? = some (VertexSplitState.inn x) ->
                            m.getLast? =
                              some (VertexSplitState.out y) ->
                              m.IsChain L.SplitResidualStep ->
                                l.length <= m.length := by
  rcases hreach with ⟨y, hyY, hyUnused, x, hxX, hxUnused, hrtg⟩
  rcases reflTransGen_exists_minimal_isChain_list hrtg with
    ⟨l, hne, hhead, hlast, hchain, hmin⟩
  exact
    ⟨x, y, hxX, hxUnused, hyY, hyUnused,
      l, hne, hhead, hlast, hchain, hmin⟩


end PartialSetLinkage

end Schematic.Math.GraphTheory
