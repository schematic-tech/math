import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.FacialPathSplits

/-! The complete finite fan construction for Euler rotation systems. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemFan

/-- Structured form of `exists_addNodeGraph_facialPathSplit_after_first`. -/
theorem exists_addNodeGraph_facialPathSplitData_after_first
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    {r s t : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    (p : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t)
    (k : Nat) (hk : k + 1 < c.length)
    (hpathDarts : p.darts = ((c.drop 1).take k).darts) :
    letI : DecidableRel
        (addNodeGraph G (insert t ({s} : Set V))).Adj := Classical.decRel _
    Nonempty (FacialPathSplitData R c p hp hst) := by
  classical
  rcases exists_addNodeGraph_facialPathSplit_after_first
      R hR c hc hfacial p hp hst k hk hpathDarts with
    ⟨S, hS, hselected, outerFace, lift, hlift, hliftTail, hliftHead,
      toStart, houterFirst, htoStartTail, closing, next, outer,
      houterRest, hordered⟩
  exact ⟨{
    rotation := S
    dual_eulerPlanar := hS
    selected_facial :=
      isFacialCycle_addNodeGraphPathCycleAtNew S p hp hst hselected
    outerFace := outerFace
    lift := lift
    lift_eq := hlift
    lift_tail := hliftTail
    lift_head := hliftHead
    toStart := toStart
    outer_first_tail := houterFirst
    toStart_tail := htoStartTail
    closing := closing
    next := next
    outer := outer
    outer_rest := houterRest
    ordered_darts := hordered
  }⟩

/-- Ordered graph-indexed `plane_add_node`: initialize at `x`, add all
remaining selected neighbours in face order, and retain the suffix beginning
at the final selected old dart followed by the incoming initialization dart. -/
theorem exists_addNodeGraph_orderedBoundary
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x y : V) (ys : List V)
    (R : RotationSystem G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge G) (qs residual : List (OrientedEdge G))
    (hselect : OrderedSelections (q :: qs) (B.first :: B.rest) residual)
    (htails : List.Forall₂ (fun d z => d.tail = z)
      (q :: qs) (y :: ys))
    (hys : (y :: ys).Nodup)
    (hnotx : forall z, z ∈ y :: ys -> z ≠ x)
    (hx : B.first.tail = x) :
    letI : DecidableRel
        (addNodeGraph G (insertList (y :: ys) ({x} : Set V))).Adj :=
      Classical.decRel _
    Exists fun S : RotationSystem
        (addNodeGraph G (insertList (y :: ys) ({x} : Set V))) =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun C : FaceBoundary S.toHypermap =>
          C.first.tail = none ∧
            Exists fun lift : OrientedEdge G ->
                OrientedEdge
                  (addNodeGraph G (insertList (y :: ys) ({x} : Set V))) =>
              (forall d, (lift d).tail = some d.tail) ∧
                Exists fun incoming : OrientedEdge
                    (addNodeGraph G (insertList (y :: ys) ({x} : Set V))) =>
                  incoming.tail = some x ∧
                    C.rest = residual.map lift ++ [incoming] := by
  classical
  let H1 := addNodeGraph G ({x} : Set V)
  letI : DecidableRel H1.Adj := Classical.decRel _
  rcases exists_addNodeGraph_singletonBoundary x R hR B hx with
    ⟨S1, hS1, C1, hC1first, lift1, hlift1Tail, _hlift1Head, incoming1,
      hincoming1Tail, hC1rest⟩
  have hselectMap0 :
      OrderedSelections ((q :: qs).map lift1)
        ((B.first :: B.rest).map lift1) (residual.map lift1) :=
    hselect.map lift1
  have hselectMap :
      OrderedSelections ((q :: qs).map lift1) C1.rest
        (residual.map lift1 ++ [incoming1]) := by
    rw [hC1rest]
    exact hselectMap0.appendSuffix [incoming1]
  have htailsMap :
      List.Forall₂ (fun d z => d.tail = some z)
        ((q :: qs).map lift1) (y :: ys) :=
    Internal.forall2_map_left_tail lift1
      (fun (d : OrientedEdge G) (z : V) hdz => by
        rw [hlift1Tail d, hdz]) htails
  have hdisjoint : forall z, z ∈ y :: ys -> z ∉ ({x} : Set V) := by
    intro z hz
    simpa using hnotx z hz
  rcases exists_addNodeGraph_orderedRetained ({x} : Set V) y ys S1 hS1 C1
      (lift1 q) (qs.map lift1) (residual.map lift1 ++ [incoming1])
      hselectMap htailsMap hys hdisjoint hC1first with
    ⟨S, hS, C, hCfirst, lift2, hlift2Tail, hCrest⟩
  let lift : OrientedEdge G ->
      OrientedEdge (addNodeGraph G (insertList (y :: ys) ({x} : Set V))) :=
    fun d => lift2 (lift1 d)
  let incoming :
      OrientedEdge (addNodeGraph G (insertList (y :: ys) ({x} : Set V))) :=
    lift2 incoming1
  refine ⟨S, hS, C, hCfirst, lift, ?_, incoming, ?_, ?_⟩
  · intro d
    calc
      (lift d).tail = (lift1 d).tail := hlift2Tail _
      _ = some d.tail := hlift1Tail _
  · calc
      incoming.tail = incoming1.tail := hlift2Tail _
      _ = some x := hincoming1Tail
  · rw [hCrest, List.map_append]
    change
      (residual.map lift1).map lift2 ++ [incoming] =
        residual.map lift ++ [incoming]
    congr 1
    have hmap : forall l : List (OrientedEdge G),
        (l.map lift1).map lift2 = l.map lift := by
      intro l
      induction l with
      | nil => rfl
      | cons d ds ih =>
          change lift d :: (ds.map lift1).map lift2 = lift d :: ds.map lift
          exact congrArg (List.cons (lift d)) ih
    exact hmap residual

/-- Coq `plane_add_node` with its retained-face conclusion.  If the marked
vertices all lie on one facial cycle and the interior of the final `y`--`x`
segment is unmarked, adding a new vertex adjacent to all marked vertices
preserves that complete segment on one face. -/
theorem exists_addNodeGraph_preserving_clean_gap
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : Set V) {x y : V}
    (R : RotationSystem G)
    (hR : R.toHypermap.dual.EulerPlanar)
    (c : G.Walk x x) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    (before : G.Walk x y) (gap : G.Walk y x)
    (hcycle : c = before.append gap)
    (hgap : gap.IsPath) (hxy : x ≠ y)
    (hxA : x ∈ A) (hyA : y ∈ A)
    (hcover : forall z, z ∈ A -> z ∈ c.support)
    (hclean : forall z, z ∈ Walk.InternalVertices gap -> z ∉ A) :
    letI : DecidableRel (addNodeGraph G A).Adj := Classical.decRel _
    Exists fun S : RotationSystem (addNodeGraph G A) =>
      S.toHypermap.dual.EulerPlanar ∧
        Exists fun C : FaceBoundary S.toHypermap =>
          C.first.tail = none ∧
            ((C.first :: C.rest).map OrientedEdge.tail).Nodup ∧
              forall z, z ∈ gap.support ->
                Exists fun d : OrientedEdge (addNodeGraph G A) =>
                  d ∈ C.first :: C.rest ∧ d.tail = some z := by
  classical
  let E : OrientedEdge G ≃ G.Dart := orientedEdgeDartEquiv (G := G)
  let B : FaceBoundary R.toHypermap :=
    orderedFacialCycleBoundary R c hc hfacial
  let source : List (OrientedEdge G) := B.first :: B.rest
  have hgapNotNil : ¬ gap.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := gap) hxy.symm
  have hgapDartsNe : gap.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hgapNotNil
  let gapDarts : List (OrientedEdge G) := gap.darts.map E.symm
  have hgapDartsMappedNe : gapDarts ≠ [] := by
    simp [gapDarts, hgapDartsNe]
  let q : OrientedEdge G := gapDarts.head hgapDartsMappedNe
  let suffix : List (OrientedEdge G) := gapDarts.tail
  have hgapDartsSplit : gapDarts = q :: suffix := by
    exact (List.cons_head_tail hgapDartsMappedNe).symm
  have hqTail : q.tail = y := by
    change (gapDarts.head hgapDartsMappedNe).tail = y
    rw [show gapDarts.head hgapDartsMappedNe =
        E.symm (gap.darts.head hgapDartsNe) by
      simp [gapDarts]]
    change (gap.darts.head hgapDartsNe).fst = y
    rw [gap.head_darts_eq_firstDart hgapDartsNe]
    simp
  let pre : List (OrientedEdge G) := before.darts.map E.symm
  have hsource : source = pre ++ q :: suffix := by
    calc
      source = c.darts.map E.symm :=
        orderedFacialCycleBoundary_darts R c hc hfacial
      _ = (before.append gap).darts.map E.symm := by rw [← hcycle]
      _ = pre ++ gapDarts := by simp [pre, gapDarts]
      _ = pre ++ q :: suffix := by rw [hgapDartsSplit]
  let p : OrientedEdge G -> Bool :=
    fun d => decide (d.tail ∈ A ∧ d.tail ≠ x)
  have hpq : p q = true := by
    simp [p, hqTail, hyA, hxy.symm]
  have hpSuffix : forall d, d ∈ suffix -> p d = false := by
    intro d hd
    have hdMap : d ∈ gap.darts.tail.map E.symm := by
      simpa [suffix, gapDarts] using hd
    rcases List.mem_map.mp hdMap with ⟨e, he, rfl⟩
    have heInternal : e.fst ∈ Walk.InternalVertices gap :=
      Walk.IsPath.dart_fst_mem_internalVertices_of_mem_tail_darts hgap he
    have heNotA : e.fst ∉ A := hclean e.fst heInternal
    change decide (e.fst ∈ A ∧ e.fst ≠ x) = false
    simp [heNotA]
  rcases exists_orderedSelections_filter_with_final p pre q suffix hpq hpSuffix with
    ⟨first, rest, hfilter, hselect⟩
  have hfilterSource : source.filter p = first :: rest := by
    rw [hsource]
    exact hfilter
  have hselectSource :
      OrderedSelections (first :: rest) source (q :: suffix) := by
    rw [hsource]
    exact hselect
  let selected : List (OrientedEdge G) := source.filter p
  let targets : List V := selected.map OrientedEdge.tail
  have hselected : selected = first :: rest := hfilterSource
  have htargets : targets = first.tail :: rest.map OrientedEdge.tail := by
    simp [targets, hselected]
  have hsourceTailsNodup :
      (source.map OrientedEdge.tail).Nodup := by
    apply B.nodup.map_on
    intro a ha b hb hab
    apply cycleForwardDart_eq_of_tail_eq hc
    · rw [cycleForwardDart_iff_mem_darts]
      have ha' : a ∈ c.darts.map E.symm := by
        rw [← orderedFacialCycleBoundary_darts R c hc hfacial]
        exact ha
      rcases List.mem_map.mp ha' with ⟨d, hd, hda⟩
      have hEa : E a = d := by
        calc
          E a = E (E.symm d) := congrArg E hda.symm
          _ = d := E.apply_symm_apply d
      change E a ∈ c.darts
      rw [hEa]
      exact hd
    · rw [cycleForwardDart_iff_mem_darts]
      have hb' : b ∈ c.darts.map E.symm := by
        rw [← orderedFacialCycleBoundary_darts R c hc hfacial]
        exact hb
      rcases List.mem_map.mp hb' with ⟨d, hd, hdb⟩
      have hEb : E b = d := by
        calc
          E b = E (E.symm d) := congrArg E hdb.symm
          _ = d := E.apply_symm_apply d
      change E b ∈ c.darts
      rw [hEb]
      exact hd
    · exact hab
  have htargetsNodup : targets.Nodup := by
    exact List.Nodup.sublist
      (List.Sublist.map OrientedEdge.tail (List.filter_sublist (p := p)))
      hsourceTailsNodup
  have htargetsNotX : forall z, z ∈ targets -> z ≠ x := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨d, hdSelected, rfl⟩
    have hdFilter := (List.mem_filter.mp hdSelected).2
    have hdPair : d.tail ∈ A ∧ d.tail ≠ x := by
      simpa [p] using hdFilter
    exact hdPair.2
  have hboundaryCover : forall z, z ∈ c.support ->
      Exists fun d : OrientedEdge G => d ∈ source ∧ d.tail = z := by
    intro z hz
    rcases exists_cycleForwardDart_of_mem_support hc hz with ⟨d, hd, htail⟩
    refine ⟨d, ?_, htail⟩
    change d ∈ B.first :: B.rest
    rw [orderedFacialCycleBoundary_darts R c hc hfacial]
    rw [cycleForwardDart_iff_mem_darts] at hd
    exact List.mem_map.mpr ⟨E d, hd, E.symm_apply_apply d⟩
  have hset : insertList targets ({x} : Set V) = A := by
    ext z
    rw [mem_insertList_iff]
    constructor
    · rintro (hzx | hzTargets)
      · have hzx' : z = x := by simpa using hzx
        simpa [hzx'] using hxA
      · rcases List.mem_map.mp hzTargets with ⟨d, hdSelected, hdz⟩
        have hdFilter := (List.mem_filter.mp hdSelected).2
        have hdPair : d.tail ∈ A ∧ d.tail ≠ x := by
          simpa [p] using hdFilter
        simpa [hdz] using hdPair.1
    · intro hzA
      by_cases hzx : z = x
      · exact Or.inl (by simp [hzx])
      · right
        rcases hboundaryCover z (hcover z hzA) with ⟨d, hdSource, hdtail⟩
        rw [List.mem_map]
        refine ⟨d, ?_, hdtail⟩
        rw [List.mem_filter]
        exact ⟨hdSource, by simp [p, hdtail, hzA, hzx]⟩
  have hforalls :
      List.Forall₂ (fun d z => d.tail = z) selected targets :=
    Internal.forall2_tail_map selected
  rw [hselected] at hforalls
  rw [htargets] at htargetsNodup htargetsNotX hset hforalls
  have hxFirst : B.first.tail = x := by
    change (cycleFirstDart c hc).tail = x
    exact cycleFirstDart_tail c hc
  rw [← hset]
  rcases exists_addNodeGraph_orderedBoundary x first.tail
      (rest.map OrientedEdge.tail) R hR B first rest (q :: suffix)
      hselectSource hforalls htargetsNodup htargetsNotX hxFirst with
    ⟨S, hS, C, hCfirst, lift, hliftTail, incoming,
      hincomingTail, hCrest⟩
  have hgapTailSequence :
      (q :: suffix).map OrientedEdge.tail ++ [x] = gap.support := by
    rw [← hgapDartsSplit]
    simpa [gapDarts, E, List.map_map, orientedEdgeDartEquiv] using
      gap.map_fst_darts_append
  have hgapTailSequenceSome :
      (q :: suffix).map (fun d => some d.tail) ++ [some x] =
        gap.support.map some := by
    simpa [List.map_append, List.map_map] using
      congrArg (List.map some) hgapTailSequence
  have hmapLiftTail : forall ds : List (OrientedEdge G),
      (ds.map lift).map OrientedEdge.tail =
        ds.map (fun d => some d.tail) := by
    intro ds
    induction ds with
    | nil => rfl
    | cons d ds ih => simp [hliftTail, ih]
  have hCtailsNodup :
      ((C.first :: C.rest).map OrientedEdge.tail).Nodup := by
    change (C.first.tail :: C.rest.map OrientedEdge.tail).Nodup
    rw [hCfirst, hCrest, List.map_append, hmapLiftTail]
    change
      (none :: ((q :: suffix).map (fun d => some d.tail) ++
        [incoming.tail])).Nodup
    rw [hincomingTail]
    rw [hgapTailSequenceSome]
    simp only [List.nodup_cons]
    refine ⟨by simp, ?_⟩
    exact hgap.support_nodup.map (fun _ _ h => Option.some.inj h)
  refine ⟨S, hS, C, hCfirst, hCtailsNodup, ?_⟩
  intro z hzGap
  by_cases hzy : z = y
  · subst z
    refine ⟨lift q, ?_, by simp [hliftTail, hqTail]⟩
    right
    rw [hCrest]
    exact List.mem_append_left _ (List.mem_cons_self)
  · by_cases hzx : z = x
    · subst z
      refine ⟨incoming, ?_, hincomingTail⟩
      right
      rw [hCrest]
      exact List.mem_append_right _ (List.mem_singleton_self incoming)
    · have hzInternal : z ∈ Walk.InternalVertices gap :=
        ⟨hzGap, hzy, hzx⟩
      rcases Walk.IsPath.exists_mem_tail_darts_fst_eq_of_mem_internalVertices
          hgap hzInternal with ⟨d, hdTail, hdz⟩
      let old : OrientedEdge G := E.symm d
      have holdSuffix : old ∈ suffix := by
        simpa [old, suffix, gapDarts] using
          (List.mem_map.mpr ⟨d, hdTail, rfl⟩ :
            E.symm d ∈ gap.darts.tail.map E.symm)
      refine ⟨lift old, ?_, ?_⟩
      · right
        rw [hCrest]
        exact List.mem_append_left _
          (List.mem_map_of_mem (by simp [holdSuffix]))
      · rw [hliftTail]
        change some d.fst = some z
        rw [hdz]

/-- Set-facing form of Coq `plane_add_node_simple`, aligned at a requested
first boundary vertex.  Every requested neighbour must occur on the face and
the boundary tails must be vertex-simple. -/
theorem exists_addNodeGraph_simple
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : Set V) (x : V) (hxA : x ∈ A)
    (R : RotationSystem G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (hxfirst : B.first.tail = x)
    (hcover : forall z, z ∈ A ->
      Exists fun d : OrientedEdge G => d ∈ B.first :: B.rest ∧ d.tail = z)
    (htailsNodup : ((B.first :: B.rest).map OrientedEdge.tail).Nodup) :
    letI : DecidableRel (addNodeGraph G A).Adj := Classical.decRel _
    Exists fun S : RotationSystem (addNodeGraph G A) =>
      (S.toHypermap).dual.EulerPlanar := by
  classical
  by_cases hother : Exists fun z : V => z ∈ A ∧ z ≠ x
  · let p : OrientedEdge G -> Bool := fun d => decide (d.tail ∈ A ∧ d.tail ≠ x)
    let source := B.first :: B.rest
    have hfilterNe : source.filter p ≠ [] := by
      rcases hother with ⟨z, hzA, hzx⟩
      rcases hcover z hzA with ⟨d, hdSource, hdtail⟩
      have hpd : p d = true := by simp [p, hdtail, hzA, hzx]
      have hdFilter : d ∈ source.filter p := by
        rw [List.mem_filter]
        exact ⟨hdSource, hpd⟩
      intro hnil
      simp [hnil] at hdFilter
    rcases Internal.exists_orderedSelections_filter p source hfilterNe with
      ⟨q, qs, residual, hfilter, hselect⟩
    let selected := source.filter p
    let targets := selected.map OrientedEdge.tail
    have hselected : selected = q :: qs := hfilter
    have htargets : targets = q.tail :: qs.map OrientedEdge.tail := by
      simp [targets, hselected]
    have htargetsNodup : targets.Nodup := by
      exact List.Nodup.sublist
        (List.Sublist.map OrientedEdge.tail (List.filter_sublist (p := p)))
        htailsNodup
    have htargetsNotX : forall z, z ∈ targets -> z ≠ x := by
      intro z hz
      rcases List.mem_map.mp hz with ⟨d, hdSelected, rfl⟩
      have hdFilter := (List.mem_filter.mp hdSelected).2
      have hdPair : d.tail ∈ A ∧ d.tail ≠ x := by
        simpa [p] using hdFilter
      exact hdPair.2
    have hset : insertList targets ({x} : Set V) = A := by
      ext z
      rw [mem_insertList_iff]
      constructor
      · rintro (hzx | hzTargets)
        · have hzx' : z = x := by simpa using hzx
          simpa [hzx'] using hxA
        · rcases List.mem_map.mp hzTargets with ⟨d, hdSelected, hdz⟩
          have hdFilter := (List.mem_filter.mp hdSelected).2
          have hdPair : d.tail ∈ A ∧ d.tail ≠ x := by
            simpa [p] using hdFilter
          have hdA : d.tail ∈ A := hdPair.1
          simpa [hdz] using hdA
      · intro hzA
        by_cases hzx : z = x
        · exact Or.inl (by simp [hzx])
        · right
          rcases hcover z hzA with ⟨d, hdSource, hdtail⟩
          rw [List.mem_map]
          refine ⟨d, ?_, hdtail⟩
          rw [List.mem_filter]
          exact ⟨hdSource, by simp [p, hdtail, hzA, hzx]⟩
    have hforalls :
        List.Forall₂ (fun d z => d.tail = z) selected targets := by
      exact Internal.forall2_tail_map selected
    rw [hselected] at hforalls
    rw [htargets] at htargetsNodup htargetsNotX hset hforalls
    rw [← hset]
    rcases exists_addNodeGraph_orderedBoundary x q.tail
        (qs.map OrientedEdge.tail) R hR B q qs residual hselect hforalls
        htargetsNodup htargetsNotX hxfirst with
      ⟨S, hS, _C, _hCfirst, _lift, _hlift, _incoming,
        _hincomingTail, _hCrest⟩
    exact ⟨S, hS⟩
  · have hAeq : A = ({x} : Set V) := by
      ext z
      constructor
      · intro hzA
        by_contra hzx
        exact hother ⟨z, hzA, hzx⟩
      · intro hzx
        simpa using hzx ▸ hxA
    rw [hAeq]
    rcases exists_addNodeGraph_singletonBoundary x R hR B hxfirst with
      ⟨S, hS, _C, _hCfirst, _lift, _hliftTail, _hliftHead, _incoming,
        _hincomingTail, _hCrest⟩
    exact ⟨S, hS⟩

/-- The one-neighbor `add_node` base case is the checked leaf extension. -/
theorem HasEulerRotationSystem.addNode_singleton
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : V)
    (hG : HasEulerRotationSystem G) :
    letI : DecidableRel (addNodeGraph G ({x} : Set V)).Adj :=
      Classical.decRel _
    HasEulerRotationSystem (addNodeGraph G ({x} : Set V)) := by
  classical
  let H := addNodeGraph G ({x} : Set V)
  letI : DecidableRel H.Adj := Classical.decRel _
  have hOld :
      HasEulerRotationSystem (H.induce {z : Option V | z ≠ none}) :=
    HasEulerRotationSystem.of_iso (addNodeGraphOldIso G ({x} : Set V)) hG
  have hx : H.Adj none (some x) := by
    simp [H, addNodeGraph]
  have hdegree : H.degree none <= 1 := by
    exact addNodeGraph_singleton_new_degree_le_one (G := G) x
  exact HasEulerRotationSystem.of_deleted_leaf_degree_le_one
    (G := H) (v := none) (w := some x) hx hdegree hOld


end RotationSystemFan

end FourColor

end Schematic.Math.GraphTheory
