import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.OrderedRetainedFaces

/-! Constructive splitting of facial paths and their complementary faces. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemFan

/-- The prefix face produced by a two-spoke split is the explicit cycle that
closes the selected old path through the fresh vertex. -/
theorem FaceBoundary.isFacialCycle_addNodeGraphPathCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {s t : V} (hst : s ≠ t)
    (p : G.Walk s t) (hp : p.IsPath)
    [DecidableRel (addNodeGraph G (insert t ({s} : Set V))).Adj]
    {R : RotationSystem (addNodeGraph G (insert t ({s} : Set V)))}
    (B : FaceBoundary R.toHypermap)
    (fromS : OrientedEdge (addNodeGraph G (insert t ({s} : Set V))))
    (hfirstTail : B.first.tail = some t)
    (hfirstHead : B.first.head = none)
    (hfromSTail : fromS.tail = none)
    (hfromSHead : fromS.head = some s)
    (hrest : B.rest = fromS ::
      (p.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
        (addNodeGraphSomeOrientedEdge G (insert t ({s} : Set V)))) :
    RotationSystemGluing.IsFacialCycle R (addNodeGraphPathCycle p)
      (addNodeGraphPathCycle_isCycle hst p hp) := by
  classical
  let H := addNodeGraph G (insert t ({s} : Set V))
  let c : H.Walk (some t) (some t) := addNodeGraphPathCycle p
  let hc : c.IsCycle := addNodeGraphPathCycle_isCycle hst p hp
  have hfirst : B.first = cycleFirstDart c hc := by
    apply Subtype.ext
    exact Prod.ext hfirstTail (by
      simpa [c, addNodeGraphPathCycle] using hfirstHead)
  apply B.isFacialCycle_of_eq_cycleDarts c hc hfirst
  rw [hrest]
  have hfromS :
      fromS =
        (orientedEdgeDartEquiv (G := H)).symm
          ⟨(none, some s), by simp [H]⟩ := by
    apply Subtype.ext
    exact Prod.ext hfromSTail hfromSHead
  rw [hfromS]
  rw [hfirst]
  simp only [c, H, addNodeGraphPathCycle, SimpleGraph.Walk.darts_cons,
    List.map_cons]
  congr 2
  let f := addNodeGraphSomeHom G (insert t ({s} : Set V))
  let E₀ := orientedEdgeDartEquiv (G := G)
  let E₁ := orientedEdgeDartEquiv
    (G := addNodeGraph G (insert t ({s} : Set V)))
  calc
    List.map (addNodeGraphSomeOrientedEdge G (insert t ({s} : Set V)))
          (List.map E₀.symm p.darts) =
        List.map E₁.symm (List.map f.mapDart p.darts) := by
          simp [addNodeGraphSomeOrientedEdge, f, E₀, E₁, List.map_map]
      _ = List.map E₁.symm (p.map f).darts := by
          exact congrArg (List.map E₁.symm)
            (SimpleGraph.Walk.darts_map f p).symm

/-- A face boundary consisting of the fresh outgoing spoke, a lifted old path,
and the fresh incoming spoke is the corresponding order-independent fan
cycle. -/
theorem FaceBoundary.isFacialCycle_addNodeGraphPathCycleAtNewIn
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : Set V} {s t : V}
    (hs : s ∈ A) (ht : t ∈ A) (hst : s ≠ t)
    (p : G.Walk s t) (hp : p.IsPath)
    [DecidableRel (addNodeGraph G A).Adj]
    {R : RotationSystem (addNodeGraph G A)}
    (B : FaceBoundary R.toHypermap)
    (toNew : OrientedEdge (addNodeGraph G A))
    (hfirstTail : B.first.tail = none)
    (hfirstHead : B.first.head = some s)
    (htoNewTail : toNew.tail = some t)
    (htoNewHead : toNew.head = none)
    (hrest : B.rest =
      (p.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
          (addNodeGraphSomeOrientedEdge G A) ++ [toNew]) :
    RotationSystemGluing.IsFacialCycle R
      (addNodeGraphPathCycleAtNewIn G A hs ht p)
      (addNodeGraphPathCycleAtNewIn_isCycle A hs ht hst p hp) := by
  classical
  let H := addNodeGraph G A
  let c : H.Walk none none := addNodeGraphPathCycleAtNewIn G A hs ht p
  let hc : c.IsCycle :=
    addNodeGraphPathCycleAtNewIn_isCycle A hs ht hst p hp
  have hcycleFirstHead : (cycleFirstDart c hc).head = some s := by
    change c.snd = some s
    simp [c, addNodeGraphPathCycleAtNewIn]
  have hfirst : B.first = cycleFirstDart c hc := by
    apply Subtype.ext
    exact Prod.ext
      (hfirstTail.trans (cycleFirstDart_tail c hc).symm)
      (hfirstHead.trans hcycleFirstHead.symm)
  apply B.isFacialCycle_of_eq_cycleDarts c hc hfirst
  rw [hrest, hfirst]
  have htoNew :
      toNew =
        (orientedEdgeDartEquiv (G := H)).symm
          ⟨(some t, none), by simp [H, addNodeGraph, ht]⟩ := by
    apply Subtype.ext
    exact Prod.ext htoNewTail htoNewHead
  rw [htoNew]
  let f := addNodeGraphSomeHom G A
  let E₀ := orientedEdgeDartEquiv (G := G)
  let E₁ := orientedEdgeDartEquiv (G := H)
  have hmiddle :
      List.map (addNodeGraphSomeOrientedEdge G A)
          (List.map E₀.symm p.darts) =
        List.map E₁.symm (p.map f).darts := by
    calc
      List.map (addNodeGraphSomeOrientedEdge G A)
            (List.map E₀.symm p.darts) =
          List.map E₁.symm (List.map f.mapDart p.darts) := by
            simp [addNodeGraphSomeOrientedEdge, f, E₀, E₁, List.map_map]
      _ = List.map E₁.symm (p.map f).darts := by
            exact congrArg (List.map E₁.symm)
              (SimpleGraph.Walk.darts_map f p).symm
  rw [show c.darts =
      ⟨(none, some s), by simp [addNodeGraph, hs]⟩ ::
        (p.map f).darts ++
          [⟨(some t, none), by simp [addNodeGraph, ht]⟩] by
    simp [c, H, f, addNodeGraphPathCycleAtNewIn_darts]]
  simp only [List.map_cons, List.map_append]
  have hfirstCanonical :
      cycleFirstDart c hc =
        E₁.symm ⟨(none, some s), by simp [H, addNodeGraph, hs]⟩ := by
    apply Subtype.ext
    exact Prod.ext (cycleFirstDart_tail c hc) hcycleFirstHead
  rw [hfirstCanonical, hmiddle]
  simp [E₁]
  rfl

/-- Split a marked facial cycle along an explicitly displayed nontrivial
path.  The ordered cycle darts are assumed to consist of one closing dart,
the selected path darts, and then the complementary outer-arc darts.  The
fresh vertex closes the selected path into the facial cycle used by
`cycleSum`; the returned `outerFace` is the other face and retains an exact
lifted-dart description for the later vertex-deletion merge. -/
theorem exists_addNodeGraph_facialPathSplit_of_orderedDarts
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    {r s t : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    (p : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t)
    (closing next : OrientedEdge G)
    (outer : List (OrientedEdge G))
    (hordered :
      c.darts.map (orientedEdgeDartEquiv (G := G)).symm =
        closing ::
          (p.darts.map (orientedEdgeDartEquiv (G := G)).symm ++
            next :: outer)) :
    letI : DecidableRel
        (addNodeGraph G (insert t ({s} : Set V))).Adj := Classical.decRel _
    Exists fun S : RotationSystem
        (addNodeGraph G (insert t ({s} : Set V))) =>
      (S.toHypermap).dual.EulerPlanar ∧
        RotationSystemGluing.IsFacialCycle S
          (addNodeGraphPathCycle p)
          (addNodeGraphPathCycle_isCycle hst p hp) ∧
          Exists fun outerFace : FaceBoundary S.toHypermap =>
            Exists fun lift : OrientedEdge G ->
                OrientedEdge (addNodeGraph G (insert t ({s} : Set V))) =>
              (forall d, lift d =
                addNodeGraphSomeOrientedEdge G
                  (insert t ({s} : Set V)) d) ∧
              (forall d, (lift d).tail = some d.tail) ∧
              (forall d, (lift d).head = some d.head) ∧
              Exists fun toS : OrientedEdge
                  (addNodeGraph G (insert t ({s} : Set V))) =>
                outerFace.first.tail = none ∧
                  toS.tail = some s ∧
                  outerFace.rest =
                    lift next :: (outer ++ [closing]).map lift ++ [toS] := by
  classical
  let E := orientedEdgeDartEquiv (G := G)
  let pathDarts : List (OrientedEdge G) := p.darts.map E.symm
  have hpNotNil : ¬ p.Nil := p.not_nil_of_ne hst
  have hpDartsNe : p.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hpNotNil
  have hpathDartsNe : pathDarts ≠ [] := by
    simp [pathDarts, hpDartsNe]
  rcases List.exists_cons_of_ne_nil hpathDartsNe with
    ⟨pfirst, prest, hpathDarts⟩
  let B0 : FaceBoundary R.toHypermap :=
    orderedFacialCycleBoundary R c hc hfacial
  have hfull :
      B0.first :: B0.rest =
        closing :: (pathDarts ++ next :: outer) := by
    rw [orderedFacialCycleBoundary_darts R c hc hfacial,
      hordered]
  have hclosing : B0.first = closing := by
    exact List.cons.inj hfull |>.1
  have hrest0 : B0.rest = pathDarts ++ next :: outer := by
    exact List.cons.inj hfull |>.2
  have hrest0' : B0.rest = pfirst :: (prest ++ next :: outer) := by
    simpa [hpathDarts] using hrest0
  let B : FaceBoundary R.toHypermap :=
    B0.rotateFromRest pfirst [] (prest ++ next :: outer) hrest0'
  have hBfirst : B.first = pfirst := by
    simp [B]
  have hBrest : B.rest = prest ++ next :: (outer ++ [closing]) := by
    simp only [B, FaceBoundary.rotateFromRest_rest, hclosing]
    simpa only [List.cons_append] using
      List.append_assoc prest (next :: outer) [closing]
  have hpfirstTail : pfirst.tail = s := by
    have hdartsMap : p.darts.map E.symm = pfirst :: prest := by
      simpa [pathDarts] using hpathDarts
    have hdartsCons : p.darts = E pfirst :: prest.map E := by
      have hmap := congrArg (List.map E) hdartsMap
      simpa [List.map_map] using hmap
    have hfirstEq : p.firstDart hpNotNil = E pfirst := by
      have hheadOption := congrArg List.head? hdartsCons
      have hleft : p.darts.head? = some (p.firstDart hpNotNil) := by
        rw [List.head?_eq_some_head hpDartsNe,
          p.head_darts_eq_firstDart hpDartsNe]
      have hright : p.darts.head? = some (E pfirst) := by
        simpa using hheadOption
      exact Option.some.inj (hleft.symm.trans hright)
    have hprod := congrArg SimpleGraph.Dart.toProd hfirstEq
    have htail := congrArg Prod.fst hprod
    simpa [E, orientedEdgeDartEquiv] using htail.symm
  have hnextTail : next.tail = t := by
    apply B.next_tail_eq_walk_to R next prest (outer ++ [closing])
      hBrest p hpNotNil
    simpa [hBfirst, pathDarts] using hpathDarts.symm
  letI : DecidableRel
      (addNodeGraph G (insert t ({s} : Set V))).Adj := Classical.decRel _
  rcases exists_addNodeGraph_pairSplitBoundaries hst R hR B next prest
      (outer ++ [closing]) hBrest
      (by simpa [hBfirst] using hpfirstTail) hnextTail with
    ⟨S, hS, outerFace, selectedFace, houterFirst,
      hselectedFirst, hselectedHead, lift, hlift, hliftTail, hliftHead,
      toS, htoSTail, fromS, hfromSTail, hfromSHead,
      houterRest, hselectedRest⟩
  have hselectedFacial :
      RotationSystemGluing.IsFacialCycle S
        (addNodeGraphPathCycle p)
        (addNodeGraphPathCycle_isCycle hst p hp) := by
    apply selectedFace.isFacialCycle_addNodeGraphPathCycle hst p hp fromS
      hselectedFirst hselectedHead hfromSTail hfromSHead
    rw [hselectedRest]
    congr 1
    calc
      lift B.first :: prest.map lift = pathDarts.map lift := by
        simp [hBfirst, hpathDarts]
      _ = pathDarts.map
          (addNodeGraphSomeOrientedEdge G
            (insert t ({s} : Set V))) := by
        apply List.map_congr_left
        intro d hd
        exact hlift d
      _ = (p.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
          (addNodeGraphSomeOrientedEdge G
            (insert t ({s} : Set V))) := by
        rfl
  exact ⟨S, hS, hselectedFacial, outerFace, lift,
    hlift, hliftTail, hliftHead, toS, houterFirst, htoSTail, houterRest⟩

/-- Canonical specialization of
`exists_addNodeGraph_facialPathSplit_of_orderedDarts`: the selected path is
the first `k` darts after the boundary cycle's initial closing dart.  The
strict inequality leaves at least one complementary outer-arc dart, which is
the `next` dart used to split the marked face. -/
theorem exists_addNodeGraph_facialPathSplit_after_first
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    {r s t : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    (p : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t)
    (k : Nat) (hk : k + 1 < c.length)
    (hpathDarts :
      p.darts = ((c.drop 1).take k).darts) :
    letI : DecidableRel
        (addNodeGraph G (insert t ({s} : Set V))).Adj := Classical.decRel _
    Exists fun S : RotationSystem
        (addNodeGraph G (insert t ({s} : Set V))) =>
      (S.toHypermap).dual.EulerPlanar ∧
        RotationSystemGluing.IsFacialCycle S
          (addNodeGraphPathCycle p)
          (addNodeGraphPathCycle_isCycle hst p hp) ∧
          Exists fun outerFace : FaceBoundary S.toHypermap =>
            Exists fun lift : OrientedEdge G ->
                OrientedEdge (addNodeGraph G (insert t ({s} : Set V))) =>
              (forall d, lift d =
                addNodeGraphSomeOrientedEdge G
                  (insert t ({s} : Set V)) d) ∧
              (forall d, (lift d).tail = some d.tail) ∧
              (forall d, (lift d).head = some d.head) ∧
              Exists fun toS : OrientedEdge
                  (addNodeGraph G (insert t ({s} : Set V))) =>
                outerFace.first.tail = none ∧
                  toS.tail = some s ∧
                  Exists fun closing : OrientedEdge G =>
                    Exists fun next : OrientedEdge G =>
                      Exists fun outer : List (OrientedEdge G) =>
                        outerFace.rest =
                          lift next ::
                            (outer ++ [closing]).map lift ++ [toS] ∧
                        c.darts.map
                            (orientedEdgeDartEquiv (G := G)).symm =
                          closing ::
                            (p.darts.map
                                (orientedEdgeDartEquiv (G := G)).symm ++
                              next :: outer) := by
  classical
  let E := orientedEdgeDartEquiv (G := G)
  let ds : List (OrientedEdge G) := c.darts.map E.symm
  have hdsNe : ds ≠ [] := by
    have hcDartsNe : c.darts ≠ [] :=
      SimpleGraph.Walk.darts_eq_nil.not.mpr hc.not_nil
    simp [ds, hcDartsNe]
  rcases List.exists_cons_of_ne_nil hdsNe with ⟨closing, rest, hds⟩
  have hdsLength : ds.length = c.length := by
    simp [ds]
  have hrestLength : rest.length + 1 = c.length := by
    rw [hds] at hdsLength
    simpa using hdsLength
  have hkRest : k < rest.length := by omega
  have hdropNe : rest.drop k ≠ [] := by
    intro hnil
    have hlen : (rest.drop k).length = 0 := by simp [hnil]
    rw [List.length_drop] at hlen
    omega
  rcases List.exists_cons_of_ne_nil hdropNe with ⟨next, outer, hdrop⟩
  have hpathMapped : p.darts.map E.symm = rest.take k := by
    calc
      p.darts.map E.symm =
          (((c.drop 1).take k).darts).map E.symm := by rw [hpathDarts]
      _ = ((c.darts.drop 1).take k).map E.symm := by
        rw [SimpleGraph.Walk.darts_take, SimpleGraph.Walk.darts_drop]
      _ = (ds.drop 1).take k := by
        simp [ds, List.map_take]
      _ = rest.take k := by simp [hds]
  have hordered :
      c.darts.map E.symm =
        closing :: (p.darts.map E.symm ++ next :: outer) := by
    calc
      c.darts.map E.symm = closing :: rest := hds
      _ = closing :: (rest.take k ++ rest.drop k) := by
        rw [List.take_append_drop]
      _ = closing :: (p.darts.map E.symm ++ next :: outer) := by
        rw [hpathMapped, hdrop]
  letI : DecidableRel
      (addNodeGraph G (insert t ({s} : Set V))).Adj := Classical.decRel _
  rcases exists_addNodeGraph_facialPathSplit_of_orderedDarts
      R hR c hc hfacial p hp hst closing next outer hordered with
    ⟨S, hS, hselected, outerFace, lift, hlift, hliftTail, hliftHead,
      toS, houterFirst, htoSTail, houterRest⟩
  exact ⟨S, hS, hselected, outerFace, lift, hlift, hliftTail,
    hliftHead, toS, houterFirst, htoSTail, closing, next, outer,
    houterRest, hordered⟩

/-- Complete constructive output of splitting a facial cycle along a path.
The selected face is based at the fresh vertex, while `outerFace` retains the
exact complementary boundary sequence needed after cycle gluing. -/
structure FacialPathSplitData
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r s t : V}
    (c : G.Walk r r) (p : G.Walk s t)
    (hp : p.IsPath) (hst : s ≠ t)
    [DecidableRel (addNodeGraph G (insert t ({s} : Set V))).Adj] where
  rotation : RotationSystem
    (addNodeGraph G (insert t ({s} : Set V)))
  dual_eulerPlanar : (rotation.toHypermap).dual.EulerPlanar
  selected_facial : RotationSystemGluing.IsFacialCycle rotation
    (addNodeGraphPathCycleAtNew p)
    (addNodeGraphPathCycleAtNew_isCycle hst p hp)
  outerFace : FaceBoundary rotation.toHypermap
  lift : OrientedEdge G ->
    OrientedEdge (addNodeGraph G (insert t ({s} : Set V)))
  lift_eq : forall d, lift d =
    addNodeGraphSomeOrientedEdge G (insert t ({s} : Set V)) d
  lift_tail : forall d, (lift d).tail = some d.tail
  lift_head : forall d, (lift d).head = some d.head
  toStart : OrientedEdge
    (addNodeGraph G (insert t ({s} : Set V)))
  outer_first_tail : outerFace.first.tail = none
  toStart_tail : toStart.tail = some s
  closing : OrientedEdge G
  next : OrientedEdge G
  outer : List (OrientedEdge G)
  outer_rest : outerFace.rest =
    lift next :: (outer ++ [closing]).map lift ++ [toStart]
  ordered_darts :
    c.darts.map (orientedEdgeDartEquiv (G := G)).symm =
      closing ::
        (p.darts.map (orientedEdgeDartEquiv (G := G)).symm ++
          next :: outer)

/-- The complementary old boundary arc encoded by a facial-path split is an
actual simple path from the selected path's terminal vertex back to its
initial vertex.  Its oriented darts are exactly `next :: outer ++ [closing]`,
the sequence retained by `outerFace`. -/
theorem FacialPathSplitData.exists_complementaryPath
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {r s t : V}
    {c : G.Walk r r} {p : G.Walk s t}
    {hp : p.IsPath} {hst : s ≠ t}
    [DecidableRel (addNodeGraph G (insert t ({s} : Set V))).Adj]
    (D : FacialPathSplitData R c p hp hst)
    (hc : c.IsCycle)
    (hsegment :
      p.support = ((c.drop 1).take p.length).support)
    (hproper : p.length + 1 < c.length) :
    Exists fun q : G.Walk t s =>
      q.IsPath ∧
        q.darts = c.darts.drop (p.length + 1) ++ c.darts.take 1 ∧
          q.darts.map (orientedEdgeDartEquiv (G := G)).symm =
            D.next :: D.outer ++ [D.closing] := by
  classical
  let segment := (c.drop 1).take p.length
  have hsRaw : s = c.getVert 1 := by
    have hhead := congrArg List.head? hsegment
    simpa [segment, List.head?_eq_some_head] using hhead
  have hs : c.getVert 1 = s := hsRaw.symm
  have htRaw : t = c.getVert (1 + p.length) := by
    have hlast := congrArg List.getLast? hsegment
    simpa [segment, List.getLast?_eq_some_getLast,
      SimpleGraph.Walk.drop_getVert] using hlast
  have ht : c.getVert (p.length + 1) = t := by
    simpa [Nat.add_comm] using htRaw.symm
  let q₀ : G.Walk (c.getVert (p.length + 1)) (c.getVert 1) :=
    (c.drop (p.length + 1)).append (c.take 1)
  let q : G.Walk t s := q₀.copy ht hs
  have hpLengthPos : 0 < p.length := by
    exact SimpleGraph.Walk.not_nil_iff_lt_length.mp (p.not_nil_of_ne hst)
  have hq₀Path : q₀.IsPath := by
    exact Walk.IsCycle.isPath_drop_succ_append_take_one
      c hc hpLengthPos hproper
  have hqDarts :
      q.darts = c.darts.drop (p.length + 1) ++ c.darts.take 1 := by
    simp [q, q₀, SimpleGraph.Walk.darts_append,
      SimpleGraph.Walk.darts_drop, SimpleGraph.Walk.darts_take]
  refine ⟨q, (SimpleGraph.Walk.isPath_copy q₀ ht hs).mpr hq₀Path,
    hqDarts, ?_⟩
  rw [hqDarts, List.map_append, List.map_drop, List.map_take,
    D.ordered_darts]
  simp [SimpleGraph.Walk.length_darts]

/-- The complementary path returned by `exists_complementaryPath`, closed
through the fresh vertex in the same fan graph, is exactly the retained outer
face of the split rotation. -/
theorem FacialPathSplitData.exists_complementaryFacialPath
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {r s t : V}
    {c : G.Walk r r} {p : G.Walk s t}
    {hp : p.IsPath} {hst : s ≠ t}
    [DecidableRel (addNodeGraph G (insert t ({s} : Set V))).Adj]
    (D : FacialPathSplitData R c p hp hst)
    (hc : c.IsCycle)
    (hsegment :
      p.support = ((c.drop 1).take p.length).support)
    (hproper : p.length + 1 < c.length) :
    Exists fun q : G.Walk t s =>
      Exists fun hq : q.IsPath =>
        q.darts = c.darts.drop (p.length + 1) ++ c.darts.take 1 ∧
          q.darts.map (orientedEdgeDartEquiv (G := G)).symm =
              D.next :: D.outer ++ [D.closing] ∧
            RotationSystemGluing.IsFacialCycle D.rotation
              (addNodeGraphPathCycleAtNewIn G
                (insert t ({s} : Set V)) (by simp) (by simp) q)
              (addNodeGraphPathCycleAtNewIn_isCycle
                (insert t ({s} : Set V)) (by simp) (by simp)
                  hst.symm q hq) := by
  classical
  rcases D.exists_complementaryPath hc hsegment hproper with
    ⟨q, hq, hqRawDarts, hqDarts⟩
  let A : Set V := insert t ({s} : Set V)
  have htA : t ∈ A := by simp [A]
  have hsA : s ∈ A := by simp [A]
  let E := orientedEdgeDartEquiv (G := G)
  have hqNotNil : ¬ q.Nil := q.not_nil_of_ne hst.symm
  have hqDartsNe : q.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hqNotNil
  have hqMappedNe : q.darts.map E.symm ≠ [] := by
    simp [hqDartsNe]
  have hfirstMapped : E.symm (q.firstDart hqNotNil) = D.next := by
    have hhead := congrArg List.head? hqDarts
    have hleft :
        (q.darts.map E.symm).head? =
          some (E.symm (q.firstDart hqNotNil)) := by
      rw [List.head?_eq_some_head hqMappedNe, List.head_map,
        q.head_darts_eq_firstDart hqDartsNe]
    have hright :
        (D.next :: D.outer ++ [D.closing]).head? = some D.next := rfl
    exact Option.some.inj (hleft.symm.trans (hhead.trans hright))
  have hnextTail : D.next.tail = t := by
    rw [← hfirstMapped]
    rfl
  have houterStep :
      D.rotation.toHypermap.face D.outerFace.first = D.lift D.next := by
    have hpath := D.outerFace.path
    rw [D.outer_rest] at hpath
    exact
      ((Hypermap.FacePath.cons D.rotation.toHypermap D.outerFace.first
        (D.lift D.next)
        ((D.outer ++ [D.closing]).map D.lift ++ [D.toStart])).mp hpath).1
  have houterFirstHead : D.outerFace.first.head = some t := by
    calc
      D.outerFace.first.head =
          (D.rotation.toHypermap.face D.outerFace.first).tail :=
        (D.rotation.toHypermap_face_tail D.outerFace.first).symm
      _ = (D.lift D.next).tail := congrArg OrientedEdge.tail houterStep
      _ = some D.next.tail := D.lift_tail D.next
      _ = some t := congrArg some hnextTail
  have hlast :
      (D.outerFace.first :: D.outerFace.rest).getLastD D.outerFace.first =
        D.toStart := by
    let pref : List D.rotation.toHypermap.Dart :=
      D.outerFace.first :: D.lift D.next ::
        (D.outer ++ [D.closing]).map D.lift
    have hlist :
        D.outerFace.first :: D.outerFace.rest =
          pref ++ ([D.toStart] : List D.rotation.toHypermap.Dart) := by
      rw [D.outer_rest]
      simp [pref]
      rfl
    rw [hlist]
    simp [List.getLastD_eq_getLast?]
  have htoStartHead : D.toStart.head = none := by
    calc
      D.toStart.head =
          (D.rotation.toHypermap.face D.toStart).tail :=
        (D.rotation.toHypermap_face_tail D.toStart).symm
      _ = D.outerFace.first.tail := by
        rw [← D.outerFace.close, hlast]
      _ = none := D.outer_first_tail
  have houterRest :
      D.outerFace.rest =
        (q.darts.map E.symm).map
            (addNodeGraphSomeOrientedEdge G A) ++ [D.toStart] := by
    have hliftOuter :
        D.outer.map D.lift =
          D.outer.map (addNodeGraphSomeOrientedEdge G A) := by
      apply List.map_congr_left
      intro d hd
      simpa [A] using D.lift_eq d
    rw [D.outer_rest, hqDarts]
    simp only [List.map_cons, List.map_append]
    rw [show D.lift D.next = addNodeGraphSomeOrientedEdge G A D.next by
      simpa [A] using D.lift_eq D.next]
    rw [hliftOuter]
    rw [show D.lift D.closing =
        addNodeGraphSomeOrientedEdge G A D.closing by
      simpa [A] using D.lift_eq D.closing]
    simp [List.append_assoc]
  refine ⟨q, hq, hqRawDarts, hqDarts, ?_⟩
  simpa [A] using
    D.outerFace.isFacialCycle_addNodeGraphPathCycleAtNewIn
      htA hsA hst.symm q hq D.toStart D.outer_first_tail
        houterFirstHead D.toStart_tail htoStartHead houterRest

/-- The retained complementary face and the selected fan face have no common
forward oriented dart.  The old darts are disjoint because they are the two
parts of the original simple facial cycle; the two fresh spokes occur in
opposite orientations. -/
theorem FacialPathSplitData.complementary_forward_disjoint_selected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {r s t : V}
    {c : G.Walk r r} {p : G.Walk s t}
    {hp : p.IsPath} {hst : s ≠ t}
    [DecidableRel (addNodeGraph G (insert t ({s} : Set V))).Adj]
    (D : FacialPathSplitData R c p hp hst)
    (hc : c.IsCycle)
    {q : G.Walk t s}
    (hqDarts :
      q.darts.map (orientedEdgeDartEquiv (G := G)).symm =
        D.next :: D.outer ++ [D.closing]) :
    forall e : OrientedEdge
        (addNodeGraph G (insert t ({s} : Set V))),
      CycleForwardDart
          (addNodeGraphPathCycleAtNewIn G
            (insert t ({s} : Set V)) (by simp) (by simp) q) e ->
        Not (CycleForwardDart (addNodeGraphPathCycleAtNew p) e) := by
  classical
  let A : Set V := insert t ({s} : Set V)
  let H : SimpleGraph (Option V) := addNodeGraph G A
  let E := orientedEdgeDartEquiv (G := G)
  let lift := addNodeGraphSomeOrientedEdge G A
  let pds : List (OrientedEdge G) := p.darts.map E.symm
  let qds : List (OrientedEdge G) := q.darts.map E.symm
  have hcDartsNodup : c.darts.Nodup := by
    apply List.Nodup.of_map SimpleGraph.Dart.edge
    change c.edges.Nodup
    exact hc.isTrail.edges_nodup
  have hcOrientedNodup : (c.darts.map E.symm).Nodup :=
    hcDartsNodup.map E.symm.injective
  have hall :
      (D.closing :: (pds ++ (D.next :: D.outer))).Nodup := by
    rw [D.ordered_darts] at hcOrientedNodup
    simpa [pds, E] using hcOrientedNodup
  have hrotated :
      (pds ++ (D.next :: D.outer ++ [D.closing])).Nodup := by
    have hclosingNot : D.closing ∉ pds ++ (D.next :: D.outer) :=
      (List.nodup_cons.mp hall).1
    rw [← List.append_assoc]
    rw [List.nodup_append]
    refine ⟨hall.tail, by simp, ?_⟩
    intro d hd closing hclosing hdc
    simp only [List.mem_singleton] at hclosing
    subst closing
    subst d
    exact hclosingNot hd
  have hpq : pds.Disjoint qds := by
    have hqds : qds = D.next :: D.outer ++ [D.closing] := by
      simpa [qds, E] using hqDarts
    rw [hqds]
    exact List.disjoint_of_nodup_append hrotated
  have hliftDisjoint : (pds.map lift).Disjoint (qds.map lift) :=
    hpq.map (addNodeGraphSomeOrientedEdge_injective G A)
  let outS : OrientedEdge H :=
    ⟨(none, some s), by simp [H, A, addNodeGraph]⟩
  let inT : OrientedEdge H :=
    ⟨(some t, none), by simp [H, A, addNodeGraph]⟩
  let outT : OrientedEdge H :=
    ⟨(none, some t), by simp [H, A, addNodeGraph]⟩
  let inS : OrientedEdge H :=
    ⟨(some s, none), by simp [H, A, addNodeGraph]⟩
  intro e heOuter heSelected
  let outerCycle : H.Walk none none :=
    addNodeGraphPathCycleAtNewIn G A (by simp [A]) (by simp [A]) q
  have heOuterMem :
      e ∈ outerCycle.darts.map (orientedEdgeDartEquiv (G := H)).symm :=
    (cycleForwardDart_iff_mem_orientedDarts _ e).mp (by
      simpa [outerCycle, A, H] using heOuter)
  dsimp [outerCycle] at heOuterMem
  rw [addNodeGraphPathCycleAtNewIn_orientedDarts] at heOuterMem
  change e ∈ outT :: (qds.map lift ++ [inS]) at heOuterMem
  have heSelectedMem :
      e ∈ (addNodeGraphPathCycleAtNew p).darts.map
        (orientedEdgeDartEquiv (G := H)).symm :=
    (cycleForwardDart_iff_mem_orientedDarts _ e).mp (by
      simpa [A, H] using heSelected)
  rw [addNodeGraphPathCycleAtNew_orientedDarts] at heSelectedMem
  change e ∈ outS :: (pds.map lift ++ [inT]) at heSelectedMem
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at heOuterMem heSelectedMem
  rcases heSelectedMem with heOutS | heSelectedOld | heInT
  · subst e
    rcases heOuterMem with heOutT | heOuterOld | heInS
    · have hhead := congrArg OrientedEdge.head heOutT
      change some s = some t at hhead
      exact hst (Option.some.inj hhead)
    · rcases List.mem_map.mp heOuterOld with ⟨d, hd, hde⟩
      have htail := congrArg OrientedEdge.tail hde
      change some d.tail = none at htail
      exact Option.some_ne_none d.tail htail
    · have htail := congrArg OrientedEdge.tail heInS
      change (none : Option V) = some s at htail
      exact Option.some_ne_none s htail.symm
  · rcases heOuterMem with heOutT | heOuterOld | heInS
    · rcases List.mem_map.mp heSelectedOld with ⟨d, hd, hde⟩
      have htail := congrArg OrientedEdge.tail (hde.trans heOutT)
      change some d.tail = none at htail
      exact Option.some_ne_none d.tail htail
    · exact List.disjoint_left.mp hliftDisjoint heSelectedOld heOuterOld
    · rcases List.mem_map.mp heSelectedOld with ⟨d, hd, hde⟩
      have hhead := congrArg OrientedEdge.head (hde.trans heInS)
      change some d.head = none at hhead
      exact Option.some_ne_none d.head hhead
  · subst e
    rcases heOuterMem with heOutT | heOuterOld | heInS
    · have htail := congrArg OrientedEdge.tail heOutT
      change some t = (none : Option V) at htail
      exact Option.some_ne_none t htail
    · rcases List.mem_map.mp heOuterOld with ⟨d, hd, hde⟩
      have hhead := congrArg OrientedEdge.head hde
      change some d.head = none at hhead
      exact Option.some_ne_none d.head hhead
    · have htail := congrArg OrientedEdge.tail heInS
      change some t = some s at htail
      exact hst.symm (Option.some.inj htail)

theorem FacialPathSplitData.toHypermap_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} {r s t : V}
    {c : G.Walk r r} {p : G.Walk s t}
    {hp : p.IsPath} {hst : s ≠ t}
    [DecidableRel (addNodeGraph G (insert t ({s} : Set V))).Adj]
    (D : FacialPathSplitData R c p hp hst)
    (hG : (G.induce G.support).Preconnected)
    (hs : s ∈ G.support) (ht : t ∈ G.support) :
    D.rotation.toHypermap.Connected := by
  let selected := addNodeGraphPathCycleAtNew p
  let hselected : selected.IsCycle :=
    addNodeGraphPathCycleAtNew_isCycle hst p hp
  letI : Nonempty
      (OrientedEdge (addNodeGraph G (insert t ({s} : Set V)))) :=
    ⟨cycleFirstDart selected hselected⟩
  exact D.rotation.toHypermap_connected_of_support_preconnected
    (addNodeGraph_pair_support_preconnected hG hs ht)

/-- Glue two path-split disk rotations along their oppositely oriented
fresh-node closures.  The common cycle and all dependent transports are
constructed from the two ordered path supports. -/
theorem exists_dualEulerPlanar_cycleSum_of_facialPathSplits
    {V : Type u} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel K.Adj]
    {R : RotationSystem G} {T : RotationSystem K}
    {r r' s t : V}
    {c : G.Walk r r} {d : K.Walk r' r'}
    {p : G.Walk s t} {q : K.Walk t s}
    {hp : p.IsPath} {hq : q.IsPath} {hst : s ≠ t}
    [DecidableRel (addNodeGraph G (insert t ({s} : Set V))).Adj]
    [DecidableRel (addNodeGraph K (insert s ({t} : Set V))).Adj]
    (D₁ : FacialPathSplitData R c p hp hst)
    (D₂ : FacialPathSplitData T d q hq hst.symm)
    (hsupport : q.support = p.reverse.support)
    (hcommon : forall ⦃x y : Option V⦄,
      (addNodeGraph G (insert t ({s} : Set V))).Adj x y ->
        (addNodeGraph K (insert s ({t} : Set V))).Adj x y ->
          (addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe.Adj x y)
    (hmeet : forall ⦃v : Option V⦄,
      v ∈ (addNodeGraph G (insert t ({s} : Set V))).support ->
        v ∈ (addNodeGraph K (insert s ({t} : Set V))).support ->
          v ∈ (addNodeGraphPathCycleAtNew p).support)
    (hG : (G.induce G.support).Preconnected)
    (hK : (K.induce K.support).Preconnected)
    (hsG : s ∈ G.support) (htG : t ∈ G.support)
    (htK : t ∈ K.support) (hsK : s ∈ K.support) :
    Exists fun U : RotationSystem
        (addNodeGraph G (insert t ({s} : Set V)) ⊔
          addNodeGraph K (insert s ({t} : Set V))) =>
      (U.toHypermap).dual.EulerPlanar := by
  classical
  let H₁ := addNodeGraph G (insert t ({s} : Set V))
  let H₂ := addNodeGraph K (insert s ({t} : Set V))
  let selected : H₁.Walk none none := addNodeGraphPathCycleAtNew p
  let selected₂ : H₂.Walk none none := addNodeGraphPathCycleAtNew q
  let C : SimpleGraph (Option V) := selected.toSubgraph.spanningCoe
  let common : C.Walk none none :=
    SimpleGraph.Walk.toSpanningCoe selected
  have hC₁ : C <= H₁ := selected.toSubgraph.spanningCoe_le
  have hspanEq :
      selected.toSubgraph.spanningCoe =
        selected₂.toSubgraph.spanningCoe := by
    exact addNodeGraphPathCycleAtNew_spanningCoe_eq_of_reverse_support
      p q hsupport
  have hC₂ : C <= H₂ := by
    rw [show C = selected₂.toSubgraph.spanningCoe by
      exact hspanEq]
    exact selected₂.toSubgraph.spanningCoe_le
  have hselectedCycle : selected.IsCycle :=
    addNodeGraphPathCycleAtNew_isCycle hst p hp
  have hcommonCycle : common.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_mapLe hC₁
    simpa [common, C, selected] using hselectedCycle
  have hspan : common.toSubgraph.spanningCoe = C := by
    calc
      common.toSubgraph.spanningCoe = selected.toSubgraph.spanningCoe :=
        SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_support_eq
          common selected (by
            simp [common, SimpleGraph.Walk.support_toSpanningCoe])
      _ = C := rfl
  have hfacial₁ :
      RotationSystemGluing.IsFacialCycle D₁.rotation
        (common.mapLe hC₁) (hcommonCycle.mapLe hC₁) := by
    simpa [common, C, selected] using D₁.selected_facial
  have hwalk₂ : (common.mapLe hC₂).reverse = selected₂ := by
    apply SimpleGraph.Walk.support_injective
    rw [_root_.SimpleGraph.Walk.support_reverse,
      _root_.SimpleGraph.Walk.support_mapLe_eq_support]
    rw [SimpleGraph.Walk.support_toSpanningCoe]
    simpa [selected, selected₂,
      _root_.SimpleGraph.Walk.support_reverse] using
        (addNodeGraphPathCycleAtNew_support_eq_reverse p q hsupport).symm
  have hfacial₂ :
      RotationSystemGluing.IsFacialCycle D₂.rotation
        (common.mapLe hC₂).reverse
        (hcommonCycle.mapLe hC₂).reverse := by
    simpa [hwalk₂, selected₂] using D₂.selected_facial
  have hconn₁ : D₁.rotation.toHypermap.Connected :=
    D₁.toHypermap_connected hG hsG htG
  have hconn₂ : D₂.rotation.toHypermap.Connected :=
    D₂.toHypermap_connected hK htK hsK
  have hmeetCommon : forall ⦃v : Option V⦄,
      v ∈ H₁.support -> v ∈ H₂.support -> v ∈ common.support := by
    intro v hv₁ hv₂
    have hv := hmeet hv₁ hv₂
    simpa [common, selected] using hv
  let U := RotationSystemGluing.cycleSum
    D₁.rotation D₂.rotation hC₁ hC₂ hcommon
      common hcommonCycle hspan hfacial₁ hfacial₂ hmeetCommon
  refine ⟨U, ?_⟩
  exact RotationSystemGluing.cycleSum_dual_eulerPlanar
    D₁.rotation D₂.rotation hC₁ hC₂ hcommon
      common hcommonCycle hspan hfacial₁ hfacial₂ hmeetCommon
      hconn₁ hconn₂ D₁.dual_eulerPlanar D₂.dual_eulerPlanar


end RotationSystemFan

end FourColor

end Schematic.Math.GraphTheory
