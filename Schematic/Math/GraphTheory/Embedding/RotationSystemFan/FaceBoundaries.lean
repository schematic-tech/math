import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.FacialTransport

/-! Ordered boundaries of hypermap faces and their elementary extensions. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemFan

/-- A face orbit written once in its cyclic order.  This is Lean's direct
counterpart of Coq's `sface`: unlike a graph cycle, its vertex projection may
repeat vertices while its darts remain distinct. -/
structure FaceBoundary (H : Hypermap.{u}) where
  first : H.Dart
  rest : List H.Dart
  path : H.FacePath first rest
  close : H.face ((first :: rest).getLastD first) = first
  nodup : (first :: rest).Nodup

/-- Every finite hypermap face has an ordered boundary. -/
noncomputable def faceBoundaryAt (H : Hypermap.{u}) (x : H.Dart) :
    FaceBoundary H := by
  classical
  let h := H.exists_ordered_faceOrbitCycle x
  exact ⟨x, h.choose, h.choose_spec.1, h.choose_spec.2.1,
    h.choose_spec.2.2.1⟩

/-- The ordered face boundary based at the first forward dart of a checked
facial graph cycle. -/
noncomputable def facialCycleBoundary
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle) :
    FaceBoundary R.toHypermap :=
  faceBoundaryAt R.toHypermap (cycleFirstDart c hc)

@[simp]
theorem facialCycleBoundary_first
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle) :
    (facialCycleBoundary R c hc).first = cycleFirstDart c hc :=
  rfl

theorem mem_facialCycleBoundary_iff_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    (d : OrientedEdge G) :
    d ∈ (facialCycleBoundary R c hc).first ::
        (facialCycleBoundary R c hc).rest ↔
      CycleForwardDart c d := by
  let B := facialCycleBoundary R c hc
  change d ∈ B.first :: B.rest ↔ CycleForwardDart c d
  have hmem := Hypermap.FacePath.mem_iff_faceReachable_closed
    R.toHypermap (y := d) B.path B.close
  constructor
  · intro hd
    apply (hfacial d).mpr
    simpa [B, facialCycleBoundary] using hmem.mp hd
  · intro hd
    apply hmem.mpr
    simpa [B, facialCycleBoundary] using (hfacial d).mp hd

/-- Any explicitly ordered closed face boundary whose darts are exactly the
forward darts of a graph cycle certifies that cycle as facial.  This is the
converse interface used after a face has been split combinatorially. -/
theorem FaceBoundary.isFacialCycle_of_mem_iff_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} (B : FaceBoundary R.toHypermap)
    {r : V} (c : G.Walk r r) (hc : c.IsCycle)
    (hfirst : B.first = cycleFirstDart c hc)
    (hmem : forall d : OrientedEdge G,
      d ∈ B.first :: B.rest ↔ CycleForwardDart c d) :
    RotationSystemGluing.IsFacialCycle R c hc := by
  intro d
  have hface := Hypermap.FacePath.mem_iff_faceReachable_closed
    R.toHypermap (y := d) B.path B.close
  constructor
  · intro hd
    rw [← hfirst]
    exact hface.mp ((hmem d).mpr hd)
  · intro hd
    exact (hmem d).mp (hface.mpr (by simpa [hfirst] using hd))

/-- An explicit face boundary equal to the oriented dart list of a simple
cycle certifies that cycle as facial.  This is the convenient endpoint for
the split-face constructions below, whose output is an exact list rather
than a reachability predicate. -/
theorem FaceBoundary.isFacialCycle_of_eq_cycleDarts
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} (B : FaceBoundary R.toHypermap)
    {r : V} (c : G.Walk r r) (hc : c.IsCycle)
    (hfirst : B.first = cycleFirstDart c hc)
    (hlist : B.first :: B.rest =
      c.darts.map (orientedEdgeDartEquiv (G := G)).symm) :
    RotationSystemGluing.IsFacialCycle R c hc := by
  apply B.isFacialCycle_of_mem_iff_forward c hc hfirst
  intro d
  rw [hlist, cycleForwardDart_iff_mem_darts]
  let E := orientedEdgeDartEquiv (G := G)
  constructor
  · intro hd
    rcases List.mem_map.mp hd with ⟨e, he, hed⟩
    have hEd : E d = e := by
      calc
        E d = E (E.symm e) := congrArg E hed.symm
        _ = e := E.apply_symm_apply e
    change E d ∈ c.darts
    rw [hEd]
    exact he
  · intro hd
    apply List.mem_map.mpr
    refine ⟨E d, ?_, E.symm_apply_apply d⟩
    exact hd

theorem facialCycleBoundary_tails_nodup
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc) :
    (((facialCycleBoundary R c hc).first ::
        (facialCycleBoundary R c hc).rest).map OrientedEdge.tail).Nodup := by
  let B := facialCycleBoundary R c hc
  apply B.nodup.map_on
  intro a ha b hb hab
  exact cycleForwardDart_eq_of_tail_eq hc
    ((mem_facialCycleBoundary_iff_forward R c hc hfacial a).mp ha)
    ((mem_facialCycleBoundary_iff_forward R c hc hfacial b).mp hb) hab

theorem facialCycleBoundary_exists_tail_of_mem_support
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    {z : V} (hz : z ∈ c.support) :
    Exists fun d : OrientedEdge G =>
      d ∈ (facialCycleBoundary R c hc).first ::
          (facialCycleBoundary R c hc).rest ∧
        d.tail = z := by
  rcases exists_cycleForwardDart_of_mem_support hc hz with ⟨d, hd, htail⟩
  exact ⟨d,
    (mem_facialCycleBoundary_iff_forward R c hc hfacial d).mpr hd,
    htail⟩

/-- Canonical facial boundary whose complete dart list is the directed dart
list of the graph cycle itself. -/
noncomputable def orderedFacialCycleBoundary
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc) :
    FaceBoundary R.toHypermap := by
  classical
  let E : OrientedEdge G ≃ G.Dart := orientedEdgeDartEquiv (G := G)
  let ds : List (OrientedEdge G) := c.darts.map E.symm
  have hcDartsNe : c.darts ≠ [] := by
    simpa using SimpleGraph.Walk.darts_eq_nil.not.mpr hc.not_nil
  have hdsNe : ds ≠ [] := by simp [ds, hcDartsNe]
  have hfirst : ds.head hdsNe = cycleFirstDart c hc := by
    apply E.injective
    rw [List.head_map]
    rw [E.apply_symm_apply]
    rw [← c.firstDart_eq_head_darts hc.not_nil]
    apply SimpleGraph.Dart.ext
    exact calc
      (c.firstDart hc.not_nil).toProd = (r, c.snd) :=
        c.firstDart_toProd hc.not_nil
      _ = (E (cycleFirstDart c hc)).toProd := by
        apply Prod.ext
        · change r = (cycleFirstDart c hc).tail
          exact (cycleFirstDart_tail c hc).symm
        · change c.snd = (cycleFirstDart c hc).head
          rfl
  let first := cycleFirstDart c hc
  let rest := ds.tail
  have hdsEq : ds = first :: rest := by
    calc
      ds = ds.head hdsNe :: ds.tail := (List.cons_head_tail hdsNe).symm
      _ = first :: rest := by rw [hfirst]
  have hforwardOfMem {d : OrientedEdge G} (hd : d ∈ ds) :
      CycleForwardDart c d := by
    apply (cycleForwardDart_iff_mem_darts c d).mpr
    rcases List.mem_map.mp hd with ⟨e, he, hed⟩
    have hEd : E d = e := by
      calc
        E d = E (E.symm e) := congrArg E hed.symm
        _ = e := E.apply_symm_apply e
    rw [hEd]
    exact he
  have htailChain :
      List.IsChain (fun a b : OrientedEdge G => a.head = b.tail) ds := by
    rw [List.isChain_map]
    exact c.isChain_dartAdj_darts.imp (fun {a b} hab => by
      simpa [E, orientedEdgeDartEquiv, SimpleGraph.DartAdj] using hab)
  have hfaceChain :
      List.IsChain (fun a b : OrientedEdge G => R.toHypermap.face a = b) ds := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi0 : i < ds.length := by omega
    have hi1 : i + 1 < ds.length := hi
    let a := ds[i]
    let b := ds[i + 1]
    have haMem : a ∈ ds := List.getElem_mem hi0
    have hbMem : b ∈ ds := List.getElem_mem hi1
    have haForward : CycleForwardDart c a := hforwardOfMem haMem
    have hbForward : CycleForwardDart c b := hforwardOfMem hbMem
    have hfaceForward : CycleForwardDart c (R.toHypermap.face a) :=
      hfacial.face_forward haForward
    apply cycleForwardDart_eq_of_tail_eq hc hfaceForward hbForward
    calc
      (R.toHypermap.face a).tail = a.head := R.toHypermap_face_tail a
      _ = b.tail := htailChain.getElem i hi
  have hpath : R.toHypermap.FacePath first rest := by
    rw [Hypermap.FacePath.iff_isChain]
    exact hdsEq ▸ hfaceChain
  have hlastHead : (ds.getLast hdsNe).head = r := by
    rw [List.getLast_map]
    change (c.darts.getLast hcDartsNe).snd = r
    rw [c.getLast_darts_eq_lastDart]
    exact congrArg Prod.snd (c.lastDart_toProd hc.not_nil)
  have hlastMem : ds.getLast hdsNe ∈ ds := List.getLast_mem hdsNe
  have hlastForward : CycleForwardDart c (ds.getLast hdsNe) :=
    hforwardOfMem hlastMem
  have hcloseLast : R.toHypermap.face (ds.getLast hdsNe) = first := by
    apply cycleForwardDart_eq_of_tail_eq hc
      (hfacial.face_forward hlastForward)
      (cycleForwardDart_first c hc)
    calc
      (R.toHypermap.face (ds.getLast hdsNe)).tail =
          (ds.getLast hdsNe).head := R.toHypermap_face_tail _
      _ = r := hlastHead
      _ = first.tail := by simp [first]
  have hlastEq :
      (first :: rest).getLastD first = ds.getLast hdsNe := by
    have hopt : (first :: rest).getLast? = ds.getLast? :=
      congrArg List.getLast? hdsEq.symm
    calc
      (first :: rest).getLastD first =
          (first :: rest).getLast?.getD first :=
        List.getLastD_eq_getLast?
      _ = ds.getLast?.getD first := congrArg (Option.getD · first) hopt
      _ = ds.getLast hdsNe := by
        rw [List.getLast?_eq_some_getLast hdsNe]
        rfl
  have hdartsNodup : c.darts.Nodup := by
    apply List.Nodup.of_map SimpleGraph.Dart.edge
    change c.edges.Nodup
    exact hc.isTrail.edges_nodup
  exact {
    first := first
    rest := rest
    path := hpath
    close := by
      calc
        R.toHypermap.face ((first :: rest).getLastD first) =
            R.toHypermap.face (ds.getLast hdsNe) := congrArg _ hlastEq
        _ = first := hcloseLast
    nodup := by
      exact hdsEq ▸ hdartsNodup.map E.symm.injective
  }

theorem orderedFacialCycleBoundary_darts
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc) :
    (orderedFacialCycleBoundary R c hc hfacial).first ::
        (orderedFacialCycleBoundary R c hc hfacial).rest =
      c.darts.map (orientedEdgeDartEquiv (G := G)).symm := by
  classical
  unfold orderedFacialCycleBoundary
  let E : OrientedEdge G ≃ G.Dart := orientedEdgeDartEquiv (G := G)
  let ds : List (OrientedEdge G) := c.darts.map E.symm
  have hcDartsNe : c.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hc.not_nil
  have hdsNe : ds ≠ [] := by simp [ds, hcDartsNe]
  have hfirst : ds.head hdsNe = cycleFirstDart c hc := by
    apply E.injective
    rw [List.head_map, E.apply_symm_apply]
    rw [← c.firstDart_eq_head_darts hc.not_nil]
    apply SimpleGraph.Dart.ext
    exact calc
      (c.firstDart hc.not_nil).toProd = (r, c.snd) :=
        c.firstDart_toProd hc.not_nil
      _ = (E (cycleFirstDart c hc)).toProd := by
        apply Prod.ext
        · change r = (cycleFirstDart c hc).tail
          exact (cycleFirstDart_tail c hc).symm
        · change c.snd = (cycleFirstDart c hc).head
          rfl
  calc
    cycleFirstDart c hc :: ds.tail = ds.head hdsNe :: ds.tail := by
      rw [hfirst]
    _ = ds := List.cons_head_tail hdsNe

/-- Rotate an ordered face boundary to a selected dart. -/
noncomputable def FaceBoundary.rotateTo
    {H : Hypermap.{u}} (B : FaceBoundary H)
    (q : H.Dart) (hq : q ∈ B.first :: B.rest) : FaceBoundary H := by
  classical
  by_cases hqFirst : q = B.first
  · simpa [hqFirst] using B
  · have hqRest : q ∈ B.rest := by
      simpa [hqFirst] using hq
    let split := (List.mem_iff_append).mp hqRest
    let pre := split.choose
    let post := split.choose_spec.choose
    have hrest : B.rest = pre ++ q :: post := split.choose_spec.choose_spec
    have hclosed : H.FacePath B.first (B.rest ++ [B.first]) :=
      Hypermap.FacePath.snoc (G := H) B.path rfl B.close
    have hrot : H.FacePath q (post ++ B.first :: pre ++ [q]) :=
      Hypermap.FacePath.rotate_closed_of_eq (G := H) hclosed hrest
    have hsplit := Hypermap.FacePath.split_append_cons
      (G := H) (p := post ++ B.first :: pre) (q := []) hrot
    exact {
      first := q
      rest := post ++ B.first :: pre
      path := hsplit.1
      close := by simpa using hsplit.2.1
      nodup := by
        have hold : ((B.first :: pre) ++ q :: post).Nodup := by
          simpa [hrest, List.append_assoc] using B.nodup
        exact hold.perm (List.perm_append_comm.trans (by simp))
    }

@[simp]
theorem FaceBoundary.rotateTo_first
    {H : Hypermap.{u}} (B : FaceBoundary H)
    (q : H.Dart) (hq : q ∈ B.first :: B.rest) :
    (B.rotateTo q hq).first = q := by
  classical
  unfold FaceBoundary.rotateTo
  split <;> simp_all

/-- Rotate an ordered face boundary at an explicitly supplied occurrence in
its tail.  Unlike `FaceBoundary.rotateTo`, this constructor retains the
chosen prefix and suffix in definitional form, which is useful when a later
face-splitting argument must identify both resulting boundary walks exactly. -/
noncomputable def FaceBoundary.rotateFromRest
    {H : Hypermap.{u}} (B : FaceBoundary H)
    (q : H.Dart) (pre post : List H.Dart)
    (hrest : B.rest = pre ++ q :: post) : FaceBoundary H := by
  classical
  have hclosed : H.FacePath B.first (B.rest ++ [B.first]) :=
    Hypermap.FacePath.snoc (G := H) B.path rfl B.close
  have hrot : H.FacePath q (post ++ B.first :: pre ++ [q]) :=
    Hypermap.FacePath.rotate_closed_of_eq (G := H) hclosed hrest
  have hsplit := Hypermap.FacePath.split_append_cons
    (G := H) (p := post ++ B.first :: pre) (q := []) hrot
  exact {
    first := q
    rest := post ++ B.first :: pre
    path := hsplit.1
    close := by simpa using hsplit.2.1
    nodup := by
      have hold : ((B.first :: pre) ++ q :: post).Nodup := by
        simpa [hrest, List.append_assoc] using B.nodup
      exact hold.perm (List.perm_append_comm.trans (by simp))
  }

@[simp]
theorem FaceBoundary.rotateFromRest_first
    {H : Hypermap.{u}} (B : FaceBoundary H)
    (q : H.Dart) (pre post : List H.Dart)
    (hrest : B.rest = pre ++ q :: post) :
    (B.rotateFromRest q pre post hrest).first = q := by
  rfl

@[simp]
theorem FaceBoundary.rotateFromRest_rest
    {H : Hypermap.{u}} (B : FaceBoundary H)
    (q : H.Dart) (pre post : List H.Dart)
    (hrest : B.rest = pre ++ q :: post) :
    (B.rotateFromRest q pre post hrest).rest =
      post ++ B.first :: pre := by
  rfl

/-- If an initial segment of an ordered face is exactly the oriented-dart
image of a nontrivial graph walk, then the next face dart starts at the walk's
terminal vertex.  This is the endpoint bookkeeping used when a facial cycle
is split immediately after a prescribed path. -/
theorem FaceBoundary.next_tail_eq_walk_to
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge G) (pre post : List (OrientedEdge G))
    (hrest : B.rest = pre ++ q :: post)
    {s t : V} (p : G.Walk s t) (hp : ¬ p.Nil)
    (hprefix : B.first :: pre =
      p.darts.map (orientedEdgeDartEquiv (G := G)).symm) :
    q.tail = t := by
  let ds : List (OrientedEdge G) :=
    p.darts.map (orientedEdgeDartEquiv (G := G)).symm
  have hpDartsNe : p.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hp
  have hdsNe : ds ≠ [] := by simp [ds, hpDartsNe]
  have hface :
      R.toHypermap.face ((B.first :: pre).getLastD B.first) = q := by
    have hfull : R.toHypermap.FacePath B.first (pre ++ q :: post) := by
      simpa [hrest] using B.path
    exact (Hypermap.FacePath.split_append_cons
      (G := R.toHypermap) hfull).2.1
  have hlastEq :
      (B.first :: pre).getLastD B.first = ds.getLast hdsNe := by
    have hopt : (B.first :: pre).getLast? = ds.getLast? :=
      congrArg List.getLast? (by simpa [ds] using hprefix)
    calc
      (B.first :: pre).getLastD B.first =
          (B.first :: pre).getLast?.getD B.first :=
        List.getLastD_eq_getLast?
      _ = ds.getLast?.getD B.first := congrArg (Option.getD · B.first) hopt
      _ = ds.getLast hdsNe := by
        rw [List.getLast?_eq_some_getLast hdsNe]
        rfl
  have hlastHead : (ds.getLast hdsNe).head = t := by
    rw [List.getLast_map]
    change (p.darts.getLast hpDartsNe).snd = t
    rw [p.getLast_darts_eq_lastDart]
    exact congrArg Prod.snd (p.lastDart_toProd hp)
  calc
    q.tail = (R.toHypermap.face
        ((B.first :: pre).getLastD B.first)).tail :=
      congrArg OrientedEdge.tail hface.symm
    _ = ((B.first :: pre).getLastD B.first).head :=
      R.toHypermap_face_tail _
    _ = (ds.getLast hdsNe).head := congrArg OrientedEdge.head hlastEq
    _ = t := hlastHead

/-- If the beginning of an explicitly ordered face is the oriented-dart list
of a nontrivial walk, then the face's base dart starts at the walk's initial
vertex. -/
theorem FaceBoundary.first_tail_eq_walk_from
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : RotationSystem G} (B : FaceBoundary R.toHypermap)
    {s t : V} (p : G.Walk s t) (hp : ¬p.Nil)
    (pre : List (OrientedEdge G))
    (hprefix : B.first :: pre =
      p.darts.map (orientedEdgeDartEquiv (G := G)).symm) :
    B.first.tail = s := by
  cases p with
  | nil => exact False.elim (hp SimpleGraph.Walk.Nil.nil)
  | @cons _ x _ hsx q =>
      simp only [SimpleGraph.Walk.darts_cons, List.map_cons] at hprefix
      have hfirst := (List.cons.inj hprefix).1
      rw [hfirst]
      rfl

/-- Split a facial cycle at two distinct vertices.

The returned face boundary is based at a forward cycle dart leaving `s`;
the distinguished dart `q`, which leaves `t`, occurs in its remaining
boundary list.  This is the ordered input expected by
`exists_addNodeGraph_pairSplitBoundaries`. -/
theorem exists_facialCycleBoundary_split_at_distinct_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    {s t : V} (hs : s ∈ c.support) (ht : t ∈ c.support)
    (hst : s ≠ t) :
    Exists fun B : FaceBoundary R.toHypermap =>
      Exists fun q : OrientedEdge G =>
        Exists fun pre : List (OrientedEdge G) =>
          Exists fun post : List (OrientedEdge G) =>
            B.first.tail = s ∧ q.tail = t ∧
              B.rest = pre ++ q :: post := by
  classical
  rcases exists_cycleForwardDart_of_mem_support hc hs with
    ⟨p, hpForward, hpTail⟩
  rcases exists_cycleForwardDart_of_mem_support hc ht with
    ⟨q, hqForward, hqTail⟩
  let B0 := orderedFacialCycleBoundary R c hc hfacial
  have hpB0 : p ∈ B0.first :: B0.rest := by
    rw [orderedFacialCycleBoundary_darts R c hc hfacial]
    refine List.mem_map.mpr ⟨orientedEdgeDartEquiv p, ?_, ?_⟩
    · exact (cycleForwardDart_iff_mem_darts c p).mp hpForward
    · exact (orientedEdgeDartEquiv (G := G)).symm_apply_apply p
  let B : FaceBoundary R.toHypermap := B0.rotateTo p hpB0
  have hBfirst : B.first = p := by
    simp [B]
  have hqReach : PermReachable R.toHypermap.face B.first q := by
    have hpReach :
        PermReachable R.toHypermap.face (cycleFirstDart c hc) p :=
      (hfacial p).mp hpForward
    have hqReach :
        PermReachable R.toHypermap.face (cycleFirstDart c hc) q :=
      (hfacial q).mp hqForward
    rw [hBfirst]
    exact PermReachable.trans R.toHypermap.face
      (PermReachable.symm R.toHypermap.face hpReach) hqReach
  have hqB : q ∈ B.first :: B.rest := by
    exact
      (Hypermap.FacePath.mem_iff_faceReachable_closed
        R.toHypermap B.path B.close).mpr hqReach
  have hqNeFirst : q ≠ B.first := by
    intro h
    apply hst
    calc
      s = B.first.tail := by simp [hBfirst, hpTail]
      _ = q.tail := congrArg OrientedEdge.tail h.symm
      _ = t := hqTail
  have hqRest : q ∈ B.rest := by
    have hcases : q = B.first ∨ q ∈ B.rest :=
      List.mem_cons.mp hqB
    exact hcases.resolve_left hqNeFirst
  rcases (List.mem_iff_append).mp hqRest with ⟨pre, post, hrest⟩
  exact ⟨B, q, pre, post,
    by simpa [hBfirst] using hpTail,
    hqTail, hrest⟩

/-- Transport an ordered face boundary through a hypermap isomorphism. -/
def FaceBoundary.mapIso
    {H K : Hypermap.{u}} (phi : Hypermap.Iso H K)
    (B : FaceBoundary H) : FaceBoundary K where
  first := phi.toEquiv B.first
  rest := B.rest.map phi.toEquiv
  path := by
    have mapPath : forall (a : H.Dart) (l : List H.Dart),
        H.FacePath a l ->
          K.FacePath (phi.toEquiv a) (l.map phi.toEquiv) := by
      intro a l hl
      induction l generalizing a with
      | nil => simp
      | cons b l ih =>
          rw [Hypermap.FacePath.cons] at hl
          rw [List.map_cons, Hypermap.FacePath.cons]
          exact ⟨(phi.map_face a).symm.trans (congrArg phi.toEquiv hl.1),
            ih b hl.2⟩
    exact mapPath B.first B.rest B.path
  close := by
    change K.face (((B.first :: B.rest).map phi.toEquiv).getLastD
      (phi.toEquiv B.first)) = phi.toEquiv B.first
    rw [List.getLastD_map, ← phi.map_face, B.close]
  nodup := B.nodup.map phi.toEquiv.injective

private theorem leafHypermap_oldPath_to_newEdge
    (H : Hypermap.{u}) (p x : H.Dart) (l : List H.Dart)
    (hpath : H.FacePath x l)
    (hclose : H.face ((x :: l).getLastD x) = p)
    (hnodup : (x :: l).Nodup)
    (hp : p = x ∨ p ∉ x :: l) :
    (LeafExtension.leafHypermap H (some p)).FacePath (ExtDart.old x)
      (l.map ExtDart.old ++ [ExtDart.newEdge]) := by
  induction l generalizing x with
  | nil =>
      have hxpred : x = H.edge (H.node p) := by
        rw [H.edge_node_eq_face_symm]
        apply H.face.injective
        simpa using hclose
      change (LeafExtension.leafHypermap H (some p)).FacePath
        (ExtDart.old x) [ExtDart.newEdge]
      rw [Hypermap.FacePath.cons]
      exact ⟨LeafExtension.leafHypermap_face_old_some_eq H p x hxpred,
        Hypermap.FacePath.nil (LeafExtension.leafHypermap H (some p))
          ExtDart.newEdge⟩
  | cons y l ih =>
      have hstep : H.face x = y :=
        ((Hypermap.FacePath.cons H x y l).mp hpath).1
      have htail : H.FacePath y l :=
        ((Hypermap.FacePath.cons H x y l).mp hpath).2
      have hyNodup : (y :: l).Nodup := hnodup.tail
      have hpTail : p ∉ y :: l := by
        rcases hp with rfl | hpnot
        · exact (List.nodup_cons.mp hnodup).1
        · exact fun hmem => hpnot (by simp [hmem])
      have hxNotPred : x ≠ H.edge (H.node p) := by
        intro hx
        have hyp : y = p := by
          calc
            y = H.face x := hstep.symm
            _ = H.face (H.edge (H.node p)) := by rw [hx]
            _ = p := by simp
        exact hpTail (by simp [hyp])
      change (LeafExtension.leafHypermap H (some p)).FacePath
        (ExtDart.old x)
          (ExtDart.old y :: (l.map ExtDart.old ++ [ExtDart.newEdge]))
      rw [Hypermap.FacePath.cons]
      refine ⟨(LeafExtension.leafHypermap_face_old_some_ne H p x hxNotPred).trans
        (congrArg ExtDart.old hstep), ?_⟩
      apply ih y htail
      · simpa using hclose
      · exact hyNodup
      · exact Or.inr hpTail

/-- Coq `add_node_face_orbitE`, rotated so that the outgoing dart of the new
leaf is first. -/
def FaceBoundary.addLeaf
    {H : Hypermap.{u}} (B : FaceBoundary H) :
    FaceBoundary (LeafExtension.leafHypermap H (some B.first)) where
  first := ExtDart.new
  rest := (B.first :: B.rest).map ExtDart.old ++ [ExtDart.newEdge]
  path := by
    change (LeafExtension.leafHypermap H (some B.first)).FacePath
      ExtDart.new
        (ExtDart.old B.first ::
          (B.rest.map ExtDart.old ++ [ExtDart.newEdge]))
    rw [Hypermap.FacePath.cons]
    refine ⟨LeafExtension.leafHypermap_face_new_some H B.first, ?_⟩
    exact leafHypermap_oldPath_to_newEdge H B.first B.first B.rest
      B.path B.close B.nodup (Or.inl rfl)
  close := by
    change (LeafExtension.leafHypermap H (some B.first)).face
      (((ExtDart.new :: (B.first :: B.rest).map ExtDart.old) ++
        [ExtDart.newEdge]).getLastD ExtDart.new) = ExtDart.new
    rw [List.getLastD_concat]
    exact LeafExtension.leafHypermap_face_newEdge_some H B.first
  nodup := by
    have hold : ((B.first :: B.rest).map ExtDart.old).Nodup :=
      B.nodup.map (fun _ _ h => ExtDart.old.inj h)
    have happ :
        (((B.first :: B.rest).map ExtDart.old) ++ [ExtDart.newEdge]).Nodup := by
      rw [List.nodup_append]
      exact ⟨hold, by simp, by simp⟩
    rw [List.nodup_cons]
    refine ⟨?_, happ⟩
    intro hmem
    rcases List.mem_append.mp hmem with hOld | hEdge
    · rcases List.mem_map.mp hOld with ⟨z, _hz, hbad⟩
      cases hbad
    · rcases List.mem_cons.mp hEdge with hbad | hnil
      · cases hbad
      · cases hnil

private theorem facePath_suffix
    (H : Hypermap.{u}) (x y : H.Dart)
    (pre post : List H.Dart)
    (hpath : H.FacePath x (pre ++ y :: post)) :
    H.FacePath y post := by
  induction pre generalizing x with
  | nil => exact ((Hypermap.FacePath.cons H x y post).mp hpath).2
  | cons z pre ih =>
      exact ih z ((Hypermap.FacePath.cons H x z (pre ++ y :: post)).mp hpath).2

private theorem getLastD_suffix
    {alpha : Type u} (x y : alpha) (pre post : List alpha) :
    (x :: (pre ++ y :: post)).getLastD x = (y :: post).getLastD y := by
  induction pre generalizing x with
  | nil => simp [List.getLastD]
  | cons z pre ih => simp [List.getLastD]

private theorem splitFace_oldPath_retained
    (H : Hypermap.{u}) (p q : H.Dart)
    (hpq : p ≠ q)
    (x : H.Dart) (l : List H.Dart)
    (hpath : H.FacePath x l)
    (hclose : H.face ((x :: l).getLastD x) = p)
    (hnodup : (x :: l).Nodup)
    (hp : p ∉ x :: l)
    (hq : q = x ∨ q ∉ x :: l) :
    let hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
        (some q : Option H.Dart) ≠ some r :=
      fun r hpr hqr => hpq (by simpa using hpr.trans hqr.symm)
    let K := EdgeDeletion.addEdgeHypermap H (some p) (some q) hAB
    K.FacePath (ExtDart.old x) (l.map ExtDart.old) ∧
      K.face (ExtDart.old ((x :: l).getLastD x)) = ExtDart.new := by
  let hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r :=
    fun r hpr hqr => hpq (by simpa using hpr.trans hqr.symm)
  let K := EdgeDeletion.addEdgeHypermap H (some p) (some q) hAB
  dsimp only
  induction l generalizing x with
  | nil =>
      have hxpred : x = H.face.symm p := by
        apply H.face.injective
        simpa using hclose
      constructor
      · exact Hypermap.FacePath.nil K (ExtDart.old x)
      · rw [show ([x]).getLastD x = x by rfl]
        rw [EdgeDeletion.addEdgeHypermap_face_apply_some_some H p q hAB hpq]
        simp [EdgeDeletion.splitFacePerm_old, hxpred]
  | cons y l ih =>
      have hstep : H.face x = y :=
        ((Hypermap.FacePath.cons H x y l).mp hpath).1
      have htail : H.FacePath y l :=
        ((Hypermap.FacePath.cons H x y l).mp hpath).2
      have hyNodup : (y :: l).Nodup := hnodup.tail
      have hpTail : p ∉ y :: l := fun hmem => hp (by simp [hmem])
      have hqTail : q ∉ y :: l := by
        rcases hq with rfl | hqnot
        · exact (List.nodup_cons.mp hnodup).1
        · exact fun hmem => hqnot (by simp [hmem])
      have hxNotPredP : x ≠ H.face.symm p := by
        intro hx
        have hyp : y = p := by
          calc
            y = H.face x := hstep.symm
            _ = H.face (H.face.symm p) := by rw [hx]
            _ = p := by simp
        exact hpTail (by simp [hyp])
      have hxNotPredQ : x ≠ H.face.symm q := by
        intro hx
        have hyq : y = q := by
          calc
            y = H.face x := hstep.symm
            _ = H.face (H.face.symm q) := by rw [hx]
            _ = q := by simp
        exact hqTail (by simp [hyq])
      have hrec := ih y htail (by simpa using hclose) hyNodup hpTail
        (Or.inr hqTail)
      constructor
      · change K.FacePath (ExtDart.old x)
          (ExtDart.old y :: l.map ExtDart.old)
        rw [Hypermap.FacePath.cons]
        refine ⟨?_, hrec.1⟩
        rw [EdgeDeletion.addEdgeHypermap_face_apply_some_some H p q hAB hpq]
        simp [EdgeDeletion.splitFacePerm_old, hxNotPredP, hxNotPredQ, hstep]
      · simpa using hrec.2

private theorem getLastD_new_old_map
    {alpha : Type u} (x : alpha) (l : List alpha) :
    (ExtDart.new :: (x :: l).map ExtDart.old).getLastD ExtDart.new =
      ExtDart.old ((x :: l).getLastD x) := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih =>
      change ((y :: l).map ExtDart.old).getLastD (ExtDart.old y) =
        ExtDart.old ((y :: l).getLastD y)
      exact List.getLastD_map

/-- Retain the face beginning with the new `p--q` dart after splitting an
ordered face at a later dart `q`.  This is the induction step of Coq
`plane_add_fan`. -/
def FaceBoundary.addEdgeRetained
    {H : Hypermap.{u}} (B : FaceBoundary H)
    (q : H.Dart) (pre post : List H.Dart)
    (hrest : B.rest = pre ++ q :: post) :
    let hpq : B.first ≠ q := by
      intro heq
      have hqmem : q ∈ B.rest := by rw [hrest]; simp
      apply (List.nodup_cons.mp B.nodup).1
      rw [heq]
      exact hqmem
    let hAB : forall r : H.Dart,
        (some B.first : Option H.Dart) = some r ->
          (some q : Option H.Dart) ≠ some r :=
      fun r hpr hqr => hpq (by simpa using hpr.trans hqr.symm)
    FaceBoundary
      (EdgeDeletion.addEdgeHypermap H (some B.first) (some q) hAB) := by
  let p := B.first
  have hpq : p ≠ q := by
    intro heq
    have hqmem : q ∈ B.rest := by rw [hrest]; simp
    apply (List.nodup_cons.mp B.nodup).1
    change p ∈ B.rest
    rw [heq]
    exact hqmem
  let hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r :=
    fun r hpr hqr => hpq (by simpa using hpr.trans hqr.symm)
  let K := EdgeDeletion.addEdgeHypermap H (some p) (some q) hAB
  have hqPath : H.FacePath q post := by
    apply facePath_suffix H p q pre post
    simpa [p, hrest] using B.path
  have hqClose : H.face ((q :: post).getLastD q) = p := by
    calc
      H.face ((q :: post).getLastD q) =
          H.face ((p :: (pre ++ q :: post)).getLastD p) := by
        rw [getLastD_suffix]
      _ = p := by simpa [p, hrest] using B.close
  have hqNodup : (q :: post).Nodup := by
    have htail : (pre ++ q :: post).Nodup := by
      simpa [hrest] using B.nodup.tail
    exact htail.of_append_right
  have hpNot : p ∉ q :: post := by
    intro hmem
    have hpRest : p ∈ B.rest := by
      rw [hrest]
      exact List.mem_append_right pre hmem
    exact (List.nodup_cons.mp B.nodup).1 hpRest
  have hsplit := splitFace_oldPath_retained H p q hpq q post hqPath
    hqClose hqNodup hpNot (Or.inl rfl)
  exact {
    first := ExtDart.new
    rest := (q :: post).map ExtDart.old
    path := by
      change K.FacePath ExtDart.new
        (ExtDart.old q :: post.map ExtDart.old)
      rw [Hypermap.FacePath.cons]
      refine ⟨?_, by simpa [hAB, K] using hsplit.1⟩
      rw [EdgeDeletion.addEdgeHypermap_face_apply_some_some H p q hAB hpq]
      exact EdgeDeletion.splitFacePerm_new H.face p q hpq
    close := by
      change K.face
        ((ExtDart.new :: (q :: post).map ExtDart.old).getLastD ExtDart.new) =
          ExtDart.new
      rw [getLastD_new_old_map]
      simpa [hAB, K] using hsplit.2
    nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, hqNodup.map (fun _ _ h => ExtDart.old.inj h)⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨z, _hz, hbad⟩
      cases hbad
  }

/-- The complementary old-face segment after inserting an edge between `p`
and `q`.  This is the prefix-side analogue of
`splitFace_oldPath_retained`: its last old dart is redirected to the opposite
new edge dart. -/
private theorem splitFace_oldPath_complementary
    (H : Hypermap.{u}) (p q : H.Dart)
    (hpq : p ≠ q)
    (x : H.Dart) (l : List H.Dart)
    (hpath : H.FacePath x l)
    (hclose : H.face ((x :: l).getLastD x) = q)
    (hnodup : (x :: l).Nodup)
    (hq : q ∉ x :: l)
    (hp : p = x ∨ p ∉ x :: l) :
    let hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
        (some q : Option H.Dart) ≠ some r :=
      fun r hpr hqr => hpq (by simpa using hpr.trans hqr.symm)
    let K := EdgeDeletion.addEdgeHypermap H (some p) (some q) hAB
    K.FacePath (ExtDart.old x) (l.map ExtDart.old) ∧
      K.face (ExtDart.old ((x :: l).getLastD x)) = ExtDart.newEdge := by
  let hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r :=
    fun r hpr hqr => hpq (by simpa using hpr.trans hqr.symm)
  let K := EdgeDeletion.addEdgeHypermap H (some p) (some q) hAB
  dsimp only
  induction l generalizing x with
  | nil =>
      have hxpred : x = H.face.symm q := by
        apply H.face.injective
        simpa using hclose
      have hxNotPredP : x ≠ H.face.symm p := by
        intro hx
        apply hpq
        calc
          p = H.face x := by rw [hx]; simp
          _ = q := by simpa using hclose
      constructor
      · exact Hypermap.FacePath.nil K (ExtDart.old x)
      · rw [show ([x]).getLastD x = x by rfl]
        rw [EdgeDeletion.addEdgeHypermap_face_apply_some_some H p q hAB hpq]
        simp [EdgeDeletion.splitFacePerm_old, hxpred, hpq.symm]
  | cons y l ih =>
      have hstep : H.face x = y :=
        ((Hypermap.FacePath.cons H x y l).mp hpath).1
      have htail : H.FacePath y l :=
        ((Hypermap.FacePath.cons H x y l).mp hpath).2
      have hyNodup : (y :: l).Nodup := hnodup.tail
      have hqTail : q ∉ y :: l := fun hmem => hq (by simp [hmem])
      have hpTail : p ∉ y :: l := by
        rcases hp with rfl | hpnot
        · exact (List.nodup_cons.mp hnodup).1
        · exact fun hmem => hpnot (by simp [hmem])
      have hxNotPredP : x ≠ H.face.symm p := by
        intro hx
        have hyp : y = p := by
          calc
            y = H.face x := hstep.symm
            _ = H.face (H.face.symm p) := by rw [hx]
            _ = p := by simp
        exact hpTail (by simp [hyp])
      have hxNotPredQ : x ≠ H.face.symm q := by
        intro hx
        have hyq : y = q := by
          calc
            y = H.face x := hstep.symm
            _ = H.face (H.face.symm q) := by rw [hx]
            _ = q := by simp
        exact hqTail (by simp [hyq])
      have hrec := ih y htail (by simpa using hclose) hyNodup hqTail
        (Or.inr hpTail)
      constructor
      · change K.FacePath (ExtDart.old x)
          (ExtDart.old y :: l.map ExtDart.old)
        rw [Hypermap.FacePath.cons]
        refine ⟨?_, hrec.1⟩
        rw [EdgeDeletion.addEdgeHypermap_face_apply_some_some H p q hAB hpq]
        simp [EdgeDeletion.splitFacePerm_old, hxNotPredP, hxNotPredQ, hstep]
      · simpa using hrec.2

/-- The second face created by `FaceBoundary.addEdgeRetained`.  Its directed
boundary is the opposite new chord dart followed by the old prefix from the
first cut point up to the second. -/
def FaceBoundary.addEdgeComplementary
    {H : Hypermap.{u}} (B : FaceBoundary H)
    (q : H.Dart) (pre post : List H.Dart)
    (hrest : B.rest = pre ++ q :: post) :
    let hpq : B.first ≠ q := by
      intro heq
      have hqmem : q ∈ B.rest := by rw [hrest]; simp
      apply (List.nodup_cons.mp B.nodup).1
      rw [heq]
      exact hqmem
    let hAB : forall r : H.Dart,
        (some B.first : Option H.Dart) = some r ->
          (some q : Option H.Dart) ≠ some r :=
      fun r hpr hqr => hpq (by simpa using hpr.trans hqr.symm)
    FaceBoundary
      (EdgeDeletion.addEdgeHypermap H (some B.first) (some q) hAB) := by
  let p := B.first
  have hpq : p ≠ q := by
    intro heq
    have hqmem : q ∈ B.rest := by rw [hrest]; simp
    apply (List.nodup_cons.mp B.nodup).1
    change p ∈ B.rest
    rw [heq]
    exact hqmem
  let hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r :=
    fun r hpr hqr => hpq (by simpa using hpr.trans hqr.symm)
  let K := EdgeDeletion.addEdgeHypermap H (some p) (some q) hAB
  have hpPath : H.FacePath p pre := by
    have hfull : H.FacePath p (pre ++ q :: post) := by
      simpa [p, hrest] using B.path
    exact (Hypermap.FacePath.split_append_cons (G := H) hfull).1
  have hpClose : H.face ((p :: pre).getLastD p) = q := by
    have hfull : H.FacePath p (pre ++ q :: post) := by
      simpa [p, hrest] using B.path
    exact (Hypermap.FacePath.split_append_cons (G := H) hfull).2.1
  have hpNodup : (p :: pre).Nodup := by
    have hfull : (p :: (pre ++ q :: post)).Nodup := by
      simpa [p, hrest] using B.nodup
    have hfull' : ((p :: pre) ++ q :: post).Nodup := by
      simpa [List.cons_append] using hfull
    exact hfull'.of_append_left
  have hqNot : q ∉ p :: pre := by
    have hfull : (p :: (pre ++ q :: post)).Nodup := by
      simpa [p, hrest] using B.nodup
    have hfull' : ((p :: pre) ++ q :: post).Nodup := by
      simpa [List.cons_append] using hfull
    have hdisjoint := (List.nodup_append.mp hfull').2.2
    intro hmem
    exact hdisjoint q hmem q (by simp) rfl
  have hsplit := splitFace_oldPath_complementary H p q hpq p pre hpPath
    hpClose hpNodup hqNot (Or.inl rfl)
  exact {
    first := ExtDart.newEdge
    rest := (p :: pre).map ExtDart.old
    path := by
      change K.FacePath ExtDart.newEdge
        (ExtDart.old p :: pre.map ExtDart.old)
      rw [Hypermap.FacePath.cons]
      refine ⟨?_, by simpa [hAB, K] using hsplit.1⟩
      rw [EdgeDeletion.addEdgeHypermap_face_apply_some_some H p q hAB hpq]
      exact EdgeDeletion.splitFacePerm_newEdge H.face p q hpq
    close := by
      change K.face
        ((ExtDart.newEdge :: (p :: pre).map ExtDart.old).getLastD
          ExtDart.newEdge) = ExtDart.newEdge
      have hlast :
          (ExtDart.newEdge :: (p :: pre).map ExtDart.old).getLastD
              ExtDart.newEdge =
            ExtDart.old ((p :: pre).getLastD p) := by
        change ((p :: pre).map ExtDart.old).getLastD (ExtDart.old p) =
          ExtDart.old ((p :: pre).getLastD p)
        exact List.getLastD_map
      rw [hlast]
      simpa [hAB, K] using hsplit.2
    nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, hpNodup.map (fun _ _ h => ExtDart.old.inj h)⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨z, _hz, hbad⟩
      cases hbad
  }


end RotationSystemFan

end FourColor

end Schematic.Math.GraphTheory
