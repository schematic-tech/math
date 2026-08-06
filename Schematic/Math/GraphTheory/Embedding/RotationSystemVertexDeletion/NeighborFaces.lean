import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.FaceBoundaries

/-!
Wheel segments and neighbor-face reachability after vertex deletion.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemVertexDeletion

/-- Coq `hmap_ops.v::wheel_segment`: two consecutive sectors around a deleted
vertex belong to one face of the restricted hypermap. -/
theorem predicateRestriction_wheelSegment
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (hsimple : FaceOrbitsVertexSimple R)
    (x : OrientedEdge G) (hx : x.tail = v) :
    let H := (R.toHypermap).predicateRestriction
      (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
    PermReachable H.face
      (⟨(R.toHypermap).face x,
        facePort_survives R v hnode x hx⟩ : H.Dart)
      (⟨(R.toHypermap).face (R.node x),
        facePort_survives R v hnode (R.node x)
          ((R.node_tail x).trans hx)⟩ : H.Dart) := by
  classical
  let old := R.toHypermap
  let H := old.predicateRestriction
    (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
  let start : OrientedEdge G := old.face x
  let xPrev : OrientedEdge G := old.face.symm x
  have hstartSurvives :
      start.tail ≠ v ∧ start.head ≠ v :=
    facePort_survives R v hnode x hx
  have hxPrevEq :
      xPrev = (R.node x).symm := by
    exact (old.edge_node_eq_face_symm x).symm
  have hxPrevHead : xPrev.head = v := by
    rw [hxPrevEq]
    exact (R.node_tail x).trans hx
  have hxPrevNeStart : xPrev ≠ start := by
    intro h
    exact hstartSurvives.2 (by simpa [h] using hxPrevHead)
  have hxNeStart : x ≠ start := by
    intro h
    exact hstartSurvives.1 (by simpa [h] using hx)
  have hstartPrev :
      PermReachable old.face start xPrev := by
    have hstartX : PermReachable old.face start x := by
      simpa [start] using
        (PermReachable.backward old.face (old.face x))
    exact PermReachable.trans old.face hstartX
      (PermReachable.backward old.face x)
  rcases old.exists_ordered_faceOrbitCycle start with
    ⟨p, hp, hclose, hnodup, horbit⟩
  have hxPrevMemFull : xPrev ∈ start :: p :=
    (horbit xPrev).2 hstartPrev
  have hxPrevMem : xPrev ∈ p := by
    rw [List.mem_cons] at hxPrevMemFull
    exact hxPrevMemFull.resolve_left hxPrevNeStart
  rcases (List.mem_iff_append).1 hxPrevMem with
    ⟨pre, post, hpSplit⟩
  have hpAtPrev :
      old.FacePath start (pre ++ xPrev :: post) := by
    simpa [hpSplit] using hp
  rcases Hypermap.FacePath.split_append_cons
      (G := old) hpAtPrev with
    ⟨hprePath, hpreLast, hpostPath⟩
  have hxPrevFace : old.face xPrev = x := by
    simp [xPrev]
  have hpostNonempty : post ≠ [] := by
    intro hpost
    have hlastPrev :
        (start :: p).getLastD start = xPrev := by
      simp [hpSplit, hpost, List.getLastD]
    have : old.face xPrev = start := by
      rw [← hlastPrev]
      exact hclose
    exact hxNeStart (hxPrevFace.symm.trans this)
  rcases List.exists_cons_of_ne_nil hpostNonempty with ⟨y, rest, rfl⟩
  have hy : y = x := by
    have := (Hypermap.FacePath.cons
      (G := old) xPrev y rest).mp hpostPath
    exact this.1.symm.trans hxPrevFace
  subst y
  have hrestEmpty : rest = [] := by
    cases rest with
    | nil =>
        rfl
    | cons z rest =>
        have hzStart : z = start := by
          have htailPath :=
            (Hypermap.FacePath.cons
              (G := old) xPrev x (z :: rest)).mp hpostPath |>.2
          have hstep :=
            (Hypermap.FacePath.cons
              (G := old) x z rest).mp htailPath |>.1
          exact hstep.symm
        have hstartNotTail :
            start ∉ pre ++ xPrev :: x :: z :: rest := by
          have hfull :
              (start :: pre ++ xPrev :: x :: z :: rest).Nodup := by
            have heq :
                start :: p =
                  (start :: pre) ++ xPrev :: x :: z :: rest := by
              rw [hpSplit, List.cons_append]
            rw [← heq]
            exact hnodup
          exact (List.nodup_cons.mp hfull).1
        apply False.elim
        apply hstartNotTail
        simp [hzStart]
  subst rest
  have hpFinal : p = pre ++ [xPrev, x] := by
    simp [hpSplit]
  have hfullNodup :
      ((start :: pre) ++ [xPrev, x]).Nodup := by
    change (start :: (pre ++ [xPrev, x])).Nodup
    rw [← hpFinal]
    exact hnodup
  have hcross :
      ∀ a ∈ start :: pre, ∀ b ∈ [xPrev, x], a ≠ b :=
    (List.nodup_append.mp hfullNodup).2.2
  have hprefixSurvives :
      ∀ z : OrientedEdge G, z ∈ start :: pre →
        z.tail ≠ v ∧ z.head ≠ v := by
    intro z hz
    have hzReachStart :
        PermReachable old.face start z := by
      apply (horbit z).1
      rw [hpFinal]
      exact List.mem_append_left [xPrev, x] hz
    have hzReachX :
        PermReachable old.face z x := by
      exact PermReachable.trans old.face
        (PermReachable.symm old.face hzReachStart)
        (by
          apply (horbit x).1
          rw [hpFinal, List.mem_cons]
          exact Or.inr
            (List.mem_append_right pre (by simp)))
    have hzReachPrev :
        PermReachable old.face z xPrev := by
      exact PermReachable.trans old.face
        (PermReachable.symm old.face hzReachStart)
        (by
          apply (horbit xPrev).1
          rw [hpFinal, List.mem_cons]
          exact Or.inr
            (List.mem_append_right pre (by simp)))
    constructor
    · intro hzv
      have hzx : z = x :=
        (hsimple hzReachX).1 (hzv.trans hx.symm)
      exact hcross z hz x (by simp) hzx
    · intro hzv
      have hzPrev : z = xPrev :=
        (hsimple hzReachPrev).2 (hzv.trans hxPrevHead.symm)
      exact hcross z hz xPrev (by simp) hzPrev
  let w : OrientedEdge G := (start :: pre).getLastD start
  have hwEq : w = pre.getLastD start := by
    exact List.getLastD_cons
  have hwMem : w ∈ start :: pre := by
    rw [hwEq]
    exact List.getLastD_mem_cons
  have hw : w.tail ≠ v ∧ w.head ≠ v :=
    hprefixSurvives w hwMem
  have hprefixReach :
      PermReachable H.face
        (⟨start, hstartSurvives⟩ : H.Dart)
        (⟨w, hw⟩ : H.Dart) := by
    simpa only [w] using
      (predicateRestriction_faceReachable_of_facePath_survives
        R v hprePath hprefixSurvives)
  have hjump :
      H.face (⟨w, hw⟩ : H.Dart) =
        (⟨old.face (R.node x),
          facePort_survives R v hnode (R.node x)
            ((R.node_tail x).trans hx)⟩ : H.Dart) := by
    apply predicateRestriction_face_after_deleted_pair
      R v hnode x w hx hw
    simpa [old, xPrev, w] using hpreLast
  exact PermReachable.trans H.face hprefixReach
    (by simpa only [hjump] using
      PermReachable.forward H.face (⟨w, hw⟩ : H.Dart))

/-- Coq `hmap_ops.v::neighbor_face_aux`: after deleting `v`, the surviving
face ports of any two darts based at `v` belong to the same face. -/
theorem predicateRestriction_neighborFaceAux
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (hsimple : FaceOrbitsVertexSimple R)
    (x y : OrientedEdge G)
    (hx : x.tail = v) (hy : y.tail = v) :
    let H := (R.toHypermap).predicateRestriction
      (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
    PermReachable H.face
      (⟨(R.toHypermap).face x,
        facePort_survives R v hnode x hx⟩ : H.Dart)
      (⟨(R.toHypermap).face y,
        facePort_survives R v hnode y hy⟩ : H.Dart) := by
  classical
  let H := (R.toHypermap).predicateRestriction
    (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
  have hxy : PermReachable R.node x y :=
    R.node_orbit_of_same_tail x y (hx.trans hy.symm)
  rcases permReachable_exists_iterate R.node hxy with ⟨n, hn⟩
  have hiterTail :
      ∀ k : Nat, ((R.node : OrientedEdge G → OrientedEdge G)^[k] x).tail = v := by
    intro k
    induction k with
    | zero =>
        simpa using hx
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (R.node_tail _).trans ih
  have hiterReach :
      ∀ k : Nat,
        PermReachable H.face
          (⟨(R.toHypermap).face x,
            facePort_survives R v hnode x hx⟩ : H.Dart)
          (⟨(R.toHypermap).face
              ((R.node : OrientedEdge G → OrientedEdge G)^[k] x),
            facePort_survives R v hnode
              ((R.node : OrientedEdge G → OrientedEdge G)^[k] x)
              (hiterTail k)⟩ : H.Dart) := by
    intro k
    induction k with
    | zero =>
        exact PermReachable.refl H.face _
    | succ k ih =>
        have hstep :=
          predicateRestriction_wheelSegment R v hnode hsimple
            ((R.node : OrientedEdge G → OrientedEdge G)^[k] x)
            (hiterTail k)
        exact PermReachable.trans H.face ih (by
          simpa only [Function.iterate_succ_apply'] using hstep)
  simpa only [hn] using hiterReach n

/-- The surviving face port at `x`, regarded as a dart of the explicit
vertex-deleted graph. -/
noncomputable def vertexDeletedFacePort
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (x : OrientedEdge G) (hx : x.tail = v) :
    OrientedEdge (G.induce {z : V | z ≠ v}) :=
  (vertexDeletedPredicateDartEquiv v).symm
    ⟨(R.toHypermap).face x,
      facePort_survives R v hnode x hx⟩

@[simp]
theorem vertexDeletedPredicateDartEquiv_vertexDeletedFacePort
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (x : OrientedEdge G) (hx : x.tail = v) :
    vertexDeletedPredicateDartEquiv v
        (vertexDeletedFacePort R v hnode x hx) =
      ⟨(R.toHypermap).face x,
        facePort_survives R v hnode x hx⟩ := by
  exact (vertexDeletedPredicateDartEquiv v).apply_symm_apply _

@[simp]
theorem vertexDeletedFacePort_tail_val
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (x : OrientedEdge G) (hx : x.tail = v) :
    ((vertexDeletedFacePort R v hnode x hx).tail : V) = x.head := by
  have h := congrArg
    (fun e : {d : OrientedEdge G // d.tail ≠ v ∧ d.head ≠ v} => e.1.tail)
    (vertexDeletedPredicateDartEquiv_vertexDeletedFacePort
      R v hnode x hx)
  simpa [vertexDeletedPredicateDartEquiv] using h

/-- Explicit graph-rotation form of Coq `neighbor_face_aux`. -/
theorem vertexDeletedFacePort_faceReachable
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (hsimple : FaceOrbitsVertexSimple R)
    (x y : OrientedEdge G)
    (hx : x.tail = v) (hy : y.tail = v) :
    PermReachable
      ((vertexDeletedRotationSystem R v).toHypermap).face
      (vertexDeletedFacePort R v hnode x hx)
      (vertexDeletedFacePort R v hnode y hy) := by
  let φ :=
    vertexDeletedRotationSystem_toPredicateRestrictionIso R v
  apply (φ.faceReachable_iff).mpr
  simpa [φ] using
    predicateRestriction_neighborFaceAux
      R v hnode hsimple x y hx hy

/-- A rotation node has no fixed dart in a finite two-connected graph.  After
deleting the head of a dart, connectivity supplies a second edge at its tail,
and both darts lie in the same node orbit. -/
theorem node_ne_self_of_isTwoConnected
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (h2 : IsTwoConnected G) :
    ∀ d : OrientedEdge G, R.node d ≠ d := by
  classical
  intro d hfixed
  let pair : Set V := {d.tail, d.head}
  have hpairCard : pair.ncard ≤ 2 := by
    exact le_of_eq (by simpa [pair] using Set.ncard_pair d.adj.ne)
  have hpairNeUniv : pair ≠ Set.univ := by
    intro hpair
    have hpairEq : pair.ncard = Nat.card V := by
      rw [hpair]
      simp
    have hunivLe : Nat.card V ≤ 2 := by omega
    exact (not_lt_of_ge hunivLe) h2.1
  have hpairCompl : pairᶜ.Nonempty :=
    Set.ssubset_univ_iff_nonempty_compl.mp
      (Set.ssubset_univ_iff.mpr hpairNeUniv)
  rcases hpairCompl with ⟨w, hw⟩
  have hwNot : w ∉ pair := by
    simpa using hw
  have hwt : w ≠ d.tail := by
    intro h
    apply hwNot
    simp [pair, h]
  have hwh : w ≠ d.head := by
    intro h
    apply hwNot
    simp [pair, h]
  have hdeleted :
      (G.induce ({d.head} : Set V)ᶜ).Connected :=
    h2.2 ({d.head} : Set V) (by simp)
  let u' : (({d.head} : Set V)ᶜ : Set V) :=
    ⟨d.tail, by simpa using d.adj.ne⟩
  let w' : (({d.head} : Set V)ᶜ : Set V) :=
    ⟨w, by simpa using hwh⟩
  have hwu : w' ≠ u' := by
    intro h
    apply hwt
    simpa [w', u'] using
      congrArg (fun z : (({d.head} : Set V)ᶜ : Set V) => (z : V)) h
  rcases Connected.exists_adjacent_crossing
      (G := G.induce ({d.head} : Set V)ᶜ)
      hdeleted
      (S := ({u'} : Set (({d.head} : Set V)ᶜ : Set V)))
      ⟨u', by simp⟩ ⟨w', by simpa using hwu⟩ with
    ⟨a, ha, b, hb, hab⟩
  have haEq : a = u' := by
    simpa using ha
  have hab' : G.Adj d.tail (b : V) := by
    simpa [haEq, u'] using hab
  let f : OrientedEdge G :=
    ⟨(d.tail, (b : V)), hab'⟩
  have hfHeadNe : f.head ≠ d.head := by
    change (b : V) ≠ d.head
    have hbNot : (b : V) ∉ ({d.head} : Set V) :=
      b.property
    intro h
    exact hbNot (by simp [h])
  have hfd : f ≠ d := by
    intro h
    exact hfHeadNe (congrArg (fun e : OrientedEdge G => e.head) h)
  have hdf : PermReachable R.node d f :=
    R.node_orbit_of_same_tail d f (by
      change d.tail = d.tail
      rfl)
  have hfdEq : f = d :=
    PermSkip.eq_of_permReachable_fixed R.node hfixed
      (PermReachable.symm R.node hdf)
  exact hfd hfdEq

/-- Coq `embedding.v::del_vertex_neighbor_face`, stated for the explicit
rotation system on the graph with one vertex deleted. -/
theorem vertexDeletedFacePort_faceReachable_of_isTwoConnected_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (h2 : IsTwoConnected G)
    (hR : (R.toHypermap).EulerPlanar)
    (v : V) (x y : OrientedEdge G)
    (hx : x.tail = v) (hy : y.tail = v) :
    PermReachable
      ((vertexDeletedRotationSystem R v).toHypermap).face
      (vertexDeletedFacePort R v
        (node_ne_self_of_isTwoConnected R h2) x hx)
      (vertexDeletedFacePort R v
        (node_ne_self_of_isTwoConnected R h2) y hy) := by
  exact
    vertexDeletedFacePort_faceReachable R v
      (node_ne_self_of_isTwoConnected R h2)
      (faceOrbitsVertexSimple_of_isTwoConnected_eulerPlanar R h2 hR)
      x y hx hy

/-- Dual-planarity form used by `HasEulerRotationSystem`. -/
theorem vertexDeletedFacePort_faceReachable_of_isTwoConnected_dualEulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (h2 : IsTwoConnected G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    (v : V) (x y : OrientedEdge G)
    (hx : x.tail = v) (hy : y.tail = v) :
    PermReachable
      ((vertexDeletedRotationSystem R v).toHypermap).face
      (vertexDeletedFacePort R v
        (node_ne_self_of_isTwoConnected R h2) x hx)
      (vertexDeletedFacePort R v
        (node_ne_self_of_isTwoConnected R h2) y hy) := by
  apply
    vertexDeletedFacePort_faceReachable_of_isTwoConnected_eulerPlanar
      R h2
  exact (R.toHypermap.dual_eulerPlanar_iff).mp hR


end RotationSystemVertexDeletion

end FourColor

end Schematic.Math.GraphTheory
