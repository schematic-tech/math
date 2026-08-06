import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.FaceSimplicity

/-!
Transport of explicitly surviving face steps and paths through vertex deletion.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemVertexDeletion

theorem facePort_survives
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (x : OrientedEdge G) (hx : x.tail = v) :
    ((R.toHypermap).face x).tail ≠ v ∧
      ((R.toHypermap).face x).head ≠ v := by
  constructor
  · rw [RotationSystem.toHypermap_face_tail R x, ← hx]
    exact x.adj.symm.ne
  · intro hhead
    have htail :
        ((R.toHypermap).face x).tail = x.symm.tail := by
      rw [RotationSystem.toHypermap_face_tail R x]
      rfl
    have hhead' :
        ((R.toHypermap).face x).head = x.symm.head := by
      rw [hhead, ← hx]
      rfl
    have hfaceEq : (R.toHypermap).face x = x.symm := by
      apply Subtype.ext
      exact Prod.ext htail hhead'
    have hnodeFace :
        R.node ((R.toHypermap).face x) = x.symm := by
      simpa using (R.toHypermap.node_face_eq_edge_symm x)
    exact hnode x.symm (by simpa [hfaceEq] using hnodeFace)

/-- A surviving old face step remains a face step after deleting `v`. -/
theorem predicateRestriction_face_eq_of_face_survives
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (d : OrientedEdge G)
    (hd : d.tail ≠ v ∧ d.head ≠ v)
    (hface :
      ((R.toHypermap).face d).tail ≠ v ∧
        ((R.toHypermap).face d).head ≠ v) :
    let H := (R.toHypermap).predicateRestriction
      (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
    H.face (⟨d, hd⟩ : H.Dart) =
      (⟨(R.toHypermap).face d, hface⟩ : H.Dart) := by
  dsimp
  let H := (R.toHypermap).predicateRestriction
    (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
  let dSymm : H.Dart := ⟨d.symm, ⟨hd.2, hd.1⟩⟩
  have hnodeFace :
      R.node ((R.toHypermap).face d) = d.symm := by
    simpa using (R.toHypermap.node_face_eq_edge_symm d)
  have hnodeRestricted :
      H.node (⟨(R.toHypermap).face d, hface⟩ : H.Dart) = dSymm := by
    apply Subtype.ext
    change
      (PermSkipPredicate.skip
        (keep := fun e : OrientedEdge G =>
          e.tail ≠ v ∧ e.head ≠ v)
        R.node
        (⟨(R.toHypermap).face d, hface⟩ :
          {e : OrientedEdge G // e.tail ≠ v ∧ e.head ≠ v})).1 =
        d.symm
    rw [predicateSkipNode_eq_fiberSkip R v]
    simp [PermSkipFiber.skipAux, hnodeFace, hd.1]
  have hedge :
      H.edge dSymm = (⟨d, hd⟩ : H.Dart) := by
    apply Subtype.ext
    change
      (PermSkipPredicate.skip
        (keep := fun e : OrientedEdge G =>
          e.tail ≠ v ∧ e.head ≠ v)
        (OrientedEdge.edgePerm G) dSymm).1 = d
    rw [PermSkipPredicate.skip_apply_of_next_mem]
    · rfl
    · exact hd
  have hedgeSymm :
      H.edge.symm (⟨d, hd⟩ : H.Dart) = dSymm := by
    apply H.edge.injective
    simpa using hedge.symm
  apply H.node.injective
  rw [H.node_face_eq_edge_symm, hedgeSymm, hnodeRestricted]

/-- A face path all of whose darts survive vertex deletion remains connected
in the restricted face permutation. -/
theorem predicateRestriction_faceReachable_of_facePath_survives
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    {d : OrientedEdge G} {p : List (OrientedEdge G)}
    (hp : (R.toHypermap).FacePath d p)
    (hsurvives :
      ∀ z : OrientedEdge G, z ∈ d :: p →
        z.tail ≠ v ∧ z.head ≠ v) :
    let H := (R.toHypermap).predicateRestriction
      (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
    PermReachable H.face
      (⟨d, hsurvives d (by simp)⟩ : H.Dart)
      (⟨(d :: p).getLastD d,
        hsurvives ((d :: p).getLastD d)
          (by simp [List.getLastD])⟩ : H.Dart) := by
  classical
  induction p generalizing d with
  | nil =>
      exact PermReachable.refl _ _
  | cons e p ih =>
      have hp' :
          (R.toHypermap).face d = e ∧
            (R.toHypermap).FacePath e p := by
        simpa [Hypermap.FacePath] using hp
      have hd := hsurvives d (by simp)
      have he := hsurvives e (by simp)
      have htail :
          ∀ z : OrientedEdge G, z ∈ e :: p →
            z.tail ≠ v ∧ z.head ≠ v := by
        intro z hz
        exact hsurvives z (List.mem_cons_of_mem d hz)
      have hstep :
          let H := (R.toHypermap).predicateRestriction
            (fun z : OrientedEdge G => z.tail ≠ v ∧ z.head ≠ v)
          H.face (⟨d, hd⟩ : H.Dart) = (⟨e, he⟩ : H.Dart) := by
        simpa [hp'.1] using
          predicateRestriction_face_eq_of_face_survives
            R v d hd (by simpa [hp'.1] using he)
      have hrest := ih hp'.2 htail
      exact
        PermReachable.trans _ (by
          simpa only [hstep] using
            PermReachable.forward
              ((R.toHypermap).predicateRestriction
                (fun z : OrientedEdge G =>
                  z.tail ≠ v ∧ z.head ≠ v)).face
              (⟨d, hd⟩ :
                ((R.toHypermap).predicateRestriction
                  (fun z : OrientedEdge G =>
                    z.tail ≠ v ∧ z.head ≠ v)).Dart))
          (by simpa [List.getLastD] using hrest)

/-- Lift an explicitly surviving dart list to the dart type of the predicate
restriction used for vertex deletion. -/
noncomputable def survivingDartList
    {V : Type u} {G : SimpleGraph V} (v : V)
    (l : List (OrientedEdge G))
    (h : forall z : OrientedEdge G, z ∈ l ->
      z.tail ≠ v ∧ z.head ≠ v) :
    List {z : OrientedEdge G // z.tail ≠ v ∧ z.head ≠ v} :=
  l.attach.map fun z => ⟨z.1, h z.1 z.2⟩

@[simp]
theorem survivingDartList_map_val
    {V : Type u} {G : SimpleGraph V} (v : V)
    (l : List (OrientedEdge G))
    (h : forall z : OrientedEdge G, z ∈ l ->
      z.tail ≠ v ∧ z.head ≠ v) :
    (survivingDartList v l h).map Subtype.val = l := by
  unfold survivingDartList
  rw [List.map_map]
  simpa [Function.comp_def] using
    (List.attach_map_val (l := l) (f := id))

/-- A surviving old face path remains an explicitly ordered face path after
vertex deletion.  This strengthens the reachability-only interface above and
is useful when the surviving pieces of several old faces are spliced into one
new face boundary. -/
theorem predicateRestriction_facePath_of_facePath_survives
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    {d : OrientedEdge G} {p : List (OrientedEdge G)}
    (hp : (R.toHypermap).FacePath d p)
    (hsurvives :
      forall z : OrientedEdge G, z ∈ d :: p ->
        z.tail ≠ v ∧ z.head ≠ v) :
    let H := (R.toHypermap).predicateRestriction
      (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
    H.FacePath
      (⟨d, hsurvives d (by simp)⟩ : H.Dart)
      ((p.attach.map fun z =>
        (⟨z.1, hsurvives z.1 (List.mem_cons_of_mem d z.2)⟩ : H.Dart))) := by
  classical
  dsimp only
  induction p generalizing d with
  | nil =>
      simp
  | cons e p ih =>
      have hp' :
          (R.toHypermap).face d = e ∧
            (R.toHypermap).FacePath e p := by
        simpa [Hypermap.FacePath] using hp
      have hd := hsurvives d (by simp)
      have he := hsurvives e (by simp)
      have htail :
          forall z : OrientedEdge G, z ∈ e :: p ->
            z.tail ≠ v ∧ z.head ≠ v := by
        intro z hz
        exact hsurvives z (List.mem_cons_of_mem d hz)
      simp only [List.attach_cons, List.map_cons]
      rw [Hypermap.FacePath.cons]
      refine ⟨?_, ?_⟩
      · simpa [hp'.1] using
          predicateRestriction_face_eq_of_face_survives
            R v d hd (by simpa [hp'.1] using he)
      · simpa using ih hp'.2 htail

/-- Local deleted-pair face jump with the exact hypothesis actually used by
the permutation restriction: the sector entered after the two rejected darts
survives.  The global no-fixed-node assumption in
`predicateRestriction_face_after_deleted_pair` is merely one convenient way
to establish this local fact. -/
theorem predicateRestriction_face_after_deleted_pair_of_target_survives
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (x w : OrientedEdge G)
    (hx : x.tail = v)
    (hw : w.tail ≠ v ∧ w.head ≠ v)
    (hfaceW :
      (R.toHypermap).face w = (R.toHypermap).face.symm x)
    (htarget :
      let target := (R.toHypermap).face (R.node x)
      target.tail ≠ v ∧ target.head ≠ v) :
    let H := (R.toHypermap).predicateRestriction
      (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
    let target := (R.toHypermap).face (R.node x)
    H.face (⟨w, hw⟩ : H.Dart) =
      (⟨target, htarget⟩ : H.Dart) := by
  classical
  dsimp
  let H := (R.toHypermap).predicateRestriction
    (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
  let target : OrientedEdge G := (R.toHypermap).face (R.node x)
  let xPrev : OrientedEdge G := (R.toHypermap).face.symm x
  let wSymm : H.Dart := ⟨w.symm, ⟨hw.2, hw.1⟩⟩
  have hxPrev : xPrev = (R.node x).symm := by
    exact (R.toHypermap.edge_node_eq_face_symm x).symm
  have hxPrevRejected :
      Not (xPrev.tail ≠ v ∧ xPrev.head ≠ v) := by
    intro h
    apply h.2
    rw [hxPrev]
    exact (R.node_tail x).trans hx
  have hnodeTarget : R.node target = xPrev := by
    change
      R.node ((R.toHypermap).face (R.node x)) =
        (R.toHypermap).face.symm x
    simpa using (R.toHypermap.node_face_eq_edge_symm (R.node x))
  have hnodePrev : R.node xPrev = w.symm := by
    calc
      R.node xPrev = R.node ((R.toHypermap).face w) :=
        congrArg R.node hfaceW.symm
      _ = w.symm := by
        simpa using (R.toHypermap.node_face_eq_edge_symm w)
  have hnodeRestricted :
      H.node (⟨target, htarget⟩ : H.Dart) = wSymm := by
    apply Subtype.ext
    change
      (PermSkipPredicate.skip
        (keep := fun e : OrientedEdge G =>
          e.tail ≠ v ∧ e.head ≠ v)
        R.node
        (⟨target, htarget⟩ :
          {e : OrientedEdge G // e.tail ≠ v ∧ e.head ≠ v})).1 =
        w.symm
    calc
      (PermSkipPredicate.skip
          (keep := fun e : OrientedEdge G =>
            e.tail ≠ v ∧ e.head ≠ v)
          R.node
          (⟨target, htarget⟩ :
            {e : OrientedEdge G // e.tail ≠ v ∧ e.head ≠ v})).1 =
          ((R.node : OrientedEdge G -> OrientedEdge G)^[1 + 1])
            target := by
        apply PermSkipPredicate.skip_eq_of_first (n := 1)
        · simpa [Function.iterate_succ_apply, hnodeTarget, hnodePrev] using
            (show w.symm.tail ≠ v ∧ w.symm.head ≠ v from
              ⟨hw.2, hw.1⟩)
        · intro m hm
          by_contra hmNot
          have hmZero : m = 0 := by omega
          subst m
          apply hxPrevRejected
          simpa [Function.iterate_succ_apply, hnodeTarget] using hm
      _ = w.symm := by
        simp [Function.iterate_succ_apply, hnodeTarget, hnodePrev]
  have hedge : H.edge wSymm = (⟨w, hw⟩ : H.Dart) := by
    apply Subtype.ext
    change
      (PermSkipPredicate.skip
        (keep := fun e : OrientedEdge G =>
          e.tail ≠ v ∧ e.head ≠ v)
        (OrientedEdge.edgePerm G) wSymm).1 = w
    rw [PermSkipPredicate.skip_apply_of_next_mem]
    · rfl
    · exact hw
  have hedgeSymm :
      H.edge.symm (⟨w, hw⟩ : H.Dart) = wSymm := by
    apply H.edge.injective
    simpa using hedge.symm
  apply H.node.injective
  rw [H.node_face_eq_edge_symm, hedgeSymm, hnodeRestricted]


end RotationSystemVertexDeletion

end FourColor

end Schematic.Math.GraphTheory

