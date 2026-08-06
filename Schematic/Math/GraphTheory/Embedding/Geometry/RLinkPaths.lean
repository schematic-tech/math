import Schematic.Math.GraphTheory.Embedding.Geometry.FacePaths

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- Coq `rlink x y`: the face of `edge x` reaches `y`.  This belongs in the
geometry layer because the `snip.v`/`revsnip.v` disk lemmas are stated for
simple `rlink` cycles before the embedding-extension layer. -/
def RLink (x y : G.Dart) : Prop :=
  PermReachable G.face (G.edge x) y

theorem RLink.self_edge (x : G.Dart) :
    G.RLink x (G.edge x) :=
  PermReachable.refl G.face (G.edge x)

theorem RLink.of_faceReachable_right
    {x y z : G.Dart}
    (hxy : G.RLink x y)
    (hyz : PermReachable G.face y z) :
    G.RLink x z :=
  PermReachable.trans G.face hxy hyz

theorem RLink.node_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.RLink (G.node x) y := by
  unfold RLink
  rw [Hypermap.edge_node_eq_face_symm]
  exact PermReachable.trans G.face
    (by
      simpa using
        PermReachable.forward G.face (G.face.symm x))
    hxy

theorem RLink.node_self (x : G.Dart) :
    G.RLink (G.node x) x :=
  RLink.node_of_faceReachable (G := G)
    (PermReachable.refl G.face x)

theorem RLink.node_face_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.RLink (G.node (G.face x)) y := by
  unfold RLink
  rw [Hypermap.edge_node_eq_face_symm]
  simpa using hxy

theorem RLink.edge_self_of_plain
    (hPlain : G.Plain) (x : G.Dart) :
    G.RLink (G.edge x) x := by
  unfold RLink
  rw [Plain.edge_edge (G := G) hPlain x]
  exact PermReachable.refl G.face x

theorem RLink.face_edge_reachable
    {z y : G.Dart}
    (hzy : G.RLink z y) :
    PermReachable G.face y (G.face (G.edge z)) :=
  PermReachable.trans G.face
    (PermReachable.symm G.face hzy)
    (PermReachable.forward G.face (G.edge z))

theorem RLink.face_edge_source_reachable
    {x y : G.Dart}
    (hxy : G.RLink x y) :
    PermReachable G.face (G.face (G.edge x)) y := by
  have hback :
      PermReachable G.face (G.face (G.edge x)) (G.edge x) := by
    simpa using PermReachable.backward G.face (G.face (G.edge x))
  exact PermReachable.trans G.face hback hxy

theorem RLink.exists_short_facePath_from_face_edge
    [Fintype G.Dart]
    {x y : G.Dart}
    (hxy : G.RLink x y) :
    ∃ p : List G.Dart,
      G.FacePath (G.face (G.edge x)) p ∧
        (G.face (G.edge x) :: p).getLastD (G.face (G.edge x)) = y ∧
          (G.face (G.edge x) :: p).Nodup :=
  G.exists_short_facePath_of_faceReachable
    (RLink.face_edge_source_reachable (G := G) hxy)

/-- A finite Coq `rlink` path, represented by its successive endpoint list.
This is the geometry-level path notion used by the ring/Jordan layer. -/
def RLinkPath (G : Hypermap.{u}) (x : G.Dart) : List G.Dart → Prop
  := List.RelPath G.RLink x

@[simp]
theorem RLinkPath.nil (x : G.Dart) :
    G.RLinkPath x [] := by
  simp [RLinkPath]

@[simp]
theorem RLinkPath.cons (x y : G.Dart) (p : List G.Dart) :
    G.RLinkPath x (y :: p) ↔ G.RLink x y ∧ G.RLinkPath y p := by
  rfl

theorem RLinkPath.singleton
    {x y : G.Dart}
    (hxy : G.RLink x y) :
    G.RLinkPath x [y] := by
  simp [RLinkPath, hxy]

theorem RLinkPath.snoc
    {x y z : G.Dart}
    (p : List G.Dart)
    (hp : G.RLinkPath x (p ++ [y]))
    (hyz : G.RLink y z) :
    G.RLinkPath x (p ++ [y, z]) := by
  simpa [List.append_assoc] using
    List.RelPath.snoc hp
      (List.getLastD_cons_append_singleton x y p) hyz

theorem RLinkPath.snoc_last
    {x z : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x p)
    (hz : G.RLink ((x :: p).getLastD x) z) :
    G.RLinkPath x (p ++ [z]) :=
  List.RelPath.snoc hp rfl hz

/-- Prefix extraction for finite `rlink` paths. -/
theorem RLinkPath.prefix_of_append
    {x : G.Dart} {p q : List G.Dart}
    (hp : G.RLinkPath x (p ++ q)) :
    G.RLinkPath x p :=
  List.RelPath.prefix_of_append hp

theorem RLinkPath.suffix_of_append_cons
    {x y : G.Dart} {p q : List G.Dart}
    (hp : G.RLinkPath x (p ++ y :: q)) :
    G.RLinkPath y q :=
  List.RelPath.suffix_of_append hp

/-- The link from the last dart of a displayed prefix to the next displayed
dart in an `rlink` path. -/
theorem RLinkPath.last_link_of_append_cons
    {x y : G.Dart} {p q : List G.Dart}
    (hp : G.RLinkPath x (p ++ y :: q)) :
    G.RLink ((x :: p).getLastD x) y :=
  List.RelPath.last_rel_of_append_cons hp

theorem RLinkPath.to_reflTransGen
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x (p ++ [y])) :
    Relation.ReflTransGen (fun a b : G.Dart => G.RLink a b) x y :=
  List.RelPath.to_reflTransGen hp

/-- Coq `cycle rlink r`: a nonempty closed `rlink` path around the ring. -/
def RLinkCycle : List G.Dart → Prop
  | [] => False
  | x :: p => G.RLinkPath x p ∧ G.RLink ((x :: p).getLastD x) x

theorem RLinkCycle.cons
    {x : G.Dart} {p : List G.Dart} :
    G.RLinkCycle (x :: p) ↔
      G.RLinkPath x p ∧ G.RLink ((x :: p).getLastD x) x := by
  rfl

theorem RLinkCycle.nonempty
    {r : List G.Dart}
    (hr : G.RLinkCycle r) :
    r ≠ [] := by
  cases r with
  | nil =>
      contradiction
  | cons _ _ =>
      simp

theorem RLinkCycle.path
    {x : G.Dart} {p : List G.Dart}
    (hr : G.RLinkCycle (x :: p)) :
    G.RLinkPath x p :=
  hr.1

theorem RLinkCycle.closing
    {x : G.Dart} {p : List G.Dart}
    (hr : G.RLinkCycle (x :: p)) :
    G.RLink ((x :: p).getLastD x) x :=
  hr.2

theorem RLinkCycle.rotate_one
    {r : List G.Dart}
    (hr : G.RLinkCycle r) :
    G.RLinkCycle (r.rotate 1) := by
  cases r with
  | nil =>
      exact hr
  | cons x p =>
      cases p with
      | nil =>
          simpa using hr
      | cons y p =>
          have hxy : G.RLink x y := by
            exact hr.1.1
          have htail : G.RLinkPath y p := by
            exact hr.1.2
          have hclose : G.RLink ((y :: p).getLastD y) x := by
            simpa [List.getLastD] using hr.2
          have hpath : G.RLinkPath y (p ++ [x]) :=
            RLinkPath.snoc_last (G := G) htail hclose
          have hclosing : G.RLink ((y :: (p ++ [x])).getLastD y) y := by
            rw [List.getLastD_cons_append_singleton y x p]
            exact hxy
          have hcycle : G.RLinkCycle (y :: (p ++ [x])) :=
            ⟨hpath, hclosing⟩
          simpa [List.rotate_cons_succ] using hcycle

theorem RLinkCycle.rotate
    (n : Nat) {r : List G.Dart}
    (hr : G.RLinkCycle r) :
    G.RLinkCycle (r.rotate n) := by
  induction n with
  | zero =>
      simpa using hr
  | succ n ih =>
      have h := RLinkCycle.rotate_one (G := G) ih
      simpa [Nat.succ_eq_add_one, List.rotate_rotate] using h

theorem FacePath.to_RCLPath_of_sources_avoid_ring
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hnodup : (x :: p).Nodup)
    (havoid :
      ∀ y : G.Dart, y ∈ x :: p →
        y ≠ (x :: p).getLastD x → y ∉ r) :
    G.RCLPath r x p := by
  induction p generalizing x with
  | nil =>
      simp [RCLPath]
  | cons y p ih =>
      have hp' : G.face x = y ∧ G.FacePath y p := by
        simpa [FacePath] using hp
      have hnodupTail : (y :: p).Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      have hx_ne_last : x ≠ (x :: y :: p).getLastD x := by
        intro hxlast
        have hlastTail : (x :: y :: p).getLastD x ∈ y :: p :=
          List.getLastD_cons_cons_mem_tail x y p
        have hxTail : x ∈ y :: p := by
          rw [hxlast]
          exact hlastTail
        exact (List.nodup_cons.mp hnodup).1 hxTail
      have hxNot : x ∉ r :=
        havoid x (by simp) hx_ne_last
      refine ⟨?_, ?_⟩
      · simp [RCLStep, hxNot, hp'.1]
      · apply ih hp'.2 hnodupTail
        intro z hz z_ne_last
        apply havoid z
        · simp [hz]
        · intro hzlast
          apply z_ne_last
          simpa [List.getLastD] using hzlast

theorem FacePath.mem_faceReachable
    {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    {y : G.Dart}
    (hy : y ∈ x :: p) :
    PermReachable G.face x y := by
  induction p generalizing x with
  | nil =>
      simp at hy
      subst y
      exact PermReachable.refl G.face x
  | cons z p ih =>
      have hp' : G.face x = z ∧ G.FacePath z p := by
        simpa [FacePath] using hp
      rw [List.mem_cons] at hy
      rcases hy with hy | hy
      · subst y
        exact PermReachable.refl G.face x
      · have hxz : PermReachable G.face x z := by
          simpa [hp'.1] using PermReachable.forward G.face x
        exact PermReachable.trans G.face hxz (ih hp'.2 hy)

theorem FacePath.last_faceReachable
    {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p) :
    PermReachable G.face x ((x :: p).getLastD x) :=
  FacePath.mem_faceReachable (G := G) hp
    (List.getLastD_cons_mem x p)

theorem FacePath.faceBand_subset_singleton_last
    {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p) :
    ∀ u : G.Dart,
      G.FaceBand (x :: p) u →
        G.FaceBand [(x :: p).getLastD x] u := by
  intro u hu
  rcases hu with ⟨y, hy, hyu⟩
  have hxy : PermReachable G.face x y :=
    FacePath.mem_faceReachable (G := G) hp hy
  have hxl : PermReachable G.face x ((x :: p).getLastD x) :=
    FacePath.last_faceReachable (G := G) hp
  rw [FaceBand.singleton]
  exact PermReachable.trans G.face
    (PermReachable.trans G.face (PermReachable.symm G.face hxl) hxy)
    hyu

theorem FacePath.faceReachable_of_faceReachable_last
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hylast : PermReachable G.face y ((x :: p).getLastD x)) :
    ∀ z : G.Dart, z ∈ x :: p → PermReachable G.face y z := by
  intro z hz
  have hxz : PermReachable G.face x z :=
    FacePath.mem_faceReachable (G := G) hp hz
  have hxlast : PermReachable G.face x ((x :: p).getLastD x) :=
    FacePath.last_faceReachable (G := G) hp
  exact PermReachable.trans G.face
    (PermReachable.trans G.face hylast
      (PermReachable.symm G.face hxlast))
    hxz

theorem FacePath.faceReachable_of_faceReachable_last_eq
    {x y z : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hlast : (x :: p).getLastD x = z)
    (hyz : PermReachable G.face y z) :
    ∀ t : G.Dart, t ∈ x :: p → PermReachable G.face y t := by
  have hlast' : (x :: p).getLast?.getD x = z := by
    simpa [List.getLastD] using hlast
  apply FacePath.faceReachable_of_faceReachable_last (G := G) hp
  simpa [hlast'] using hyz

theorem FacePath.faceReachable_of_faceReachable_face_last
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hyfaceLast :
      PermReachable G.face y (G.face ((x :: p).getLastD x))) :
    ∀ z : G.Dart, z ∈ x :: p → PermReachable G.face y z := by
  apply FacePath.faceReachable_of_faceReachable_last (G := G) hp
  exact PermReachable.trans G.face hyfaceLast
    (PermReachable.symm G.face
      (PermReachable.forward G.face ((x :: p).getLastD x)))

theorem FacePath.faceReachable_of_faceReachable_face_last_eq
    {x y z : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hfaceLast : G.face ((x :: p).getLastD x) = z)
    (hyz : PermReachable G.face y z) :
    ∀ t : G.Dart, t ∈ x :: p → PermReachable G.face y t := by
  have hfaceLast' : G.face ((x :: p).getLast?.getD x) = z := by
    simpa [List.getLastD] using hfaceLast
  apply FacePath.faceReachable_of_faceReachable_face_last (G := G) hp
  simpa [hfaceLast'] using hyz

theorem FacePath.mem_of_faceReachable_closed
    [Fintype G.Dart]
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hclose : G.face ((x :: p).getLastD x) = x)
    (hxy : PermReachable G.face x y) :
    y ∈ x :: p := by
  rcases permReachable_exists_iterate G.face hxy with ⟨n, hn⟩
  rw [← hn]
  exact FacePath.iterate_mem_of_closed (G := G) hp hclose n

theorem FacePath.mem_iff_faceReachable_closed
    [Fintype G.Dart]
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hclose : G.face ((x :: p).getLastD x) = x) :
    y ∈ x :: p ↔ PermReachable G.face x y := by
  constructor
  · exact FacePath.mem_faceReachable (G := G) hp
  · exact FacePath.mem_of_faceReachable_closed (G := G) hp hclose

theorem FacePath.suffix_avoids_ring_of_prior_ring_hit
    {r : List G.Dart} {x z y : G.Dart} {pre post : List G.Dart}
    (hr : G.FaceSimple r)
    (hnodup : (x :: (pre ++ z :: post)).Nodup)
    (hyPre : y ∈ x :: pre)
    (hyR : y ∈ r)
    (hyz : PermReachable G.face y z)
    (hpost : G.FacePath z post) :
    ∀ t : G.Dart, t ∈ z :: post → t ∉ r := by
  have hfull :
      ((x :: pre) ++ (z :: post)).Nodup := by
    simpa [List.cons_append, List.append_assoc] using hnodup
  have hdisj := (List.nodup_append.mp hfull).2.2
  intro t ht htR
  have hzt : PermReachable G.face z t :=
    FacePath.mem_faceReachable (G := G) hpost ht
  have hyt : PermReachable G.face y t :=
    PermReachable.trans G.face hyz hzt
  have hytEq : y = t :=
    FaceSimple.eq_of_faceReachable_of_mem (G := G) hr hyR htR hyt
  exact hdisj y hyPre t ht hytEq

theorem FacePath.mem_face_edge_of_rlink_closed
    [Fintype G.Dart]
    {x y z : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hclose : G.face ((x :: p).getLastD x) = x)
    (hy : y ∈ x :: p)
    (hzy : G.RLink z y) :
    G.face (G.edge z) ∈ x :: p := by
  have hxy : PermReachable G.face x y :=
    FacePath.mem_faceReachable (G := G) hp hy
  exact FacePath.mem_of_faceReachable_closed (G := G) hp hclose
    (PermReachable.trans G.face hxy
      (RLink.face_edge_reachable (G := G) hzy))

theorem FacePath.mem_face_edge_of_rlink_last_edge
    [Fintype G.Dart]
    {x y z : G.Dart} {p : List G.Dart}
    (hp : G.FacePath (G.face (G.edge x)) p)
    (hlast :
      (G.face (G.edge x) :: p).getLastD (G.face (G.edge x)) =
        G.edge x)
    (hy : y ∈ G.face (G.edge x) :: p)
    (hzy : G.RLink z y) :
    G.face (G.edge z) ∈ G.face (G.edge x) :: p := by
  have hclose :
      G.face
          ((G.face (G.edge x) :: p).getLastD
            (G.face (G.edge x))) =
        G.face (G.edge x) := by
    rw [hlast]
  exact FacePath.mem_face_edge_of_rlink_closed
    (G := G) hp hclose hy hzy

theorem FacePath.exists_first_tail_mem
    [DecidableEq G.Dart]
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hx : x ∉ r)
    (hhit : ∃ y : G.Dart, y ∈ x :: p ∧ y ∈ r) :
    ∃ pre : List G.Dart, ∃ y : G.Dart, ∃ post : List G.Dart,
      p = pre ++ y :: post ∧
        y ∈ r ∧
          (∀ z : G.Dart, z ∈ pre → z ∉ r) ∧
            G.FacePath x pre ∧
              G.face ((x :: pre).getLastD x) = y ∧
                G.FacePath y post := by
  rcases list_exists_first_tail_mem_of_head_not_mem
      (c := r) (xs := p) (x := x) hx hhit with
    ⟨pre, y, post, hsplit, hyR, hpre⟩
  have hpSplit : G.FacePath x (pre ++ y :: post) := by
    simpa [hsplit] using hp
  rcases FacePath.split_append_cons (G := G) hpSplit with
    ⟨hprefix, hlink, hsuffix⟩
  exact ⟨pre, y, post, hsplit, hyR, hpre, hprefix, hlink, hsuffix⟩

theorem FacePath.exists_split_at_tail_mem
    {x z : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hz : z ∈ p) :
    ∃ pre : List G.Dart, ∃ post : List G.Dart,
      p = pre ++ z :: post ∧
        G.FacePath x pre ∧
          G.face ((x :: pre).getLastD x) = z ∧
            G.FacePath z post ∧
              (z :: post).getLastD z = (x :: p).getLastD x := by
  rcases (List.mem_iff_append).1 hz with ⟨pre, post, hsplit⟩
  have hpSplit : G.FacePath x (pre ++ z :: post) := by
    simpa [hsplit] using hp
  rcases FacePath.split_append_cons (G := G) hpSplit with
    ⟨hprefix, hlink, hsuffix⟩
  refine ⟨pre, post, hsplit, hprefix, hlink, hsuffix, ?_⟩
  rw [hsplit]
  exact (List.getLastD_cons_append_cons x z pre post).symm

theorem FacePath.exists_prefix_append_singleton_at_tail_mem
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hy : y ∈ p) :
    ∃ pre : List G.Dart, ∃ post : List G.Dart,
      p = pre ++ y :: post ∧
        G.FacePath x (pre ++ [y]) ∧
          (x :: (pre ++ [y])).getLastD x = y ∧
            G.FacePath y post := by
  rcases (List.mem_iff_append).1 hy with ⟨pre, post, hsplit⟩
  have hpSplit : G.FacePath x (pre ++ y :: post) := by
    simpa [hsplit] using hp
  rcases FacePath.prefix_append_singleton_of_split (G := G) hpSplit with
    ⟨hprefix, hlast, hsuffix⟩
  exact ⟨pre, post, hsplit, hprefix, hlast, hsuffix⟩

theorem FacePath.to_RCLPath_of_faceSimple_last_mem
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hr : G.FaceSimple r)
    (hp : G.FacePath x p)
    (hnodup : (x :: p).Nodup)
    (hlast : (x :: p).getLastD x ∈ r) :
    G.RCLPath r x p := by
  apply FacePath.to_RCLPath_of_sources_avoid_ring
      (G := G) (r := r) hp hnodup
  intro y hy hne hyRing
  have hxy : PermReachable G.face x y :=
    FacePath.mem_faceReachable (G := G) hp hy
  have hxlast : PermReachable G.face x ((x :: p).getLastD x) :=
    FacePath.last_faceReachable (G := G) hp
  have hylast : PermReachable G.face y ((x :: p).getLastD x) :=
    PermReachable.trans G.face (PermReachable.symm G.face hxy) hxlast
  have hyEq :
      y = (x :: p).getLastD x :=
    FaceSimple.eq_of_faceReachable_of_mem (G := G) hr
      hyRing hlast hylast
  exact hne hyEq

theorem RLink.exists_RCLPath_from_ring_mem_faceBand_nodup
    [Fintype G.Dart]
    {r : List G.Dart} {x y : G.Dart}
    (hr : G.FaceSimple r)
    (hx : x ∈ r)
    (hy : y ∈ r)
    (hxy : G.RLink x y) :
    ∃ p : List G.Dart,
      G.RCLPath r x p ∧
        (x :: p).getLastD x = y ∧
          p.Nodup ∧
            ∀ t : G.Dart, G.FaceBand p t → G.FaceBand [y] t := by
  rcases RLink.exists_short_facePath_from_face_edge (G := G) hxy with
    ⟨q, hq, hlast, hnodup⟩
  have hrclTail :
      G.RCLPath r (G.face (G.edge x)) q :=
    FacePath.to_RCLPath_of_faceSimple_last_mem
      (G := G) hr hq hnodup (by rw [hlast]; exact hy)
  refine ⟨G.face (G.edge x) :: q, ?_, ?_, hnodup, ?_⟩
  · exact ⟨RCLStep.eq_face_edge_of_mem (G := G) hx, hrclTail⟩
  · simpa [List.getLastD] using hlast
  · intro t ht
    have hsubset :=
      FacePath.faceBand_subset_singleton_last (G := G) hq t ht
    have hreachLast :
        PermReachable G.face
          ((G.face (G.edge x) :: q).getLastD (G.face (G.edge x))) t := by
      rwa [FaceBand.singleton] at hsubset
    have hlast' :
        (G.face (G.edge x) :: q).getLast?.getD (G.face (G.edge x)) = y := by
      simpa [List.getLastD] using hlast
    have hreach : PermReachable G.face y t := by
      simpa [hlast'] using hreachLast
    exact (FaceBand.singleton (G := G)).2 hreach

theorem RLink.exists_RCLPath_from_ring_mem_faceBand
    [Fintype G.Dart]
    {r : List G.Dart} {x y : G.Dart}
    (hr : G.FaceSimple r)
    (hx : x ∈ r)
    (hy : y ∈ r)
    (hxy : G.RLink x y) :
    ∃ p : List G.Dart,
      G.RCLPath r x p ∧
        (x :: p).getLastD x = y ∧
          ∀ t : G.Dart, G.FaceBand p t → G.FaceBand [y] t := by
  rcases RLink.exists_RCLPath_from_ring_mem_faceBand_nodup
      (G := G) hr hx hy hxy with ⟨p, hp, hlast, _, hband⟩
  exact ⟨p, hp, hlast, hband⟩

theorem RLink.exists_RCLPath_from_ring_mem
    [Fintype G.Dart]
    {r : List G.Dart} {x y : G.Dart}
    (hr : G.FaceSimple r)
    (hx : x ∈ r)
    (hy : y ∈ r)
    (hxy : G.RLink x y) :
    ∃ p : List G.Dart,
      G.RCLPath r x p ∧
        (x :: p).getLastD x = y := by
  rcases RLink.exists_RCLPath_from_ring_mem_faceBand
      (G := G) hr hx hy hxy with ⟨p, hp, hlast, _⟩
  exact ⟨p, hp, hlast⟩

theorem RLinkPath.exists_RCLPath_from_ring_path_subset_faceBand
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hr : G.FaceSimple r)
    (hx : x ∈ r)
    (hp : G.RLinkPath x p)
    (hsub : ∀ y : G.Dart, y ∈ p → y ∈ r) :
    ∃ q : List G.Dart,
      G.RCLPath r x q ∧
        (x :: q).getLastD x = (x :: p).getLastD x ∧
          (∀ y : G.Dart, y ∈ x :: p → y ∈ x :: q) ∧
            ∀ t : G.Dart, G.FaceBand q t → G.FaceBand p t := by
  induction p generalizing x with
  | nil =>
      refine ⟨[], by simp [RCLPath], by simp [List.getLastD], ?_, ?_⟩
      · intro y hy
        exact hy
      · intro t ht
        rcases ht with ⟨u, hu, _⟩
        cases hu
  | cons y p ih =>
      have hp' : G.RLink x y ∧ G.RLinkPath y p := by
        simpa [RLinkPath] using hp
      have hy : y ∈ r := hsub y (by simp)
      have hsubTail : ∀ z : G.Dart, z ∈ p → z ∈ r := by
        intro z hz
        exact hsub z (by simp [hz])
      rcases RLink.exists_RCLPath_from_ring_mem_faceBand
          (G := G) hr hx hy hp'.1 with
        ⟨q1, hq1, hlast1, hband1⟩
      rcases ih hy hp'.2 hsubTail with
        ⟨q2, hq2, hlast2, hsubQ2, hband2⟩
      have hyq1 : y ∈ x :: q1 := by
        rw [← hlast1]
        exact List.getLastD_cons_mem x q1
      have hyInAppend : y ∈ x :: (q1 ++ q2) := by
        rw [List.mem_cons] at hyq1 ⊢
        rcases hyq1 with hyx | hyq1
        · exact Or.inl hyx
        · exact Or.inr (List.mem_append_left q2 hyq1)
      refine ⟨q1 ++ q2, ?_, ?_, ?_, ?_⟩
      · exact RCLPath.append (G := G) hq1 hlast1 hq2
      · calc
          (x :: (q1 ++ q2)).getLastD x =
              (y :: q2).getLastD y :=
                list_getLastD_cons_append_of_getLast x y q1 q2 hlast1
          _ = (y :: p).getLastD y := hlast2
          _ = (x :: y :: p).getLastD x := by
                simp [List.getLastD]
      · intro z hz
        rw [List.mem_cons] at hz
        rcases hz with hzx | hz
        · rw [hzx]
          simp
        · have hzQ2 : z ∈ y :: q2 := hsubQ2 z hz
          rw [List.mem_cons] at hzQ2
          rcases hzQ2 with hzy | hzq2
          · rw [hzy]
            exact hyInAppend
          · exact List.mem_cons_of_mem x
              (List.mem_append_right q1 hzq2)
      · intro t ht
        rw [FaceBand.append] at ht
        rcases ht with ht | ht
        · have hyt : G.FaceBand [y] t := hband1 t ht
          exact (FaceBand.cons (G := G)).2
            (Or.inl ((FaceBand.singleton (G := G)).1 hyt))
        · exact (FaceBand.cons (G := G)).2
            (Or.inr (hband2 t ht))

theorem RLinkPath.exists_RCLPath_from_ring_path_subset
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hr : G.FaceSimple r)
    (hx : x ∈ r)
    (hp : G.RLinkPath x p)
    (hsub : ∀ y : G.Dart, y ∈ p → y ∈ r) :
    ∃ q : List G.Dart,
      G.RCLPath r x q ∧
        (x :: q).getLastD x = (x :: p).getLastD x ∧
          ∀ y : G.Dart, y ∈ x :: p → y ∈ x :: q := by
  rcases RLinkPath.exists_RCLPath_from_ring_path_subset_faceBand
      (G := G) hr hx hp hsub with ⟨q, hq, hlast, hsubset, _⟩
  exact ⟨q, hq, hlast, hsubset⟩

theorem RLinkPath.exists_RCLPath_from_ring_path
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hr : G.FaceSimple r)
    (hx : x ∈ r)
    (hp : G.RLinkPath x p)
    (hsub : ∀ y : G.Dart, y ∈ p → y ∈ r) :
    ∃ q : List G.Dart,
      G.RCLPath r x q ∧
        (x :: q).getLastD x = (x :: p).getLastD x := by
  rcases RLinkPath.exists_RCLPath_from_ring_path_subset
      (G := G) hr hx hp hsub with ⟨q, hq, hlast, _⟩
  exact ⟨q, hq, hlast⟩

theorem RLinkPath.exists_RCLPath_from_ring_path_subset_faceBand_nodup
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hr : G.FaceSimple r)
    (hx : x ∈ r)
    (hp : G.RLinkPath x p)
    (hsub : ∀ y : G.Dart, y ∈ p → y ∈ r)
    (hpathSimple : G.FaceSimple (x :: p)) :
    ∃ q : List G.Dart,
      G.RCLPath r x q ∧
        (x :: q).getLastD x = (x :: p).getLastD x ∧
          (∀ y : G.Dart, y ∈ x :: p → y ∈ x :: q) ∧
            q.Nodup ∧
              ∀ t : G.Dart, G.FaceBand q t → G.FaceBand p t := by
  induction p generalizing x with
  | nil =>
      refine ⟨[], by simp [RCLPath], by simp [List.getLastD], ?_, by simp, ?_⟩
      · intro y hy
        exact hy
      · intro t ht
        exact False.elim (FaceBand.nil (G := G) ht)
  | cons y p ih =>
      have hp' : G.RLink x y ∧ G.RLinkPath y p := by
        simpa [RLinkPath] using hp
      have hy : y ∈ r := hsub y (by simp)
      have hsubTail : ∀ z : G.Dart, z ∈ p → z ∈ r := by
        intro z hz
        exact hsub z (by simp [hz])
      have htailSimple : G.FaceSimple (y :: p) :=
        FaceSimple.tail (G := G) hpathSimple
      rcases RLink.exists_RCLPath_from_ring_mem_faceBand_nodup
          (G := G) hr hx hy hp'.1 with
        ⟨q1, hq1, hlast1, hq1Nodup, hband1⟩
      rcases ih hy hp'.2 hsubTail htailSimple with
        ⟨q2, hq2, hlast2, hsubQ2, hq2Nodup, hband2⟩
      have hyq1 : y ∈ x :: q1 := by
        rw [← hlast1]
        exact List.getLastD_cons_mem x q1
      have hyInAppend : y ∈ x :: (q1 ++ q2) := by
        rw [List.mem_cons] at hyq1 ⊢
        rcases hyq1 with hyx | hyq1
        · exact Or.inl hyx
        · exact Or.inr (List.mem_append_left q2 hyq1)
      have hqNodup : (q1 ++ q2).Nodup := by
        rw [List.nodup_append]
        refine ⟨hq1Nodup, hq2Nodup, ?_⟩
        intro a ha b hb hab
        subst b
        have haBand : G.FaceBand q1 a :=
          FaceBand.of_mem (G := G) ha (PermReachable.refl G.face a)
        have hbBand : G.FaceBand q2 a :=
          FaceBand.of_mem (G := G) hb (PermReachable.refl G.face a)
        have hya : PermReachable G.face y a :=
          (FaceBand.singleton (G := G)).1 (hband1 a haBand)
        rcases hband2 a hbBand with ⟨u, hu, hua⟩
        have hyu : PermReachable G.face y u :=
          PermReachable.trans G.face hya (PermReachable.symm G.face hua)
        exact FaceSimple.not_faceReachable_head (G := G) htailSimple hu hyu
      refine ⟨q1 ++ q2, ?_, ?_, ?_, hqNodup, ?_⟩
      · exact RCLPath.append (G := G) hq1 hlast1 hq2
      · calc
          (x :: (q1 ++ q2)).getLastD x =
              (y :: q2).getLastD y :=
                list_getLastD_cons_append_of_getLast x y q1 q2 hlast1
          _ = (y :: p).getLastD y := hlast2
          _ = (x :: y :: p).getLastD x := by
                simp [List.getLastD]
      · intro z hz
        rw [List.mem_cons] at hz
        rcases hz with hzx | hz
        · rw [hzx]
          simp
        · have hzQ2 : z ∈ y :: q2 := hsubQ2 z hz
          rw [List.mem_cons] at hzQ2
          rcases hzQ2 with hzy | hzq2
          · rw [hzy]
            exact hyInAppend
          · exact List.mem_cons_of_mem x
              (List.mem_append_right q1 hzq2)
      · intro t ht
        rw [FaceBand.append] at ht
        rcases ht with ht | ht
        · have hyt : G.FaceBand [y] t := hband1 t ht
          exact (FaceBand.cons (G := G)).2
            (Or.inl ((FaceBand.singleton (G := G)).1 hyt))
        · exact (FaceBand.cons (G := G)).2
            (Or.inr (hband2 t ht))

theorem RCLCycle.of_facePath_faceSimple_last_mem
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hr : G.FaceSimple r)
    (hp : G.FacePath x p)
    (hnodup : (x :: p).Nodup)
    (hlast : (x :: p).getLastD x ∈ r)
    (hx : x = G.face (G.edge ((x :: p).getLastD x))) :
    G.RCLCycle r (x :: p) := by
  have hrcl :
      G.RCLPath r x p :=
    FacePath.to_RCLPath_of_faceSimple_last_mem
      (G := G) hr hp hnodup hlast
  exact RCLCycle.of_path_last_mem (G := G) hrcl rfl hlast hx

theorem RCLCycle.of_facePath_prefix_RCLPath_tail
    {r : List G.Dart} {x y z : G.Dart} {p q : List G.Dart}
    (hr : G.FaceSimple r)
    (hp : G.FacePath x p)
    (hnodup : (x :: p).Nodup)
    (hlastp : (x :: p).getLastD x = y)
    (hy : y ∈ r)
    (hq : G.RCLPath r y q)
    (hlastq : (y :: q).getLastD y = z)
    (hz : z ∈ r)
    (hx : x = G.face (G.edge z)) :
    G.RCLCycle r (x :: (p ++ q)) := by
  have hpRCL : G.RCLPath r x p :=
    FacePath.to_RCLPath_of_faceSimple_last_mem
      (G := G) hr hp hnodup (by rw [hlastp]; exact hy)
  have hpath : G.RCLPath r x (p ++ q) :=
    RCLPath.append (G := G) hpRCL hlastp hq
  have hlast : (x :: (p ++ q)).getLastD x = z := by
    calc
      (x :: (p ++ q)).getLastD x =
          (y :: q).getLastD y :=
            list_getLastD_cons_append_of_getLast x y p q hlastp
      _ = z := hlastq
  exact RCLCycle.of_path_last_mem (G := G) hpath hlast hz hx

theorem diskN_of_facePath_avoids_ring
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hx : G.DiskN r x)
    (hp : G.FacePath x p)
    (havoid : ∀ y : G.Dart, y ∈ x :: p → y ∉ r) :
    G.DiskN r ((x :: p).getLastD x) := by
  induction p generalizing x with
  | nil =>
      simpa [List.getLastD] using hx
  | cons y p ih =>
      have hp' : G.face x = y ∧ G.FacePath y p := by
        simpa [FacePath] using hp
      have hxNot : x ∉ r := havoid x (by simp)
      have hyN : G.DiskN r y := by
        rw [← hp'.1]
        exact G.diskN_face_of_not_mem hx hxNot
      have havoidTail : ∀ z : G.Dart, z ∈ y :: p → z ∉ r := by
        intro z hz
        exact havoid z (by simp [hz])
      simpa [List.getLastD] using ih hyN hp'.2 havoidTail

theorem diskE_of_facePath_avoids_ring
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hx : G.DiskN r x)
    (hp : G.FacePath x p)
    (havoid : ∀ y : G.Dart, y ∈ x :: p → y ∉ r) :
    G.DiskE r ((x :: p).getLastD x) := by
  refine ⟨G.diskN_of_facePath_avoids_ring hx hp havoid, ?_⟩
  exact havoid ((x :: p).getLastD x)
    (List.getLastD_cons_mem x p)

theorem diskE_of_facePath_to_edge_avoids_ring
    {r : List G.Dart} {x x' : G.Dart} {p : List G.Dart}
    (hx' : G.DiskN r x')
    (hp : G.FacePath x' p)
    (hlast : (x' :: p).getLastD x' = G.edge x)
    (havoid : ∀ y : G.Dart, y ∈ x' :: p → y ∉ r) :
    G.DiskE r (G.edge x) := by
  rw [← hlast]
  exact G.diskE_of_facePath_avoids_ring hx' hp havoid

theorem diskN_face_edge_of_diskE
    {r : List G.Dart} {x : G.Dart}
    (hx : G.DiskE r x) :
    G.DiskN r (G.face (G.edge x)) := by
  have hxNodeSymm : G.DiskN r (G.node.symm x) :=
    G.diskN_node_symm hx.1
  convert hxNodeSymm using 1
  apply G.node.injective
  simp

theorem diskN_face_edge_of_mem
    {r : List G.Dart} {x : G.Dart}
    (hx : x ∈ r) :
    G.DiskN r (G.face (G.edge x)) := by
  rw [face_edge_eq_node_symm (G := G) x]
  exact G.diskN_node_symm_of_mem hx

theorem diskE_edge_of_facePath_avoids_ring
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hx : G.DiskE r x)
    (hp : G.FacePath (G.face (G.edge x)) p)
    (hlast :
      (G.face (G.edge x) :: p).getLastD (G.face (G.edge x)) =
        G.edge x)
    (havoid :
      ∀ y : G.Dart,
        y ∈ G.face (G.edge x) :: p → y ∉ r) :
    G.DiskE r (G.edge x) :=
  G.diskE_of_facePath_to_edge_avoids_ring
    (G.diskN_face_edge_of_diskE hx) hp hlast havoid

theorem diskE_of_facePath_from_ring_face_edge_avoids_ring
    {r : List G.Dart} {x z : G.Dart} {p : List G.Dart}
    (hz : z ∈ r)
    (hp : G.FacePath (G.face (G.edge z)) p)
    (hlast :
      (G.face (G.edge z) :: p).getLastD (G.face (G.edge z)) =
        G.edge x)
    (havoid :
      ∀ y : G.Dart,
        y ∈ G.face (G.edge z) :: p → y ∉ r) :
    G.DiskE r (G.edge x) :=
  G.diskE_of_facePath_to_edge_avoids_ring
    (G.diskN_face_edge_of_mem hz) hp hlast havoid

theorem diskE_of_split_suffix_prior_ring_hit
    {r : List G.Dart} {x y z : G.Dart} {pre post : List G.Dart}
    (hr : G.FaceSimple r)
    (hz : z ∈ r)
    (hnodup :
      (G.face (G.edge x) :: (pre ++ G.face (G.edge z) :: post)).Nodup)
    (hyPre : y ∈ G.face (G.edge x) :: pre)
    (hyR : y ∈ r)
    (hzy : G.RLink z y)
    (hpost : G.FacePath (G.face (G.edge z)) post)
    (hlast :
      (G.face (G.edge z) :: post).getLastD (G.face (G.edge z)) =
        G.edge x) :
    G.DiskE r (G.edge x) := by
  have havoid :
      ∀ t : G.Dart,
        t ∈ G.face (G.edge z) :: post → t ∉ r :=
    FacePath.suffix_avoids_ring_of_prior_ring_hit
      (G := G) hr hnodup hyPre hyR
      (RLink.face_edge_reachable (G := G) hzy) hpost
  exact G.diskE_of_facePath_from_ring_face_edge_avoids_ring
    hz hpost hlast havoid

theorem diskE_ne_face_edge_of_ring_mem
    {r : List G.Dart} {x z : G.Dart}
    (hx : G.DiskE r x)
    (hz : z ∈ r) :
    G.face (G.edge z) ≠ G.face (G.edge x) := by
  intro hzx
  have hzx' : z = x :=
    face_edge_injective (G := G) hzx
  exact hx.2 (by simpa [hzx'] using hz)

theorem RLinkPath.exists_successor_or_last
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x p)
    (hy : y ∈ x :: p) :
    (∃ z : G.Dart, z ∈ p ∧ G.RLink y z) ∨
      y = (x :: p).getLastD x := by
  induction p generalizing x with
  | nil =>
      simp at hy
      subst y
      right
      simp [List.getLastD]
  | cons z p ih =>
      have hp' : G.RLink x z ∧ G.RLinkPath z p := by
        simpa [RLinkPath] using hp
      rw [List.mem_cons] at hy
      rcases hy with hy | hy
      · subst y
        exact Or.inl ⟨z, by simp, hp'.1⟩
      · rcases ih hp'.2 hy with hsucc | hlast
        · rcases hsucc with ⟨w, hw, hyw⟩
          exact Or.inl ⟨w, by simp [hw], hyw⟩
        · exact Or.inr (by simpa [List.getLastD] using hlast)

theorem RLinkPath.exists_predecessor_or_head
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x p)
    (hy : y ∈ x :: p) :
    y = x ∨ ∃ z : G.Dart, z ∈ x :: p ∧ G.RLink z y := by
  induction p generalizing x with
  | nil =>
      simp at hy
      exact Or.inl hy
  | cons z p ih =>
      have hp' : G.RLink x z ∧ G.RLinkPath z p := by
        simpa [RLinkPath] using hp
      rw [List.mem_cons] at hy
      rcases hy with hy | hy
      · exact Or.inl hy
      · have hyTail : y ∈ z :: p := hy
        rcases ih hp'.2 hyTail with hyz | hpred
        · subst y
          exact Or.inr ⟨x, by simp, hp'.1⟩
        · rcases hpred with ⟨w, hw, hwy⟩
          exact Or.inr ⟨w, by simp [hw], hwy⟩

theorem RLinkCycle.exists_outgoing
    {r : List G.Dart}
    (hr : G.RLinkCycle r)
    {x : G.Dart}
    (hx : x ∈ r) :
    ∃ y : G.Dart, y ∈ r ∧ G.RLink x y := by
  cases r with
  | nil =>
      cases hx
  | cons a p =>
      rcases RLinkPath.exists_successor_or_last (G := G) hr.1 hx with
        hsucc | hlast
      · rcases hsucc with ⟨y, hy, hxy⟩
        exact ⟨y, by simp [hy], hxy⟩
      · subst x
        exact ⟨a, by simp, hr.2⟩

theorem RLinkCycle.exists_incoming
    {r : List G.Dart}
    (hr : G.RLinkCycle r)
    {x : G.Dart}
    (hx : x ∈ r) :
    ∃ y : G.Dart, y ∈ r ∧ G.RLink y x := by
  cases r with
  | nil =>
      cases hx
  | cons a p =>
      rcases RLinkPath.exists_predecessor_or_head (G := G) hr.1 hx with
        hhead | hpred
      · subst x
        exact ⟨(a :: p).getLastD a,
          List.getLastD_cons_mem a p, hr.2⟩
      · exact hpred

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
