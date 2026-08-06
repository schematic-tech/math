import Schematic.Math.GraphTheory.Embedding.Geometry.DiskChords
import Schematic.Math.GraphTheory.Embedding.Geometry.LocalPeriod

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

theorem RLink.symm_edge_of_plain
    (hPlain : G.Plain)
    {x y : G.Dart}
    (hxy : G.RLink x y) :
    G.RLink (G.edge y) (G.edge x) := by
  unfold RLink at hxy ⊢
  simpa [Plain.edge_edge (G := G) hPlain y] using
    PermReachable.symm G.face hxy

theorem RLinkPath.reverse_edges_of_plain
    (hPlain : G.Plain)
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x (p ++ [y])) :
    G.RLinkPath (G.edge y) ((p.reverse.map G.edge) ++ [G.edge x]) := by
  induction p generalizing x with
  | nil =>
      have hxy : G.RLink x y := by
        simpa [RLinkPath] using hp
      simpa [RLinkPath] using
        RLinkPath.singleton (G := G)
          (RLink.symm_edge_of_plain (G := G) hPlain hxy)
  | cons z p ih =>
      have hp' : G.RLink x z ∧ G.RLinkPath z (p ++ [y]) := by
        simpa [RLinkPath] using hp
      have htail : G.RLinkPath (G.edge y)
          ((p.reverse.map G.edge) ++ [G.edge z]) :=
        ih hp'.2
      have hlast : G.RLink (G.edge z) (G.edge x) :=
        RLink.symm_edge_of_plain (G := G) hPlain hp'.1
      have hsnoc : G.RLinkPath (G.edge y)
          ((p.reverse.map G.edge) ++ [G.edge z, G.edge x]) :=
        RLinkPath.snoc (G := G) (p.reverse.map G.edge) htail hlast
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using hsnoc

theorem RLinkPath.reverse_forall₂_faceReachable
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x (p ++ [y])) :
    List.Forall₂ (fun a b : G.Dart => PermReachable G.face a b)
      ((p ++ [y]).reverse) ((p.map G.edge).reverse ++ [G.edge x]) := by
  induction p generalizing x with
  | nil =>
      have hxy : G.RLink x y := by
        simpa [RLinkPath] using hp
      exact List.Forall₂.cons (PermReachable.symm G.face hxy) List.Forall₂.nil
  | cons z p ih =>
      have hp' : G.RLink x z ∧ G.RLinkPath z (p ++ [y]) := by
        simpa [RLinkPath] using hp
      have htail :
          List.Forall₂ (fun a b : G.Dart => PermReachable G.face a b)
            ((p ++ [y]).reverse)
            ((p.map G.edge).reverse ++ [G.edge z]) :=
        ih hp'.2
      have hlast :
          List.Forall₂ (fun a b : G.Dart => PermReachable G.face a b)
            [z] [G.edge x] :=
        List.Forall₂.cons (PermReachable.symm G.face hp'.1) List.Forall₂.nil
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        List.rel_append htail hlast

theorem RLinkCycle.revRing_of_plain
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.RLinkCycle r) :
    G.RLinkCycle (G.RevRing r) := by
  cases r with
  | nil =>
      contradiction
  | cons a p =>
      rcases List.eq_nil_or_concat' p with hp | ⟨q, b, hp⟩
      · subst p
        have haa : G.RLink a a := by
          simpa [List.getLastD] using hr.2
        have hclose : G.RLink (G.edge a) (G.edge a) :=
          RLink.symm_edge_of_plain (G := G) hPlain haa
        simp [RevRing, RLinkCycle, RLinkPath, hclose]
      · subst p
        have hpath : G.RLinkPath (G.edge b)
            ((q.reverse.map G.edge) ++ [G.edge a]) :=
          RLinkPath.reverse_edges_of_plain (G := G) hPlain hr.1
        have hba : G.RLink b a := by
          simpa [List.getLastD] using hr.2
        have hclose : G.RLink (G.edge a) (G.edge b) :=
          RLink.symm_edge_of_plain (G := G) hPlain hba
        simp [RevRing, RLinkCycle, List.reverse_cons, List.map_append]
        constructor
        · simpa [List.map_reverse] using hpath
        · have hlast :
              (G.edge b :: ((List.map (⇑G.edge) q).reverse ++
                [G.edge a])).getLast?.getD (G.edge b) = G.edge a := by
            exact List.getLast?_getD_cons_append_singleton
              (G.edge b) (G.edge a) ((List.map (⇑G.edge) q).reverse)
          rw [hlast]
          exact hclose

private theorem RLinkPath.map_faceOrbit_edge
    {x : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x p) :
    (x :: p).map (fun z => PermOrbit.of G.face (G.edge z)) =
      p.map (PermOrbit.of G.face) ++
        [PermOrbit.of G.face (G.edge ((x :: p).getLastD x))] := by
  induction p generalizing x with
  | nil => simp [List.getLastD]
  | cons y p ih =>
      have hp' : G.RLink x y ∧ G.RLinkPath y p := by
        simpa [RLinkPath] using hp
      have hxy :
          PermOrbit.of G.face (G.edge x) = PermOrbit.of G.face y :=
        PermOrbit.of_eq_of G.face hp'.1
      change
        PermOrbit.of G.face (G.edge x) ::
            (y :: p).map (fun z => PermOrbit.of G.face (G.edge z)) =
          PermOrbit.of G.face y :: p.map (PermOrbit.of G.face) ++
            [PermOrbit.of G.face (G.edge ((x :: y :: p).getLastD x))]
      rw [ih hp'.2, hxy]
      congr 2

/-- Coq `froot_face_rev_ring`, with the canonical quotient `PermOrbit.of`
in place of MathComp's selected orbit root. -/
theorem RLinkCycle.map_faceOrbit_revRing
    {r : List G.Dart}
    (hr : G.RLinkCycle r) :
    (G.RevRing r).map (PermOrbit.of G.face) =
      ((r.map (PermOrbit.of G.face)).rotate 1).reverse := by
  cases r with
  | nil => simp [RevRing]
  | cons x p =>
      have hpath := RLinkPath.map_faceOrbit_edge (G := G) hr.1
      have hclose :
          PermOrbit.of G.face
              (G.edge ((x :: p).getLastD x)) =
            PermOrbit.of G.face x :=
        PermOrbit.of_eq_of G.face hr.2
      have hedge :
          (x :: p).map (fun z => PermOrbit.of G.face (G.edge z)) =
            p.map (PermOrbit.of G.face) ++ [PermOrbit.of G.face x] := by
        rw [hpath, hclose]
      calc
        (G.RevRing (x :: p)).map (PermOrbit.of G.face) =
            ((x :: p).map
              (fun z => PermOrbit.of G.face (G.edge z))).reverse := by
          simp [RevRing, List.map_reverse, List.map_map, Function.comp_def]
        _ = (p.map (PermOrbit.of G.face) ++
              [PermOrbit.of G.face x]).reverse :=
          congrArg List.reverse hedge
        _ = (((x :: p).map (PermOrbit.of G.face)).rotate 1).reverse := by
          simp [List.rotate_cons_succ]

theorem FaceSimple.revRing_of_plain
    {r : List G.Dart}
    (hr : G.RLinkCycle r)
    (hs : G.FaceSimple r) :
    G.FaceSimple (G.RevRing r) := by
  cases r with
  | nil =>
      simp [RevRing, FaceSimple]
  | cons a p =>
      rcases List.eq_nil_or_concat' p with hp | ⟨q, b, hp⟩
      · subst p
        have haa : G.RLink a a := by
          simpa [List.getLastD] using hr.2
        have hall :
            List.Forall₂ (fun x y : G.Dart => PermReachable G.face x y)
              [a] [G.edge a] :=
          List.Forall₂.cons (PermReachable.symm G.face haa) List.Forall₂.nil
        exact FaceSimple.of_forall₂_faceReachable (G := G) hall hs
      · subst p
        have htail :
            List.Forall₂ (fun x y : G.Dart => PermReachable G.face x y)
              ((q ++ [b]).reverse)
              ((q.map G.edge).reverse ++ [G.edge a]) :=
          RLinkPath.reverse_forall₂_faceReachable (G := G) hr.1
        have hba : G.RLink b a := by
          simpa [List.getLastD] using hr.2
        have hhead : PermReachable G.face a (G.edge b) :=
          PermReachable.symm G.face hba
        have hall :
            List.Forall₂ (fun x y : G.Dart => PermReachable G.face x y)
              (a :: (q ++ [b]).reverse)
              (G.edge b :: ((q.map G.edge).reverse ++ [G.edge a])) :=
          List.Forall₂.cons hhead htail
        have hperm :
            List.Perm (a :: (q ++ [b])) (a :: (q ++ [b]).reverse) :=
          List.Perm.cons a (List.reverse_perm (q ++ [b])).symm
        have hsource : G.FaceSimple (a :: (q ++ [b]).reverse) :=
          FaceSimple.perm (G := G) hperm hs
        have htarget : G.FaceSimple
            (G.edge b :: ((q.map G.edge).reverse ++ [G.edge a])) :=
          FaceSimple.of_forall₂_faceReachable (G := G) hall hsource
        simpa [RevRing, List.reverse_cons, List.map_append] using htarget

theorem SimpleRLinkCycle.revRing_of_plain
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r) :
    G.SimpleRLinkCycle (G.RevRing r) :=
  ⟨RLinkCycle.revRing_of_plain (G := G) hPlain hr.1,
    FaceSimple.revRing_of_plain (G := G) hr.1 hr.2⟩

theorem FaceBand.revRing_iff_of_plain
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.RLinkCycle r)
    {u : G.Dart} :
    G.FaceBand (G.RevRing r) u ↔ G.FaceBand r u := by
  constructor
  · rintro ⟨y, hyRev, hyu⟩
    have hyEdge : G.edge y ∈ r :=
      (mem_revRing_of_plain (G := G) hPlain).1 hyRev
    rcases RLinkCycle.exists_outgoing (G := G) hr hyEdge with
      ⟨z, hz, hyz⟩
    have hyz' : PermReachable G.face y z := by
      unfold RLink at hyz
      simpa [Plain.edge_edge (G := G) hPlain y] using hyz
    exact ⟨z, hz,
      PermReachable.trans G.face (PermReachable.symm G.face hyz') hyu⟩
  · rintro ⟨y, hy, hyu⟩
    rcases RLinkCycle.exists_incoming (G := G) hr hy with
      ⟨z, hz, hzy⟩
    refine ⟨G.edge z, ?_, ?_⟩
    · rw [mem_revRing_of_plain (G := G) hPlain]
      simpa [Plain.edge_edge (G := G) hPlain z] using hz
    · unfold RLink at hzy
      exact PermReachable.trans G.face hzy hyu

theorem Plain.node_face_eq_edge
    (hG : G.Plain)
    (x : G.Dart) :
    G.node (G.face x) = G.edge x := by
  apply G.edge.injective
  calc
    G.edge (G.node (G.face x)) = x := G.edge_node_face x
    _ = G.edge (G.edge x) := (Plain.edge_edge (G := G) hG x).symm

theorem Plain.edge_eq_node_face
    (hG : G.Plain)
    (x : G.Dart) :
    G.edge x = G.node (G.face x) :=
  (Plain.node_face_eq_edge (G := G) hG x).symm

theorem diskN_rev_ring_base
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    (hproper : G.ProperRing r)
    {y : G.Dart}
    (hy : y ∈ r) :
    G.DiskN (G.RevRing r) (G.edge y) ↔
      ¬ G.DiskN r (G.edge y) := by
  constructor
  · intro _hyRev
    exact G.diskN_edge_ring hJ hPlain hr hproper hy
  · intro _hyNot
    apply G.diskN_of_mem
    rw [mem_revRing_of_plain (G := G) hPlain]
    simpa [Plain.edge_edge (G := G) hPlain y] using hy

theorem diskN_rev_ring_node_step
    [Fintype G.Dart]
    {r : List G.Dart}
    {x y : G.Dart}
    (hyx : y = G.node.symm x)
    (hy :
      G.DiskN (G.RevRing r) y ↔
        ¬ G.DiskN r y) :
    G.DiskN (G.RevRing r) x ↔
      ¬ G.DiskN r x := by
  subst y
  constructor
  · intro hxRev hx
    have hyRev : G.DiskN (G.RevRing r) (G.node.symm x) :=
      (diskN_node_symm_iff (G := G) (r := G.RevRing r)).2 hxRev
    have hyNot : ¬ G.DiskN r (G.node.symm x) := hy.1 hyRev
    exact hyNot ((diskN_node_symm_iff (G := G) (r := r)).2 hx)
  · intro hxNot
    have hyNot : ¬ G.DiskN r (G.node.symm x) := by
      intro hyDisk
      exact hxNot ((diskN_node_symm_iff (G := G) (r := r)).1 hyDisk)
    have hyRev : G.DiskN (G.RevRing r) (G.node.symm x) :=
      hy.2 hyNot
    exact (diskN_node_symm_iff (G := G) (r := G.RevRing r)).1 hyRev

theorem diskN_rev_ring_face_step
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    (hproper : G.ProperRing r)
    {x y : G.Dart}
    (hyx : y = G.face x)
    (hy :
      G.DiskN (G.RevRing r) y ↔
        ¬ G.DiskN r y) :
    G.DiskN (G.RevRing r) x ↔
      ¬ G.DiskN r x := by
  subst y
  let rr : List G.Dart := G.RevRing r
  have hrRev : G.SimpleRLinkCycle rr :=
    SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr
  have hproperRev : G.ProperRing rr :=
    (properRing_revRing_iff_of_plain (G := G) hPlain r).2 hproper
  have hrevNode :
      G.DiskN rr (G.edge x) ↔ G.DiskN rr (G.face x) := by
    rw [Plain.edge_eq_node_face (G := G) hPlain x]
    exact diskN_node_iff (G := G) (r := rr)
  have hnode :
      G.DiskN r (G.edge x) ↔ G.DiskN r (G.face x) := by
    rw [Plain.edge_eq_node_face (G := G) hPlain x]
    exact diskN_node_iff (G := G) (r := r)
  by_cases hEdgeR : G.edge x ∈ r
  · have hxRevMem : x ∈ rr := by
      rw [mem_revRing_of_plain (G := G) hPlain]
      exact hEdgeR
    have hxRev : G.DiskN rr x :=
      G.diskN_of_mem hxRevMem
    have hxNot : ¬ G.DiskN r x := by
      have hnot := G.diskN_edge_ring hJ hPlain hr hproper hEdgeR
      simpa [Plain.edge_edge (G := G) hPlain x] using hnot
    exact ⟨fun _ => hxNot, fun _ => hxRev⟩
  · have hxNotRev : x ∉ rr := by
      intro hxRev
      exact hEdgeR ((mem_revRing_of_plain (G := G) hPlain).1 hxRev)
    constructor
    · intro hxRev hxDisk
      by_cases hxR : x ∈ r
      · have hedgeRevMem : G.edge x ∈ rr := by
          rw [mem_revRing_of_plain (G := G) hPlain]
          simpa [Plain.edge_edge (G := G) hPlain x] using hxR
        have hnotRevX : ¬ G.DiskN rr x := by
          have hnot :=
            G.diskN_edge_ring hJ hPlain hrRev hproperRev hedgeRevMem
          simpa [rr, Plain.edge_edge (G := G) hPlain x] using hnot
        exact hnotRevX hxRev
      · have hxRevE : G.DiskE rr x :=
          ⟨hxRev, hxNotRev⟩
        have hedgeRevE : G.DiskE rr (G.edge x) :=
          (G.diskE_edge_iff hJ hPlain hrRev).2 hxRevE
        have hfaceRev : G.DiskN rr (G.face x) :=
          hrevNode.1 hedgeRevE.1
        have hfaceNot : ¬ G.DiskN r (G.face x) :=
          hy.1 hfaceRev
        have hxE : G.DiskE r x := ⟨hxDisk, hxR⟩
        have hedgeE : G.DiskE r (G.edge x) :=
          (G.diskE_edge_iff hJ hPlain hr).2 hxE
        exact hfaceNot (hnode.1 hedgeE.1)
    · intro hxNot
      have hxNotR : x ∉ r := by
        intro hxR
        exact hxNot (G.diskN_of_mem hxR)
      have hfaceNot : ¬ G.DiskN r (G.face x) := by
        intro hface
        have hedgeDisk : G.DiskN r (G.edge x) :=
          hnode.2 hface
        have hedgeE : G.DiskE r (G.edge x) :=
          ⟨hedgeDisk, hEdgeR⟩
        have hxE : G.DiskE r x :=
          (G.diskE_edge_iff hJ hPlain hr).1 hedgeE
        exact hxNot hxE.1
      have hfaceRev : G.DiskN rr (G.face x) :=
        hy.2 hfaceNot
      have hedgeRevDisk : G.DiskN rr (G.edge x) :=
        hrevNode.2 hfaceRev
      have hedgeNotRev : G.edge x ∉ rr := by
        intro hedgeRev
        have hxR : x ∈ r := by
          have hxRR :=
            (mem_revRing_of_plain (G := G) hPlain).1 hedgeRev
          simpa [Plain.edge_edge (G := G) hPlain x] using hxRR
        exact hxNot (G.diskN_of_mem hxR)
      have hedgeRevE : G.DiskE rr (G.edge x) :=
        ⟨hedgeRevDisk, hedgeNotRev⟩
      have hxRevE : G.DiskE rr x :=
        (G.diskE_edge_iff hJ hPlain hrRev).1 hedgeRevE
      exact hxRevE.1

theorem diskN_rev_ring_of_cPath
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    (hproper : G.ProperRing r)
    {x target : G.Dart} {p : List G.Dart}
    (hp : G.CPath x p)
    (hlast : (x :: p).getLastD x = target)
    (htarget :
      G.DiskN (G.RevRing r) target ↔
        ¬ G.DiskN r target) :
    G.DiskN (G.RevRing r) x ↔
      ¬ G.DiskN r x := by
  induction p generalizing x with
  | nil =>
      have hxTarget : x = target := by
        simpa [List.getLastD] using hlast
      simpa [hxTarget] using htarget
  | cons y p ih =>
      have hp' : G.CLink x y ∧ G.CPath y p := by
        simpa [CPath] using hp
      have hlastTail : (y :: p).getLastD y = target := by
        simpa [List.getLastD] using hlast
      have hy :=
        ih hp'.2 hlastTail
      rcases hp'.1 with hnode | hface
      · exact G.diskN_rev_ring_node_step hnode hy
      · exact G.diskN_rev_ring_face_step hJ hPlain hr hproper hface hy

theorem diskN_rev_ring
    [Fintype G.Dart]
    (hConn : G.Connected)
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    (hproper : G.ProperRing r)
    (x : G.Dart) :
    G.DiskN (G.RevRing r) x ↔
      ¬ G.DiskN r x := by
  rcases ProperRing.exists_mem (G := G) hproper with ⟨y, hy⟩
  have hconn : G.CConnect x (G.edge y) :=
    Connected.cConnect (G := G) hConn x (G.edge y)
  rcases CConnect.exists_cPath (G := G) hconn with
    ⟨p, hp, hlast⟩
  exact G.diskN_rev_ring_of_cPath hJ hPlain hr hproper hp hlast
    (G.diskN_rev_ring_base hJ hPlain hr hproper hy)

theorem diskF_rev_ring
    [Fintype G.Dart]
    (hConn : G.Connected)
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    (hproper : G.ProperRing r)
    (x : G.Dart) :
    G.DiskF (G.RevRing r) x ↔
      ¬ G.DiskN r x ∧ ¬ G.FaceBand r x := by
  rw [DiskF, G.diskN_rev_ring hConn hJ hPlain hr hproper x,
    FaceBand.revRing_iff_of_plain (G := G) hPlain hr.1]

theorem Plain.face_eq_node_node_edge_of_cubic
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.face x = G.node (G.node (G.edge x)) := by
  calc
    G.face x =
        G.node (G.node (G.node (G.face x))) := by
          exact (hCubic (G.face x)).1.symm
    _ = G.node (G.node (G.edge x)) := by
          rw [Plain.node_face_eq_edge (G := G) hPlain x]

theorem Cubic.node_node_eq_face_edge
    (hG : G.Cubic)
    (x : G.Dart) :
    G.node (G.node x) = G.face (G.edge x) :=
  Hypermap.node_node_eq_face_edge_of_period_three (hG x).1

theorem edge_node_edge_node_eq_face_symm_face_symm
    (x : G.Dart) :
    G.edge (G.node (G.edge (G.node x))) =
      G.face.symm (G.face.symm x) := by
  apply G.face.injective
  apply G.face.injective
  simp [Hypermap.face_edge_node]

theorem Plain.mirror_edge_eq_face_edge_face_symm
    (hG : G.Plain)
    (x : G.Dart) :
    G.mirror.edge x = G.face (G.edge (G.face.symm x)) := by
  change G.face (G.node x) = G.face (G.edge (G.face.symm x))
  congr 1
  simpa using Plain.node_face_eq_edge (G := G) hG (G.face.symm x)

theorem Plain.mirror
    (hG : G.Plain) :
    G.mirror.Plain := by
  intro x
  constructor
  · change G.face (G.node (G.face (G.node x))) = x
    rw [Plain.node_face_eq_edge (G := G) hG (G.node x)]
    exact G.face_edge_node x
  · intro hfixed
    change G.face (G.node x) = x at hfixed
    have hbad : G.edge (G.node x) = G.node x := by
      calc
        G.edge (G.node x) = G.node (G.face (G.node x)) := by
          exact (Plain.node_face_eq_edge (G := G) hG (G.node x)).symm
        _ = G.node x := by rw [hfixed]
    exact Plain.edge_ne (G := G) hG (G.node x) hbad

theorem Plain.dual
    (hG : G.Plain) :
    G.dual.Plain := by
  intro x
  constructor
  · change G.edge.symm (G.edge.symm x) = x
    rw [Plain.edge_symm_eq (G := G) hG x,
      Plain.edge_symm_eq (G := G) hG (G.edge x)]
    exact Plain.edge_edge (G := G) hG x
  · change G.edge.symm x ≠ x
    rw [Plain.edge_symm_eq (G := G) hG x]
    exact Plain.edge_ne (G := G) hG x

theorem Bridgeless.dual_loopless
    (hG : G.Bridgeless) :
    G.dual.Loopless := by
  intro x hdual
  have hface : PermReachable G.face x (G.edge.symm x) :=
    (permReachable_symmPerm_iff G.face).mp hdual
  have hback : PermReachable G.face (G.edge.symm x) x :=
    PermReachable.symm G.face hface
  exact hG (G.edge.symm x) (by simpa using hback)

theorem Bridgeless.node_ne_self
    (hG : G.Bridgeless)
    (x : G.Dart) :
    G.node x ≠ x := by
  intro hnode
  have hface_edge : G.face (G.edge x) = x := by
    apply G.node.injective
    simp [hnode]
  have hreach_edge_x : PermReachable G.face (G.edge x) x := by
    simpa [hface_edge] using PermReachable.forward G.face (G.edge x)
  exact hG x (PermReachable.symm G.face hreach_edge_x)

theorem Bridgeless.not_faceReachable_node
    (hG : G.Bridgeless)
    (x : G.Dart) :
    ¬ PermReachable G.face x (G.node x) := by
  intro hx
  have hback : PermReachable G.face (G.node x) x :=
    PermReachable.symm G.face hx
  have hprev : PermReachable G.face x (G.face.symm x) :=
    PermReachable.backward G.face x
  have hbridge : PermReachable G.face (G.node x) (G.edge (G.node x)) := by
    have hpath : PermReachable G.face (G.node x) (G.face.symm x) :=
      PermReachable.trans G.face hback hprev
    simpa [edge_node_eq_face_symm (G := G) x] using hpath
  exact hG (G.node x) hbridge

theorem Bridgeless.not_faceReachable_node_left
    (hG : G.Bridgeless)
    (x : G.Dart) :
    ¬ PermReachable G.face (G.node x) x := by
  intro hx
  exact Bridgeless.not_faceReachable_node (G := G) hG x
    (PermReachable.symm G.face hx)

theorem Bridgeless.not_faceReachable_node_symm
    (hG : G.Bridgeless)
    (x : G.Dart) :
    ¬ PermReachable G.face x (G.node.symm x) := by
  intro hx
  have htoEdge :
      PermReachable G.face (G.node.symm x) (G.edge x) := by
    have h := PermReachable.backward G.face (G.face (G.edge x))
    have hface : G.face (G.edge x) = G.node.symm x := by
      apply G.node.injective
      simp [G.node_face_edge x]
    have htarget : G.face.symm (G.node.symm x) = G.edge x := by
      rw [← hface]
      simp
    simpa [hface, htarget] using h
  exact hG x (PermReachable.trans G.face hx htoEdge)

theorem Bridgeless.not_faceReachable_node_symm_left
    (hG : G.Bridgeless)
    (x : G.Dart) :
    ¬ PermReachable G.face (G.node.symm x) x := by
  intro hx
  exact Bridgeless.not_faceReachable_node_symm (G := G) hG x
    (PermReachable.symm G.face hx)

theorem Bridgeless.not_ringAdj_self
    (hG : G.Bridgeless)
    (x : G.Dart) :
    ¬ G.RingAdj x x := by
  rintro ⟨z, hxz, hzx⟩
  have hzEdge : PermReachable G.face z (G.edge z) :=
    PermReachable.trans G.face
      (PermReachable.symm G.face hxz)
      (PermReachable.symm G.face hzx)
  exact hG z hzEdge

theorem Bridgeless.edge_ne_self
    (hG : G.Bridgeless)
    (x : G.Dart) :
    G.edge x ≠ x := by
  intro hfixed
  have hreach : PermReachable G.face x (G.edge x) := by
    rw [hfixed]
    exact PermReachable.refl G.face x
  exact hG x hreach

theorem Loopless.dual_bridgeless
    (hG : G.Loopless) :
    G.dual.Bridgeless := by
  intro x hdual
  have hnode : PermReachable G.node x (G.edge.symm x) :=
    (permReachable_symmPerm_iff G.node).mp hdual
  have hback : PermReachable G.node (G.edge.symm x) x :=
    PermReachable.symm G.node hnode
  exact hG (G.edge.symm x) (by simpa using hback)

theorem Bridgeless.mirror
    (hG : G.Bridgeless) :
    G.mirror.Bridgeless := by
  intro x hmirror
  have hface :
      PermReachable G.face x (G.face (G.node x)) := by
    have hfaceSymm :
        PermReachable G.face.symm x (G.face (G.node x)) := by
      simpa [Hypermap.mirror, Equiv.trans_apply] using hmirror
    exact (permReachable_symmPerm_iff G.face).mp hfaceSymm
  have h_start :
      PermReachable G.face (G.node x) (G.face (G.node x)) :=
    PermReachable.forward G.face (G.node x)
  have h_back :
      PermReachable G.face (G.face (G.node x)) x :=
    PermReachable.symm G.face hface
  have h_prev :
      PermReachable G.face x (G.face.symm x) :=
    PermReachable.backward G.face x
  have hbridge :
      PermReachable G.face (G.node x) (G.edge (G.node x)) := by
    have hpath :
        PermReachable G.face (G.node x) (G.face.symm x) :=
      Relation.ReflTransGen.trans h_start
        (Relation.ReflTransGen.trans h_back h_prev)
    simpa [edge_node_eq_face_symm (G := G) x] using hpath
  exact hG (G.node x) hbridge

theorem Pentagonal.mirror
    (hG : G.Pentagonal) :
    G.mirror.Pentagonal := by
  intro x
  constructor
  · intro hbad
    exact (hG (G.face.symm x)).1 (by simpa using hbad.symm)
  · constructor
    · intro hbad
      exact (hG (G.face.symm (G.face.symm x))).2.1
        (by simpa using hbad.symm)
    · constructor
      · intro hbad
        exact (hG (G.face.symm (G.face.symm (G.face.symm x)))).2.2.1
          (by simpa using hbad.symm)
      · intro hbad
        exact
          (hG (G.face.symm (G.face.symm (G.face.symm (G.face.symm x))))).2.2.2
            (by simpa using hbad.symm)

/-- Euler-planar and bridgeless hypermaps. -/
structure PlanarBridgeless : Prop where
  planar : G.EulerPlanar
  bridgeless : G.Bridgeless

/-- Plain cubic hypermaps. -/
structure PlainCubic : Prop where
  plain : G.Plain
  cubic : G.Cubic

theorem PlainCubic.face_eq_node_node_edge
    (hG : G.PlainCubic)
    (x : G.Dart) :
    G.face x = G.node (G.node (G.edge x)) :=
  Plain.face_eq_node_node_edge_of_cubic
    (G := G) hG.plain hG.cubic x

theorem PlainCubic.node_node_eq_face_edge
    (hG : G.PlainCubic)
    (x : G.Dart) :
    G.node (G.node x) = G.face (G.edge x) :=
  Cubic.node_node_eq_face_edge (G := G) hG.cubic x

/-- Plain cubic connected hypermaps. -/
structure PlainCubicConnected : Prop where
  base : G.PlainCubic
  connected : G.Connected

/-- Euler-planar plain cubic connected hypermaps. -/
structure PlanarPlainCubicConnected : Prop where
  base : G.PlainCubicConnected
  planar : G.EulerPlanar

/-- Plain cubic pentagonal hypermaps. -/
structure PlainCubicPentagonal : Prop where
  base : G.PlainCubic
  pentagonal : G.Pentagonal

/-- Euler-planar bridgeless plain hypermaps. -/
structure PlanarBridgelessPlain : Prop where
  base : G.PlanarBridgeless
  plain : G.Plain

/-- Euler-planar bridgeless plain connected hypermaps. -/
structure PlanarBridgelessPlainConnected : Prop where
  base : G.PlanarBridgelessPlain
  connected : G.Connected

/-- Euler-planar bridgeless plain precubic hypermaps. -/
structure PlanarBridgelessPlainPrecubic : Prop where
  base : G.PlanarBridgelessPlain
  precubic : G.Precubic

theorem PlainCubic.mirror
    (hG : G.PlainCubic) :
    G.mirror.PlainCubic where
  plain := hG.plain.mirror
  cubic := hG.cubic.mirror

theorem PlainCubicConnected.mirror
    (hG : G.PlainCubicConnected) :
    G.mirror.PlainCubicConnected where
  base := hG.base.mirror
  connected := (G.mirror_connected_iff).2 hG.connected

theorem PlanarPlainCubicConnected.mirror
    (hG : G.PlanarPlainCubicConnected) :
    G.mirror.PlanarPlainCubicConnected where
  base := hG.base.mirror
  planar := (G.mirror_eulerPlanar_iff).2 hG.planar

theorem PlainCubicPentagonal.mirror
    (hG : G.PlainCubicPentagonal) :
    G.mirror.PlainCubicPentagonal where
  base := hG.base.mirror
  pentagonal := hG.pentagonal.mirror

theorem PlanarBridgeless.mirror
    (hG : G.PlanarBridgeless) :
    G.mirror.PlanarBridgeless where
  planar := (G.mirror_eulerPlanar_iff).2 hG.planar
  bridgeless := hG.bridgeless.mirror

theorem PlanarBridgelessPlain.mirror
    (hG : G.PlanarBridgelessPlain) :
    G.mirror.PlanarBridgelessPlain where
  base := hG.base.mirror
  plain := hG.plain.mirror

theorem PlanarBridgelessPlainConnected.mirror
    (hG : G.PlanarBridgelessPlainConnected) :
    G.mirror.PlanarBridgelessPlainConnected where
  base := hG.base.mirror
  connected := (G.mirror_connected_iff).2 hG.connected

theorem PlanarBridgelessPlainPrecubic.mirror
    (hG : G.PlanarBridgelessPlainPrecubic) :
    G.mirror.PlanarBridgelessPlainPrecubic where
  base := hG.base.mirror
  precubic := hG.precubic.mirror

private theorem mirror_iff_of_mirror
    (P : Hypermap → Prop)
    (hmirror : ∀ H, P H → P H.mirror) :
    P G.mirror ↔ P G := by
  constructor
  · intro hG
    have hm := hmirror G.mirror hG
    convert hm using 1
    exact (Hypermap.mirror_mirror G).symm
  · exact hmirror G

theorem Plain.mirror_iff :
    G.mirror.Plain ↔ G.Plain :=
  mirror_iff_of_mirror (G := G) (fun H => H.Plain) (fun _ h => h.mirror)

theorem Cubic.mirror_iff :
    G.mirror.Cubic ↔ G.Cubic :=
  mirror_iff_of_mirror (G := G) (fun H => H.Cubic) (fun _ h => h.mirror)

theorem Precubic.mirror_iff :
    G.mirror.Precubic ↔ G.Precubic :=
  mirror_iff_of_mirror (G := G) (fun H => H.Precubic) (fun _ h => h.mirror)

theorem Pentagonal.mirror_iff :
    G.mirror.Pentagonal ↔ G.Pentagonal :=
  mirror_iff_of_mirror (G := G) (fun H => H.Pentagonal) (fun _ h => h.mirror)

theorem PlanarBridgeless.mirror_iff :
    G.mirror.PlanarBridgeless ↔ G.PlanarBridgeless :=
  mirror_iff_of_mirror (G := G) (fun H => H.PlanarBridgeless)
    (fun _ h => h.mirror)

theorem PlainCubic.mirror_iff :
    G.mirror.PlainCubic ↔ G.PlainCubic :=
  mirror_iff_of_mirror (G := G) (fun H => H.PlainCubic) (fun _ h => h.mirror)

theorem PlainCubicConnected.mirror_iff :
    G.mirror.PlainCubicConnected ↔ G.PlainCubicConnected :=
  mirror_iff_of_mirror (G := G) (fun H => H.PlainCubicConnected)
    (fun _ h => h.mirror)

theorem PlanarPlainCubicConnected.mirror_iff :
    G.mirror.PlanarPlainCubicConnected ↔ G.PlanarPlainCubicConnected :=
  mirror_iff_of_mirror (G := G) (fun H => H.PlanarPlainCubicConnected)
    (fun _ h => h.mirror)

theorem PlainCubicPentagonal.mirror_iff :
    G.mirror.PlainCubicPentagonal ↔ G.PlainCubicPentagonal :=
  mirror_iff_of_mirror (G := G) (fun H => H.PlainCubicPentagonal)
    (fun _ h => h.mirror)

theorem PlanarBridgelessPlain.mirror_iff :
    G.mirror.PlanarBridgelessPlain ↔ G.PlanarBridgelessPlain :=
  mirror_iff_of_mirror (G := G) (fun H => H.PlanarBridgelessPlain)
    (fun _ h => h.mirror)

theorem PlanarBridgelessPlainConnected.mirror_iff :
    G.mirror.PlanarBridgelessPlainConnected ↔
      G.PlanarBridgelessPlainConnected :=
  mirror_iff_of_mirror (G := G) (fun H => H.PlanarBridgelessPlainConnected)
    (fun _ h => h.mirror)

theorem PlanarBridgelessPlainPrecubic.mirror_iff :
    G.mirror.PlanarBridgelessPlainPrecubic ↔
      G.PlanarBridgelessPlainPrecubic :=
  mirror_iff_of_mirror (G := G) (fun H => H.PlanarBridgelessPlainPrecubic)
    (fun _ h => h.mirror)

namespace Iso

universe u v

variable {G : Hypermap.{u}} {H : Hypermap.{v}} (φ : Iso G H)

theorem bridgeless
    (φ : Iso G H)
    (hG : G.Bridgeless) :
    H.Bridgeless := by
  intro y hy
  have hback := (φ.symm.faceReachable_iff).mp hy
  exact hG (φ.toEquiv.symm y) (by
    have hEdge :
        φ.toEquiv.symm (H.edge y) = G.edge (φ.toEquiv.symm y) := by
      simpa [Iso.symm] using φ.symm.map_edge y
    convert hback using 1
    exact hEdge.symm)

theorem bridgeless_iff
    (φ : Iso G H) :
    G.Bridgeless ↔ H.Bridgeless :=
  ⟨φ.bridgeless, φ.symm.bridgeless⟩

theorem loopless
    (φ : Iso G H)
    (hG : G.Loopless) :
    H.Loopless := by
  intro y hy
  have hback := (φ.symm.nodeReachable_iff).mp hy
  exact hG (φ.toEquiv.symm y) (by
    have hEdge :
        φ.toEquiv.symm (H.edge y) = G.edge (φ.toEquiv.symm y) := by
      simpa [Iso.symm] using φ.symm.map_edge y
    convert hback using 1
    exact hEdge.symm)

theorem loopless_iff
    (φ : Iso G H) :
    G.Loopless ↔ H.Loopless :=
  ⟨φ.loopless, φ.symm.loopless⟩

private theorem iterate_eq_self_iff_of_semiconj
    {α β : Type _} (e : α ≃ β)
    {f : α → α} {g : β → β}
    (hmap : Function.Semiconj e f g)
    (n : Nat) (y : β) :
    (g^[n]) y = y ↔ (f^[n]) (e.symm y) = e.symm y := by
  constructor
  · intro h
    apply e.injective
    rw [hmap.iterate_right n]
    simpa using h
  · intro h
    calc
      (g^[n]) y = (g^[n]) (e (e.symm y)) := by simp
      _ = e ((f^[n]) (e.symm y)) := (hmap.iterate_right n _).symm
      _ = e (e.symm y) := congrArg e h
      _ = y := e.apply_symm_apply y

private theorem periodic_moved_of_semiconj
    {α β : Type _} (e : α ≃ β)
    {f : α → α} {g : β → β}
    (hmap : Function.Semiconj e f g)
    (n : Nat)
    (h : ∀ x, (f^[n]) x = x ∧ f x ≠ x) :
    ∀ y, (g^[n]) y = y ∧ g y ≠ y := by
  intro y
  constructor
  · exact (iterate_eq_self_iff_of_semiconj e hmap n y).2 (h _).1
  · intro hfixed
    exact (h _).2 ((iterate_eq_self_iff_of_semiconj e hmap 1 y).1
      (by simpa only [Function.iterate_one] using hfixed))

private theorem period_at_most_three_of_semiconj
    {α β : Type _} (e : α ≃ β)
    {f : α → α} {g : β → β}
    (hmap : Function.Semiconj e f g)
    (h : ∀ x, f x = x ∨ f (f x) = x ∨ f (f (f x)) = x) :
    ∀ y, g y = y ∨ g (g y) = y ∨ g (g (g y)) = y := by
  intro y
  rcases h (e.symm y) with h1 | h2 | h3
  · left
    have h' := (iterate_eq_self_iff_of_semiconj e hmap 1 y).2
      (by simpa only [Function.iterate_one] using h1)
    simpa only [Function.iterate_one] using h'
  · right
    left
    have h' := (iterate_eq_self_iff_of_semiconj e hmap 2 y).2
      (by simpa [Function.iterate_succ_apply] using h2)
    simpa [Function.iterate_succ_apply] using h'
  · right
    right
    have h' := (iterate_eq_self_iff_of_semiconj e hmap 3 y).2
      (by simpa [Function.iterate_succ_apply] using h3)
    simpa [Function.iterate_succ_apply] using h'

private theorem first_four_moved_of_semiconj
    {α β : Type _} (e : α ≃ β)
    {f : α → α} {g : β → β}
    (hmap : Function.Semiconj e f g)
    (h : ∀ x,
      x ≠ f x ∧ x ≠ f (f x) ∧
        x ≠ f (f (f x)) ∧ x ≠ f (f (f (f x)))) :
    ∀ y,
      y ≠ g y ∧ y ≠ g (g y) ∧
        y ≠ g (g (g y)) ∧ y ≠ g (g (g (g y))) := by
  intro y
  have moved (n : Nat)
      (hn : e.symm y ≠ (f^[n]) (e.symm y)) :
      y ≠ (g^[n]) y := by
    intro hfixed
    exact hn ((iterate_eq_self_iff_of_semiconj e hmap n y).1 hfixed.symm).symm
  rcases h (e.symm y) with ⟨h1, h2, h3, h4⟩
  constructor
  · simpa only [Function.iterate_one] using moved 1 (by
      simpa only [Function.iterate_one] using h1)
  · constructor
    · simpa [Function.iterate_succ_apply] using moved 2 (by
        simpa [Function.iterate_succ_apply] using h2)
    · constructor
      · simpa [Function.iterate_succ_apply] using moved 3 (by
          simpa [Function.iterate_succ_apply] using h3)
      · simpa [Function.iterate_succ_apply] using moved 4 (by
          simpa [Function.iterate_succ_apply] using h4)

theorem plain
    (φ : Iso G H)
    (hG : G.Plain) :
    H.Plain := by
  simpa [Function.iterate_succ_apply] using
    periodic_moved_of_semiconj φ.toEquiv
      (show Function.Semiconj φ.toEquiv G.edge H.edge from φ.map_edge)
      2 (fun x => by
        simpa [Function.iterate_succ_apply] using hG x)

theorem plain_iff
    (φ : Iso G H) :
    G.Plain ↔ H.Plain :=
  ⟨φ.plain, φ.symm.plain⟩

theorem cubic
    (φ : Iso G H)
    (hG : G.Cubic) :
    H.Cubic := by
  simpa [Function.iterate_succ_apply] using
    periodic_moved_of_semiconj φ.toEquiv
      (show Function.Semiconj φ.toEquiv G.node H.node from φ.map_node)
      3 (fun x => by
        simpa [Function.iterate_succ_apply] using hG x)

theorem cubic_iff
    (φ : Iso G H) :
    G.Cubic ↔ H.Cubic :=
  ⟨φ.cubic, φ.symm.cubic⟩

theorem precubic
    (φ : Iso G H)
    (hG : G.Precubic) :
    H.Precubic :=
  period_at_most_three_of_semiconj φ.toEquiv
    (show Function.Semiconj φ.toEquiv G.node H.node from φ.map_node) hG

theorem precubic_iff
    (φ : Iso G H) :
    G.Precubic ↔ H.Precubic :=
  ⟨φ.precubic, φ.symm.precubic⟩

theorem pentagonal
    (φ : Iso G H)
    (hG : G.Pentagonal) :
    H.Pentagonal :=
  first_four_moved_of_semiconj φ.toEquiv
    (show Function.Semiconj φ.toEquiv G.face H.face from φ.map_face) hG

theorem pentagonal_iff
    (φ : Iso G H) :
    G.Pentagonal ↔ H.Pentagonal :=
  ⟨φ.pentagonal, φ.symm.pentagonal⟩

theorem plainCubic
    (φ : Iso G H)
    (hG : G.PlainCubic) :
    H.PlainCubic where
  plain := φ.plain hG.plain
  cubic := φ.cubic hG.cubic

theorem plainCubic_iff
    (φ : Iso G H) :
    G.PlainCubic ↔ H.PlainCubic :=
  ⟨φ.plainCubic, φ.symm.plainCubic⟩

theorem plainCubicConnected
    (φ : Iso G H)
    (hG : G.PlainCubicConnected) :
    H.PlainCubicConnected where
  base := φ.plainCubic hG.base
  connected := (φ.connected_iff).mp hG.connected

theorem plainCubicConnected_iff
    (φ : Iso G H) :
    G.PlainCubicConnected ↔ H.PlainCubicConnected :=
  ⟨φ.plainCubicConnected, φ.symm.plainCubicConnected⟩

theorem planarPlainCubicConnected
    (φ : Iso G H)
    (hG : G.PlanarPlainCubicConnected) :
    H.PlanarPlainCubicConnected where
  base := φ.plainCubicConnected hG.base
  planar := (φ.eulerPlanar_iff).mp hG.planar

theorem planarPlainCubicConnected_iff
    (φ : Iso G H) :
    G.PlanarPlainCubicConnected ↔ H.PlanarPlainCubicConnected :=
  ⟨φ.planarPlainCubicConnected, φ.symm.planarPlainCubicConnected⟩

theorem plainCubicPentagonal
    (φ : Iso G H)
    (hG : G.PlainCubicPentagonal) :
    H.PlainCubicPentagonal where
  base := φ.plainCubic hG.base
  pentagonal := φ.pentagonal hG.pentagonal

theorem plainCubicPentagonal_iff
    (φ : Iso G H) :
    G.PlainCubicPentagonal ↔ H.PlainCubicPentagonal :=
  ⟨φ.plainCubicPentagonal, φ.symm.plainCubicPentagonal⟩

theorem planarBridgeless
    (φ : Iso G H)
    (hG : G.PlanarBridgeless) :
    H.PlanarBridgeless where
  planar := (φ.eulerPlanar_iff).mp hG.planar
  bridgeless := φ.bridgeless hG.bridgeless

theorem planarBridgeless_iff
    (φ : Iso G H) :
    G.PlanarBridgeless ↔ H.PlanarBridgeless :=
  ⟨φ.planarBridgeless, φ.symm.planarBridgeless⟩

theorem planarBridgelessPlain
    (φ : Iso G H)
    (hG : G.PlanarBridgelessPlain) :
    H.PlanarBridgelessPlain where
  base := φ.planarBridgeless hG.base
  plain := φ.plain hG.plain

theorem planarBridgelessPlain_iff
    (φ : Iso G H) :
    G.PlanarBridgelessPlain ↔ H.PlanarBridgelessPlain :=
  ⟨φ.planarBridgelessPlain, φ.symm.planarBridgelessPlain⟩

theorem planarBridgelessPlainConnected
    (φ : Iso G H)
    (hG : G.PlanarBridgelessPlainConnected) :
    H.PlanarBridgelessPlainConnected where
  base := φ.planarBridgelessPlain hG.base
  connected := (φ.connected_iff).mp hG.connected

theorem planarBridgelessPlainConnected_iff
    (φ : Iso G H) :
    G.PlanarBridgelessPlainConnected ↔ H.PlanarBridgelessPlainConnected :=
  ⟨φ.planarBridgelessPlainConnected, φ.symm.planarBridgelessPlainConnected⟩

theorem planarBridgelessPlainPrecubic
    (φ : Iso G H)
    (hG : G.PlanarBridgelessPlainPrecubic) :
    H.PlanarBridgelessPlainPrecubic where
  base := {
    base := {
      planar := (φ.eulerPlanar_iff).mp hG.base.base.planar
      bridgeless := φ.bridgeless hG.base.base.bridgeless }
    plain := φ.plain hG.base.plain
  }
  precubic := φ.precubic hG.precubic

theorem planarBridgelessPlainPrecubic_iff
    (φ : Iso G H) :
    G.PlanarBridgelessPlainPrecubic ↔ H.PlanarBridgelessPlainPrecubic :=
  ⟨φ.planarBridgelessPlainPrecubic, φ.symm.planarBridgelessPlainPrecubic⟩

end Iso

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
