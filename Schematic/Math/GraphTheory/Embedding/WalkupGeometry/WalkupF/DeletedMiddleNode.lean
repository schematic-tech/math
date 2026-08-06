import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.WalkupF.PathLifting

/-!
The remaining `WalkupF` branch obtained by deleting a middle node dart.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- Coq `planar_Jordan`, `WalkupF` path package: the special first link after
deleting the middle dart, followed by the generic lifted tail. -/
theorem walkupF_liftCPath_of_face_eq_deleted_of_node_eq_deleted
    {x y z : G.Dart} {p : List G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface : G.face x = y)
    (hnode : G.node z = y)
    (havoidFaceEdge : G.face (G.edge y) ∉ p)
    (havoid : y ∉ z :: p)
    (hp : G.CPath z p) :
    ∃ q : List (G.walkupF y).Dart,
      q.map Subtype.val = z :: p ∧
        (G.walkupF y).CPath
          (⟨x, hx⟩ : (G.walkupF y).Dart) q := by
  rcases G.walkupF_liftCPath havoidFaceEdge havoid hp with
    ⟨q, hqmap, hqpath⟩
  have hqpath' :
      (G.walkupF y).CPath
        (⟨z, hz⟩ : (G.walkupF y).Dart) q := by
    convert hqpath using 1
  refine ⟨(⟨z, hz⟩ : (G.walkupF y).Dart) :: q, ?_, ?_⟩
  · change z :: q.map Subtype.val = z :: p
    exact congrArg (fun r : List G.Dart => z :: r) hqmap
  · constructor
    · exact G.walkupF_cLink_of_face_eq_deleted_of_node_eq_deleted
        hx hz hface hnode
    · exact hqpath'

/-- Coq `planar_Jordan`, `WalkupF` Moebius package for the `Dfy` branch:
after `face x = y`, a contrary reverse-node step through the deleted dart
`y` lifts to a Moebius path in `WalkupF y`.  The split on
`G.node.symm last = y` is the Lean form of Coq's `insubd` case split. -/
theorem walkupF_liftMoebiusPath_of_face_eq_deleted_of_node_eq_deleted
    {x y z : G.Dart} {p : List G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface : G.face x = y)
    (hnode : G.node z = y)
    (havoidFaceEdge : G.face (G.edge y) ∉ p)
    (havoid : y ∉ z :: p)
    (hpath : G.CPath z p)
    (hnodup : (x :: y :: z :: p).Nodup)
    (hmem :
      ListMemBeforeEq (y :: z :: p)
        (G.node.symm ((x :: y :: z :: p).getLastD x)) (G.node x)) :
    ∃ q : List (G.walkupF y).Dart,
      q.map Subtype.val = z :: p ∧
        (G.walkupF y).MoebiusPath
          ((⟨x, hx⟩ : (G.walkupF y).Dart) :: q) := by
  let H : Hypermap := G.walkupF y
  let ux : H.Dart := ⟨x, hx⟩
  let uz : H.Dart := ⟨z, hz⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = z :: p ∧ H.MoebiusPath (ux :: q)
  rcases G.walkupF_liftCPath havoidFaceEdge havoid hpath with
    ⟨r, hrmap, hrpath⟩
  have hrpath' : H.CPath uz r := by
    simpa [H, uz] using hrpath
  have hqpath : H.CPath ux (uz :: r) := by
    constructor
    · exact G.walkupF_cLink_of_face_eq_deleted_of_node_eq_deleted
        hx hz hface hnode
    · exact hrpath'
  have hqmap : (uz :: r).map Subtype.val = z :: p := by
    change z :: r.map Subtype.val = z :: p
    exact congrArg (fun s : List G.Dart => z :: s) hrmap
  have hmap_all : (ux :: uz :: r).map Subtype.val = x :: z :: p := by
    change x :: z :: r.map Subtype.val = x :: z :: p
    exact congrArg (fun s : List G.Dart => x :: z :: s) hrmap
  have hx_not_zp : x ∉ z :: p := by
    have hx_not_yzp : x ∉ y :: z :: p :=
      List.Nodup.notMem hnodup
    intro hxmem
    exact hx_not_yzp (by
      right
      exact hxmem)
  have hnodup_yzp : (y :: z :: p).Nodup :=
    List.Nodup.of_cons hnodup
  have hnodup_zp : (z :: p).Nodup :=
    List.Nodup.of_cons hnodup_yzp
  have hnodup_xzp : (x :: z :: p).Nodup :=
    List.nodup_cons.mpr ⟨hx_not_zp, hnodup_zp⟩
  have hnodup_map : ((ux :: uz :: r).map Subtype.val).Nodup := by
    rw [hmap_all]
    exact hnodup_xzp
  have hnodup_lift : (ux :: uz :: r).Nodup :=
    (List.nodup_map_iff Subtype.val_injective).mp hnodup_map
  let L : G.Dart := (x :: y :: z :: p).getLastD x
  let a : G.Dart := G.node.symm L
  let b : G.Dart := G.node x
  have hlast_val :
      ((ux :: uz :: r).getLastD ux).1 = L := by
    have h1 : ((ux :: uz :: r).map Subtype.val).getLastD x =
        (x :: z :: p).getLastD x := by
      simpa [ux, uz] using
        congrArg (fun l : List G.Dart => l.getLastD x) hmap_all
    have h2 : ((ux :: uz :: r).map Subtype.val).getLastD x =
        ((ux :: uz :: r).getLastD ux).1 := by
      simpa [ux] using
        (List.getLastD_map (f := Subtype.val)
          (l := ux :: uz :: r) (a := ux))
    have hlast_delete : (x :: z :: p).getLastD x = L := by
      dsimp [L]
      cases p with
      | nil =>
          simp [List.getLastD]
      | cons w ws =>
          simp [List.getLastD]
    exact h2.symm.trans (h1.trans hlast_delete)
  have hlast_mem_tail : L ∈ z :: p := by
    dsimp [L]
    cases p with
    | nil =>
        simp [List.getLastD]
    | cons w ws =>
        right
        change (w :: ws).getLast (by simp) ∈ w :: ws
        exact List.getLast_mem (l := w :: ws) (by simp)
  have hlast_ne : L ≠ y := by
    intro hLy
    exact havoid (by
      simpa [hLy] using hlast_mem_tail)
  have hnode_y_ne : G.node y ≠ y := by
    intro hyy
    have hyz : y = z := by
      apply G.node.injective
      calc
        G.node y = y := hyy
        _ = G.node z := hnode.symm
    exact hz hyz.symm
  have hb_ne : b ≠ y := by
    intro hby
    have hxz : x = z := by
      apply G.node.injective
      calc
        G.node x = y := hby
        _ = G.node z := hnode.symm
    have hx_not_yzp : x ∉ y :: z :: p :=
      List.Nodup.notMem hnodup
    exact hx_not_yzp (by
      right
      rw [hxz]
      exact List.Mem.head p)
  let ub : H.Dart := ⟨b, hb_ne⟩
  have hnode_ux : H.node ux = ub := by
    apply Subtype.ext
    change ((G.permFace.walkupE y).face
      (⟨x, hx⟩ : (G.permFace.walkupE y).Dart)).1 = b
    have hface_apply :
        ((G.permFace.walkupE y).face
          (⟨x, hx⟩ : (G.permFace.walkupE y).Dart)).1 = G.node x := by
      exact G.permFace.walkupE_face_apply_coe_of_ne
        (⟨x, hx⟩ : (G.permFace.walkupE y).Dart)
        (by
          change G.node x ≠ y
          exact hb_ne)
    simpa [Hypermap.permFace, b] using hface_apply
  refine ⟨uz :: r, hqmap, ?_⟩
  apply MoebiusPath.of_cons (G := H) hnodup_lift hqpath
  rw [hnode_ux]
  by_cases ha : a = y
  · have hnode_uz : H.node uz = (ux :: uz :: r).getLastD ux := by
      apply Subtype.ext
      change ((G.permFace.walkupE y).face
        (⟨z, hz⟩ : (G.permFace.walkupE y).Dart)).1 =
          ((ux :: uz :: r).getLastD ux).1
      have hface_apply :
          ((G.permFace.walkupE y).face
            (⟨z, hz⟩ : (G.permFace.walkupE y).Dart)).1 =
              G.node y := by
        exact G.permFace.walkupE_face_apply_coe_of_eq
          (⟨z, hz⟩ : (G.permFace.walkupE y).Dart)
          (by
            change G.node z = y
            exact hnode)
      have hnode_y_L : G.node y = L := by
        rw [← ha]
        change G.node (G.node.symm L) = L
        simp
      exact hface_apply.trans (hnode_y_L.trans hlast_val.symm)
    have hnodeSymm_last :
        H.node.symm ((ux :: uz :: r).getLastD ux) = uz := by
      calc
        H.node.symm ((ux :: uz :: r).getLastD ux) =
            H.node.symm (H.node uz) := by rw [hnode_uz]
        _ = uz := by simp
    have hb_mem_full : b ∈ y :: z :: p :=
      ListMemBeforeEq.right_mem hmem
    have hb_mem_tail : b ∈ z :: p := by
      rw [List.mem_cons] at hb_mem_full
      rcases hb_mem_full with hby | hb_tail
      · exact (hb_ne hby).elim
      · exact hb_tail
    have hb_mem_map : b ∈ (uz :: r).map Subtype.val := by
      rw [hqmap]
      exact hb_mem_tail
    have hb_mem_map' : Subtype.val ub ∈ (uz :: r).map Subtype.val := by
      change b ∈ (uz :: r).map Subtype.val
      exact hb_mem_map
    have hb_mem_q : ub ∈ uz :: r :=
      (List.mem_map_of_injective Subtype.val_injective
        (a := ub) (l := uz :: r)).mp hb_mem_map'
    rw [hnodeSymm_last]
    exact ListMemBeforeEq.cons_self r uz ub hb_mem_q
  · let ua : H.Dart := ⟨a, ha⟩
    have hnode_a_ne : G.node a ≠ y := by
      intro hnodea
      exact hlast_ne (by
        calc
          L = G.node a := by simp [a]
          _ = y := hnodea)
    have hnode_ua : H.node ua = (ux :: uz :: r).getLastD ux := by
      apply Subtype.ext
      change ((G.permFace.walkupE y).face
        (⟨a, ha⟩ : (G.permFace.walkupE y).Dart)).1 =
          ((ux :: uz :: r).getLastD ux).1
      have hface_apply :
          ((G.permFace.walkupE y).face
            (⟨a, ha⟩ : (G.permFace.walkupE y).Dart)).1 =
              G.node a := by
        exact G.permFace.walkupE_face_apply_coe_of_ne
          (⟨a, ha⟩ : (G.permFace.walkupE y).Dart)
          (by
            change G.node a ≠ y
            exact hnode_a_ne)
      have hnode_a_L : G.node a = L := by
        change G.node (G.node.symm L) = L
        simp
      exact hface_apply.trans (hnode_a_L.trans hlast_val.symm)
    have hnodeSymm_last :
        H.node.symm ((ux :: uz :: r).getLastD ux) = ua := by
      calc
        H.node.symm ((ux :: uz :: r).getLastD ux) =
            H.node.symm (H.node ua) := by rw [hnode_ua]
        _ = ua := by simp
    have hmem_tail : ListMemBeforeEq (z :: p) a b :=
      ListMemBeforeEq.tail_of_cons_ne hmem ha
    have hmem_map : ListMemBeforeEq ((uz :: r).map Subtype.val) a b := by
      rw [hqmap]
      exact hmem_tail
    have hmem_lift : ListMemBeforeEq (uz :: r) ua ub :=
      ListMemBeforeEq.of_map_injective
        (f := Subtype.val) Subtype.val_injective
        (by simpa [ua, ub] using hmem_map)
    rw [hnodeSymm_last]
    exact hmem_lift

/-- Coq `planar_Jordan`, `Dfy` wrapper: once the first step has been forced
to be `face x = y`, Jordan for `WalkupF y` rules out the contrary
reverse-node link from `y` to `z`; hence the second step is also a face step. -/
theorem walkupF_forces_second_face_of_first_face
    {x y z : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupF y).Jordan)
    (hm : G.MoebiusPath (x :: y :: z :: p))
    (hface : G.face x = y) :
    G.face y = z := by
  have hnodup : (x :: y :: z :: p).Nodup :=
    MoebiusPath.nodup (G := G) hm
  have hnodup_yzp : (y :: z :: p).Nodup :=
    List.Nodup.of_cons hnodup
  have hnodup_zp : (z :: p).Nodup :=
    List.Nodup.of_cons hnodup_yzp
  have hx : x ≠ y := by
    have hx_not_yzp : x ∉ y :: z :: p :=
      List.Nodup.notMem hnodup
    intro hxy
    exact hx_not_yzp (by simp [hxy])
  have hz : z ≠ y := by
    have hy_not_zp : y ∉ z :: p :=
      List.Nodup.notMem hnodup_yzp
    intro hzy
    exact hy_not_zp (by simp [hzy])
  have havoid : y ∉ z :: p :=
    List.Nodup.notMem hnodup_yzp
  have hmem :
      ListMemBeforeEq (y :: z :: p)
        (G.node.symm ((x :: y :: z :: p).getLastD x)) (G.node x) :=
    MoebiusPath.memBefore (G := G) hm
  have hcp : G.CPath x (y :: z :: p) :=
    MoebiusPath.cPath (G := G) hm
  rcases hcp with ⟨_hxy, hyzp⟩
  rcases hyzp with ⟨hyz, hpath⟩
  rcases hyz with hnodeSymm | hface_yz
  · exfalso
    have hnode : G.node z = y := by
      simp [hnodeSymm]
    have hz_not_p : z ∉ p :=
      List.Nodup.notMem hnodup_zp
    have hfaceEdge : G.face (G.edge y) = z := by
      rw [← hnode]
      exact G.face_edge_node z
    have havoidFaceEdge : G.face (G.edge y) ∉ p := by
      intro hmemEdge
      exact hz_not_p (by
        simpa [hfaceEdge] using hmemEdge)
    rcases G.walkupF_liftMoebiusPath_of_face_eq_deleted_of_node_eq_deleted
        hx hz hface hnode havoidFaceEdge havoid hpath hnodup hmem with
      ⟨q, _hqmap, hq⟩
    exact hJ ((⟨x, hx⟩ : (G.walkupF y).Dart) :: q) hq
  · exact hface_yz.symm

end Hypermap
end FourColor
end Schematic.Math.GraphTheory

