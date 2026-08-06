import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.WalkupE.PathLifting

/-!
The two-face branch obtained by deleting the middle dart with `WalkupE`.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- Special first-step link used after two consecutive face steps: deleting
the middle dart `y` with `WalkupE` turns `x --F--> y --F--> z` into a contour
link from the lifted `x` to the lifted `z`. -/
theorem walkupE_cLink_of_face_eq_deleted_of_face_eq_deleted
    {x y z : G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z) :
    (G.walkupE y).CLink
      (⟨x, hx⟩ : (G.walkupE y).Dart)
      (⟨z, hz⟩ : (G.walkupE y).Dart) := by
  right
  apply Subtype.ext
  have hface_apply :
      ((G.walkupE y).face
        (⟨x, hx⟩ : (G.walkupE y).Dart)).1 = G.face y :=
    G.walkupE_face_apply_coe_of_eq
      (⟨x, hx⟩ : (G.walkupE y).Dart) hface₁
  exact (hface_apply.trans hface₂).symm

/-- Path package for the Coq `t = y` reduction: after two consecutive face
steps, delete the middle dart with `WalkupE`, use the special first link, and
lift the remaining tail generically. -/
theorem walkupE_liftCPath_of_face_eq_deleted_of_face_eq_deleted
    {x y z : G.Dart} {p : List G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (havoid : y ∉ z :: p)
    (hp : G.CPath z p) :
    ∃ q : List (G.walkupE y).Dart,
      q.map Subtype.val = z :: p ∧
        (G.walkupE y).CPath
          (⟨x, hx⟩ : (G.walkupE y).Dart) q := by
  rcases G.walkupE_liftCPath havoid hp with ⟨q, hqmap, hqpath⟩
  have hqpath' :
      (G.walkupE y).CPath
        (⟨z, hz⟩ : (G.walkupE y).Dart) q := by
    convert hqpath using 1
  refine ⟨(⟨z, hz⟩ : (G.walkupE y).Dart) :: q, ?_, ?_⟩
  · change z :: q.map Subtype.val = z :: p
    exact congrArg (fun r : List G.Dart => z :: r) hqmap
  · constructor
    · exact G.walkupE_cLink_of_face_eq_deleted_of_face_eq_deleted
        hx hz hface₁ hface₂
    · exact hqpath'

/-- Coq `planar_Jordan`, `Dt` branch: after two consecutive face steps,
the contrary assumption that the inverse-node endpoint is not the deleted
middle dart lifts the path to a Moebius path in `WalkupE y`. -/
theorem walkupE_liftMoebiusPath_of_face_eq_deleted_of_face_eq_deleted
    {x y z : G.Dart} {p : List G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (havoid : y ∉ z :: p)
    (hpath : G.CPath z p)
    (hnodup : (x :: y :: z :: p).Nodup)
    (ha_ne :
      G.node.symm ((x :: y :: z :: p).getLastD x) ≠ y)
    (hmem :
      ListMemBeforeEq (y :: z :: p)
        (G.node.symm ((x :: y :: z :: p).getLastD x)) (G.node x)) :
    ∃ q : List (G.walkupE y).Dart,
      q.map Subtype.val = z :: p ∧
        (G.walkupE y).MoebiusPath
          ((⟨x, hx⟩ : (G.walkupE y).Dart) :: q) := by
  let H : Hypermap := G.walkupE y
  let ux : H.Dart := ⟨x, hx⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = z :: p ∧ H.MoebiusPath (ux :: q)
  rcases G.walkupE_liftCPath_of_face_eq_deleted_of_face_eq_deleted
      hx hz hface₁ hface₂ havoid hpath with
    ⟨q, hqmap, hqpath⟩
  change H.CPath ux q at hqpath
  have hmap_all : (ux :: q).map Subtype.val = x :: z :: p := by
    change x :: q.map Subtype.val = x :: z :: p
    exact congrArg (fun s : List G.Dart => x :: s) hqmap
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
  have hnodup_map : ((ux :: q).map Subtype.val).Nodup := by
    rw [hmap_all]
    exact hnodup_xzp
  have hnodup_lift : (ux :: q).Nodup :=
    (List.nodup_map_iff Subtype.val_injective).mp hnodup_map
  let L : G.Dart := (x :: y :: z :: p).getLastD x
  let a : G.Dart := G.node.symm L
  let b : G.Dart := G.node x
  have ha_ne' : a ≠ y := by
    simpa [a, L] using ha_ne
  have hmem_tail : ListMemBeforeEq (z :: p) a b := by
    exact ListMemBeforeEq.tail_of_cons_ne
      (by simpa [a, b, L] using hmem) ha_ne'
  have hb_ne : b ≠ y := by
    have hb_mem : b ∈ z :: p := ListMemBeforeEq.right_mem hmem_tail
    intro hby
    exact havoid (by
      simpa [hby] using hb_mem)
  let ua : H.Dart := ⟨a, ha_ne'⟩
  let ub : H.Dart := ⟨b, hb_ne⟩
  have hnode_ux : H.node ux = ub := by
    apply Subtype.ext
    change ((G.walkupE y).node (⟨x, hx⟩ : (G.walkupE y).Dart)).1 = b
    have hnode_apply :
        ((G.walkupE y).node
          (⟨x, hx⟩ : (G.walkupE y).Dart)).1 = G.node x :=
      G.walkupE_node_apply_coe_of_ne
        (⟨x, hx⟩ : (G.walkupE y).Dart)
        (by
          change G.node x ≠ y
          exact hb_ne)
    simpa [b] using hnode_apply
  have hlast_val :
      ((ux :: q).getLastD ux).1 = L := by
    have h1 : ((ux :: q).map Subtype.val).getLastD x =
        (x :: z :: p).getLastD x := by
      simpa [ux] using
        congrArg (fun l : List G.Dart => l.getLastD x) hmap_all
    have h2 : ((ux :: q).map Subtype.val).getLastD x =
        ((ux :: q).getLastD ux).1 := by
      simpa [ux] using
        (List.getLastD_map (f := Subtype.val)
          (l := ux :: q) (a := ux))
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
  have hnode_a_ne : G.node a ≠ y := by
    intro hnodea
    exact hlast_ne (by
      calc
        L = G.node a := by simp [a]
        _ = y := hnodea)
  have hnode_ua : H.node ua = (ux :: q).getLastD ux := by
    apply Subtype.ext
    change ((G.walkupE y).node ua).1 = ((ux :: q).getLastD ux).1
    rw [G.walkupE_node_apply_coe_of_ne]
    · calc
        G.node a = L := by simp [a]
        _ = ((ux :: q).getLastD ux).1 := hlast_val.symm
    · exact hnode_a_ne
  have hnodeSymm_last :
      H.node.symm ((ux :: q).getLastD ux) = ua := by
    calc
      H.node.symm ((ux :: q).getLastD ux) =
          H.node.symm (H.node ua) := by rw [hnode_ua]
      _ = ua := by simp
  have hmem_map : ListMemBeforeEq (q.map Subtype.val) a b := by
    rw [hqmap]
    exact hmem_tail
  have hmem_lift : ListMemBeforeEq q ua ub :=
    ListMemBeforeEq.of_map_injective
      (f := Subtype.val) Subtype.val_injective
      (by simpa [ua, ub] using hmem_map)
  refine ⟨q, hqmap, ?_⟩
  apply MoebiusPath.of_cons (G := H) hnodup_lift hqpath
  rw [hnodeSymm_last, hnode_ux]
  exact hmem_lift

/-- Coq `planar_Jordan`, `Dt`: after `face x = y` and `face y = z`,
Jordan for `WalkupE y` forces the inverse-node endpoint of the original
Moebius path to be exactly the deleted middle dart. -/
theorem walkupE_forces_inverse_node_endpoint_of_two_faces
    {x y z : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupE y).Jordan)
    (hm : G.MoebiusPath (x :: y :: z :: p))
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z) :
    G.node.symm ((x :: y :: z :: p).getLastD x) = y := by
  by_contra ha_ne
  have hnodup : (x :: y :: z :: p).Nodup :=
    MoebiusPath.nodup (G := G) hm
  have hnodup_yzp : (y :: z :: p).Nodup :=
    List.Nodup.of_cons hnodup
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
  rcases hyzp with ⟨_hyz, hpath⟩
  rcases G.walkupE_liftMoebiusPath_of_face_eq_deleted_of_face_eq_deleted
      hx hz hface₁ hface₂ havoid hpath hnodup ha_ne hmem with
    ⟨q, _hqmap, hq⟩
  exact hJ ((⟨x, hx⟩ : (G.walkupE y).Dart) :: q) hq

end Hypermap
end FourColor
end Schematic.Math.GraphTheory

