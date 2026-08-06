import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.PathTransport

/-!
Generic contour-path lifting and the first Jordan branch for `WalkupF`.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- Coq `liftF`, one-step form: a contour link avoiding the deleted dart and
the skipped `face (edge z)` lifts through `WalkupF`. -/
theorem walkupF_cLink_lift
    {z x y : G.Dart}
    (hx : x ≠ z) (hy : y ≠ z)
    (hy_face_edge : y ≠ G.face (G.edge z))
    (hxy : G.CLink x y) :
    (G.walkupF z).CLink
      (⟨x, hx⟩ : (G.walkupF z).Dart)
      (⟨y, hy⟩ : (G.walkupF z).Dart) := by
  let P : Hypermap := G.permFace
  let H : Hypermap := P.walkupE z
  change (H.permNode).CLink
    (⟨x, hx⟩ : H.Dart) (⟨y, hy⟩ : H.Dart)
  rcases hxy with hnode | hface
  · left
    have hnode' : G.node y = x := by
      simp [hnode]
    have hfaceH : H.face (⟨y, hy⟩ : H.Dart) =
        (⟨x, hx⟩ : H.Dart) := by
      apply Subtype.ext
      calc
        (H.face (⟨y, hy⟩ : H.Dart)).1 = G.node y := by
          simpa [P, H, Hypermap.permFace] using
            (G.permFace.walkupE_face_apply_coe_of_ne
              (⟨y, hy⟩ : (G.permFace.walkupE z).Dart)
              (by
                change G.node y ≠ z
                rw [hnode']
                exact hx))
        _ = x := hnode'
    calc
      (⟨y, hy⟩ : H.Dart) =
          H.face.symm (H.face (⟨y, hy⟩ : H.Dart)) := by simp
      _ = H.face.symm (⟨x, hx⟩ : H.Dart) := by rw [hfaceH]
  · right
    have hnode_y_edge : G.edge (G.node y) = x := by
      rw [hface]
      exact G.edge_node_face x
    have hnode_y_ne : G.node y ≠ z := by
      intro hny
      apply hy_face_edge
      calc
        y = G.node.symm z := by
          rw [← hny]
          simp
        _ = G.face (G.edge z) := by
          rw [face_edge_eq_node_symm (G := G) z]
    have hface_apply :
        (H.face (⟨y, hy⟩ : H.Dart)).1 = G.node y := by
      simpa [P, H, Hypermap.permFace] using
        (G.permFace.walkupE_face_apply_coe_of_ne
          (⟨y, hy⟩ : (G.permFace.walkupE z).Dart)
          (by
            change G.node y ≠ z
            exact hnode_y_ne))
    have hnode_ne :
        P.node ((H.face (⟨y, hy⟩ : H.Dart)).1) ≠ z := by
      rw [hface_apply]
      change G.edge (G.node y) ≠ z
      rw [hnode_y_edge]
      exact hx
    have hcomp :
        H.node (H.face (⟨y, hy⟩ : H.Dart)) =
          (⟨x, hx⟩ : H.Dart) := by
      apply Subtype.ext
      calc
        (H.node (H.face (⟨y, hy⟩ : H.Dart))).1 =
            P.node ((H.face (⟨y, hy⟩ : H.Dart)).1) := by
          simpa [H] using
            (P.walkupE_node_apply_coe_of_ne
              (H.face (⟨y, hy⟩ : H.Dart)) hnode_ne)
        _ = x := by
          rw [hface_apply]
          change G.edge (G.node y) = x
          exact hnode_y_edge
    have hedgeH : H.edge (⟨x, hx⟩ : H.Dart) =
        (⟨y, hy⟩ : H.Dart) := by
      change (H.face.trans H.node).symm (⟨x, hx⟩ : H.Dart) =
        (⟨y, hy⟩ : H.Dart)
      rw [← hcomp]
      simp
    exact hedgeH.symm

/-- Special first-step link used in Coq `planar_Jordan`: after deleting the
middle dart `y` with `WalkupF`, a face step `x --F--> y` followed by a
reverse-node step `z --N--> y` becomes a contour link from `x` to `z`. -/
theorem walkupF_cLink_of_face_eq_deleted_of_node_eq_deleted
    {x y z : G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface : G.face x = y)
    (hnode : G.node z = y) :
    (G.walkupF y).CLink
      (⟨x, hx⟩ : (G.walkupF y).Dart)
      (⟨z, hz⟩ : (G.walkupF y).Dart) := by
  let P : Hypermap := G.permFace
  let K : Hypermap := P.walkupE y
  change (K.permNode).CLink
    (⟨x, hx⟩ : K.Dart) (⟨z, hz⟩ : K.Dart)
  right
  have hface_z :
      (K.face (⟨z, hz⟩ : K.Dart)).1 = G.node y := by
    simpa [P, K, Hypermap.permFace] using
      (G.permFace.walkupE_face_apply_coe_of_eq
        (⟨z, hz⟩ : (G.permFace.walkupE y).Dart)
        (by
          change G.node z = y
          exact hnode))
  have hedge_node_y : G.edge (G.node y) = x := by
    rw [← hface]
    exact G.edge_node_face x
  have hnode_ne :
      P.node ((K.face (⟨z, hz⟩ : K.Dart)).1) ≠ y := by
    rw [hface_z]
    change G.edge (G.node y) ≠ y
    rw [hedge_node_y]
    exact hx
  have hcomp :
      K.node (K.face (⟨z, hz⟩ : K.Dart)) =
        (⟨x, hx⟩ : K.Dart) := by
    apply Subtype.ext
    calc
      (K.node (K.face (⟨z, hz⟩ : K.Dart))).1 =
          P.node ((K.face (⟨z, hz⟩ : K.Dart)).1) := by
        simpa [K] using
          (P.walkupE_node_apply_coe_of_ne
            (K.face (⟨z, hz⟩ : K.Dart)) hnode_ne)
      _ = x := by
        rw [hface_z]
        change G.edge (G.node y) = x
        exact hedge_node_y
  have hedgeK : K.edge (⟨x, hx⟩ : K.Dart) =
      (⟨z, hz⟩ : K.Dart) := by
    change (K.face.trans K.node).symm (⟨x, hx⟩ : K.Dart) =
      (⟨z, hz⟩ : K.Dart)
    rw [← hcomp]
    simp
  exact hedgeK.symm

/-- Coq `liftF`: a contour path avoiding `z`, with no tail hit of
`face (edge z)`, lifts through `WalkupF`. -/
theorem walkupF_liftCPath
    {z x : G.Dart} {p : List G.Dart}
    (havoidFaceEdge : G.face (G.edge z) ∉ p)
    (havoid : z ∉ x :: p)
    (hp : G.CPath x p) :
    ∃ q : List (G.walkupF z).Dart,
      q.map Subtype.val = p ∧
        (G.walkupF z).CPath
          (⟨x, by
            intro hxz
            exact havoid (by simp [hxz])⟩ : (G.walkupF z).Dart) q := by
  have hx : x ≠ z := by
    intro hxz
    exact havoid (by simp [hxz])
  have havoidTail : z ∉ p := by
    intro hz
    exact havoid (by simp [hz])
  have hgood : ∀ y ∈ p, y ≠ G.face (G.edge z) := by
    intro y hy hyFaceEdge
    subst y
    exact havoidFaceEdge hy
  simpa [CPath] using
    (liftRelPathThroughDeletedPoint
      (z := z) (x := x) (p := p)
      (R := G.CLink) (S := (G.walkupF z).CLink)
      (fun y => y ≠ G.face (G.edge z)) hx havoidTail hgood
      (fun ha hb hfaceEdge hlink =>
        G.walkupF_cLink_lift ha hb hfaceEdge hlink) hp)

/-- Path package for the final nonempty-tail Coq branch: after
`x --F--> y --F--> z` and `node t = z`, deleting `z` with `WalkupF` skips the
middle dart and lifts the remaining tail. -/
theorem walkupF_liftCPath_of_two_faces_node_delete_third
    {x y z t : G.Dart} {p : List G.Dart}
    (hxz : x ≠ z) (hyz : y ≠ z) (htz : t ≠ z) (hyt : y ≠ t)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (hnode_t : G.node t = z)
    (havoidFaceEdge : G.face (G.edge z) ∉ p)
    (havoid : z ∉ t :: p)
    (hp : G.CPath t p) :
    ∃ q : List (G.walkupF z).Dart,
      q.map Subtype.val = y :: t :: p ∧
        (G.walkupF z).CPath
          (⟨x, hxz⟩ : (G.walkupF z).Dart) q := by
  let H : Hypermap := G.walkupF z
  let ux : H.Dart := ⟨x, hxz⟩
  let uy : H.Dart := ⟨y, hyz⟩
  let ut : H.Dart := ⟨t, htz⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = y :: t :: p ∧ H.CPath ux q
  rcases G.walkupF_liftCPath havoidFaceEdge havoid hp with
    ⟨r, hrmap, hrpath⟩
  have hrpath' : H.CPath ut r := by
    simpa [H, ut] using hrpath
  have hfaceEdge : G.face (G.edge z) = t := by
    rw [← hnode_t]
    exact G.face_edge_node t
  have hy_face_edge : y ≠ G.face (G.edge z) := by
    intro hybad
    exact hyt (by rw [hybad, hfaceEdge])
  refine ⟨uy :: ut :: r, ?_, ?_⟩
  · change y :: t :: r.map Subtype.val = y :: t :: p
    exact congrArg (fun s : List G.Dart => y :: t :: s) hrmap
  · constructor
    · exact G.walkupF_cLink_lift hxz hyz hy_face_edge
        (Or.inr hface₁.symm)
    · constructor
      · exact G.walkupF_cLink_of_face_eq_deleted_of_node_eq_deleted
          hyz htz hface₂ hnode_t
      · exact hrpath'

/-- Final nonempty-tail Coq branch: with `face x = y`, `face y = z`,
endpoint `y`, `node x = y`, and `node t = z`, the `WalkupF z` lift gives a
smaller Moebius path. -/
theorem walkupF_liftMoebiusPath_of_two_faces_node_delete_third
    {x y z t : G.Dart} {p : List G.Dart}
    (hxz : x ≠ z) (hyz : y ≠ z) (htz : t ≠ z) (hyt : y ≠ t)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (hnode_x : G.node x = y)
    (hnode_t : G.node t = z)
    (hendpoint :
      G.node.symm ((x :: y :: z :: t :: p).getLastD x) = y)
    (havoidFaceEdge : G.face (G.edge z) ∉ p)
    (havoid : z ∉ t :: p)
    (hpath : G.CPath t p)
    (hnodup : (x :: y :: z :: t :: p).Nodup) :
    ∃ q : List (G.walkupF z).Dart,
      q.map Subtype.val = y :: t :: p ∧
        (G.walkupF z).MoebiusPath
          ((⟨x, hxz⟩ : (G.walkupF z).Dart) :: q) := by
  let H : Hypermap := G.walkupF z
  let ux : H.Dart := ⟨x, hxz⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = y :: t :: p ∧ H.MoebiusPath (ux :: q)
  rcases G.walkupF_liftCPath_of_two_faces_node_delete_third
      hxz hyz htz hyt hface₁ hface₂ hnode_t havoidFaceEdge havoid hpath with
    ⟨q, hqmap, hqpath⟩
  change H.CPath ux q at hqpath
  have hmap_all : (ux :: q).map Subtype.val = x :: y :: t :: p := by
    change x :: q.map Subtype.val = x :: y :: t :: p
    exact congrArg (fun s : List G.Dart => x :: s) hqmap
  have hnodup_yztp : (y :: z :: t :: p).Nodup :=
    List.Nodup.of_cons hnodup
  have hnodup_ztp : (z :: t :: p).Nodup :=
    List.Nodup.of_cons hnodup_yztp
  have hnodup_tp : (t :: p).Nodup :=
    List.Nodup.of_cons hnodup_ztp
  have hy_not_tp : y ∉ t :: p := by
    have hy_not_ztp : y ∉ z :: t :: p :=
      List.Nodup.notMem hnodup_yztp
    intro hymem
    exact hy_not_ztp (by
      right
      exact hymem)
  have hx_not_ytp : x ∉ y :: t :: p := by
    have hx_not_yztp : x ∉ y :: z :: t :: p :=
      List.Nodup.notMem hnodup
    intro hxmem
    rw [List.mem_cons] at hxmem
    rcases hxmem with hxy | hxmem
    · exact hx_not_yztp (by
        rw [hxy]
        exact List.Mem.head (z :: t :: p))
    · exact hx_not_yztp (by
        right
        right
        exact hxmem)
  have hnodup_ytp : (y :: t :: p).Nodup :=
    List.nodup_cons.mpr ⟨hy_not_tp, hnodup_tp⟩
  have hnodup_xytp : (x :: y :: t :: p).Nodup :=
    List.nodup_cons.mpr ⟨hx_not_ytp, hnodup_ytp⟩
  have hnodup_map : ((ux :: q).map Subtype.val).Nodup := by
    rw [hmap_all]
    exact hnodup_xytp
  have hnodup_lift : (ux :: q).Nodup :=
    (List.nodup_map_iff Subtype.val_injective).mp hnodup_map
  let L : G.Dart := (x :: y :: z :: t :: p).getLastD x
  have hlast_val :
      ((ux :: q).getLastD ux).1 = L := by
    have h1 : ((ux :: q).map Subtype.val).getLastD x =
        (x :: y :: t :: p).getLastD x := by
      simpa [ux] using
        congrArg (fun l : List G.Dart => l.getLastD x) hmap_all
    have h2 : ((ux :: q).map Subtype.val).getLastD x =
        ((ux :: q).getLastD ux).1 := by
      simpa [ux] using
        (List.getLastD_map (f := Subtype.val)
          (l := ux :: q) (a := ux))
    have hlast_delete : (x :: y :: t :: p).getLastD x = L := by
      dsimp [L]
      cases p with
      | nil =>
          simp [List.getLastD]
      | cons w ws =>
          simp [List.getLastD]
    exact h2.symm.trans (h1.trans hlast_delete)
  have hlast_mem_tail : L ∈ t :: p := by
    dsimp [L]
    cases p with
    | nil =>
        simp [List.getLastD]
    | cons w ws =>
        right
        change (w :: ws).getLast (by simp) ∈ w :: ws
        exact List.getLast_mem (l := w :: ws) (by simp)
  have hlast_ne : L ≠ z := by
    intro hLz
    exact havoid (by
      simpa [hLz] using hlast_mem_tail)
  have hnode_y_L : G.node y = L := by
    rw [← hendpoint]
    change G.node (G.node.symm L) = L
    simp
  have hnode_y_ne : G.node y ≠ z := by
    intro hbad
    exact hlast_ne (by
      rw [← hnode_y_L, hbad])
  let uy : H.Dart := ⟨y, hyz⟩
  have hnode_ux : H.node ux = uy := by
    apply Subtype.ext
    change ((G.permFace.walkupE z).face
      (⟨x, hxz⟩ : (G.permFace.walkupE z).Dart)).1 = y
    have hface_apply :
        ((G.permFace.walkupE z).face
          (⟨x, hxz⟩ : (G.permFace.walkupE z).Dart)).1 =
            G.node x :=
      G.permFace.walkupE_face_apply_coe_of_ne
        (⟨x, hxz⟩ : (G.permFace.walkupE z).Dart)
        (by
          change G.node x ≠ z
          simpa [hnode_x] using hyz)
    exact hface_apply.trans hnode_x
  have hnode_uy : H.node uy = (ux :: q).getLastD ux := by
    apply Subtype.ext
    change ((G.permFace.walkupE z).face
      (⟨y, hyz⟩ : (G.permFace.walkupE z).Dart)).1 =
        ((ux :: q).getLastD ux).1
    have hface_apply :
        ((G.permFace.walkupE z).face
          (⟨y, hyz⟩ : (G.permFace.walkupE z).Dart)).1 =
            G.node y :=
      G.permFace.walkupE_face_apply_coe_of_ne
        (⟨y, hyz⟩ : (G.permFace.walkupE z).Dart)
        (by
          change G.node y ≠ z
          exact hnode_y_ne)
    exact hface_apply.trans (hnode_y_L.trans hlast_val.symm)
  have hnodeSymm_last :
      H.node.symm ((ux :: q).getLastD ux) = uy := by
    calc
      H.node.symm ((ux :: q).getLastD ux) =
          H.node.symm (H.node uy) := by rw [hnode_uy]
      _ = uy := by simp
  have hy_mem_q : uy ∈ q := by
    have hy_mem_map : Subtype.val uy ∈ q.map Subtype.val := by
      change y ∈ q.map Subtype.val
      rw [hqmap]
      exact List.Mem.head (t :: p)
    exact (List.mem_map_of_injective Subtype.val_injective
      (a := uy) (l := q)).mp hy_mem_map
  refine ⟨q, hqmap, ?_⟩
  apply MoebiusPath.of_cons (G := H) hnodup_lift hqpath
  rw [hnodeSymm_last, hnode_ux]
  exact ListMemBeforeEq.refl_of_mem hy_mem_q

/-- Coq `planar_Jordan`, final nonempty-tail contradiction after `Dnt`. -/
theorem walkupF_jordan_not_after_forced_fourth_node
    {x y z t : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupF z).Jordan)
    (hm : G.MoebiusPath (x :: y :: z :: t :: p))
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (hnode_x : G.node x = y)
    (hnode_t : G.node t = z)
    (hendpoint :
      G.node.symm ((x :: y :: z :: t :: p).getLastD x) = y) :
    False := by
  have hnodup : (x :: y :: z :: t :: p).Nodup :=
    MoebiusPath.nodup (G := G) hm
  have hnodup_yztp : (y :: z :: t :: p).Nodup :=
    List.Nodup.of_cons hnodup
  have hnodup_ztp : (z :: t :: p).Nodup :=
    List.Nodup.of_cons hnodup_yztp
  have hnodup_tp : (t :: p).Nodup :=
    List.Nodup.of_cons hnodup_ztp
  have hxz : x ≠ z := by
    have hx_not_yztp : x ∉ y :: z :: t :: p :=
      List.Nodup.notMem hnodup
    intro hxz
    exact hx_not_yztp (by
      right
      rw [hxz]
      exact List.Mem.head (t :: p))
  have hyz : y ≠ z := by
    have hy_not_ztp : y ∉ z :: t :: p :=
      List.Nodup.notMem hnodup_yztp
    intro hyz
    exact hy_not_ztp (by
      rw [hyz]
      exact List.Mem.head (t :: p))
  have htz : t ≠ z := by
    have hz_not_tp : z ∉ t :: p :=
      List.Nodup.notMem hnodup_ztp
    intro htz
    exact hz_not_tp (by
      rw [htz]
      exact List.Mem.head p)
  have hyt : y ≠ t := by
    have hy_not_ztp : y ∉ z :: t :: p :=
      List.Nodup.notMem hnodup_yztp
    intro hyt
    exact hy_not_ztp (by
      right
      rw [hyt]
      exact List.Mem.head p)
  have havoid : z ∉ t :: p :=
    List.Nodup.notMem hnodup_ztp
  have ht_not_p : t ∉ p :=
    List.Nodup.notMem hnodup_tp
  have hfaceEdge : G.face (G.edge z) = t := by
    rw [← hnode_t]
    exact G.face_edge_node t
  have havoidFaceEdge : G.face (G.edge z) ∉ p := by
    intro hmem
    exact ht_not_p (by
      simpa [hfaceEdge] using hmem)
  have hcp : G.CPath x (y :: z :: t :: p) :=
    MoebiusPath.cPath (G := G) hm
  rcases hcp with ⟨_hxy, hyztp⟩
  rcases hyztp with ⟨_hyz, hztp⟩
  rcases hztp with ⟨_hzt, hpath⟩
  rcases G.walkupF_liftMoebiusPath_of_two_faces_node_delete_third
      hxz hyz htz hyt hface₁ hface₂ hnode_x hnode_t hendpoint
      havoidFaceEdge havoid hpath hnodup with
    ⟨q, _hqmap, hq⟩
  exact hJ ((⟨x, hxz⟩ : (G.walkupF z).Dart) :: q) hq

end Hypermap
end FourColor
end Schematic.Math.GraphTheory
