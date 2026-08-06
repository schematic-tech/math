import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.PathTransport

/-!
Contour-path lifting and two-face Jordan branches for `WalkupN`.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- Coq `liftN`, one-step form: a contour link avoiding the deleted dart and
the skipped `face z` lifts through `WalkupN`. -/
theorem walkupN_cLink_lift
    {z x y : G.Dart}
    (hx : x ≠ z) (hy : y ≠ z)
    (hy_face : y ≠ G.face z)
    (hxy : G.CLink x y) :
    (G.walkupN z).CLink
      (⟨x, hx⟩ : (G.walkupN z).Dart)
      (⟨y, hy⟩ : (G.walkupN z).Dart) := by
  let P : Hypermap := G.permNode
  let H : Hypermap := P.walkupE z
  change (H.permFace).CLink
    (⟨x, hx⟩ : H.Dart) (⟨y, hy⟩ : H.Dart)
  rcases hxy with hnode | hface
  · left
    have hface_edge : G.face (G.edge x) = y := by
      simpa [hnode] using face_edge_eq_node_symm (G := G) x
    have hedge_ne : G.edge x ≠ z := by
      intro hxez
      exact hy_face (by rw [← hface_edge, hxez])
    have hface_apply :
        (H.face (⟨x, hx⟩ : H.Dart)).1 = G.edge x := by
      simpa [P, H, Hypermap.permNode] using
        (G.permNode.walkupE_face_apply_coe_of_ne
          (⟨x, hx⟩ : (G.permNode.walkupE z).Dart)
          (by simpa [Hypermap.permNode] using hedge_ne))
    have hnode_ne :
        P.node ((H.face (⟨x, hx⟩ : H.Dart)).1) ≠ z := by
      rw [hface_apply]
      change G.face (G.edge x) ≠ z
      rw [hface_edge]
      exact hy
    have hcomp :
        H.node (H.face (⟨x, hx⟩ : H.Dart)) =
          (⟨y, hy⟩ : H.Dart) := by
      apply Subtype.ext
      calc
        (H.node (H.face (⟨x, hx⟩ : H.Dart))).1 =
            P.node ((H.face (⟨x, hx⟩ : H.Dart)).1) := by
          simpa [H] using
            (P.walkupE_node_apply_coe_of_ne
              (H.face (⟨x, hx⟩ : H.Dart)) hnode_ne)
        _ = y := by
          rw [hface_apply]
          change G.face (G.edge x) = y
          exact hface_edge
    have hedgeH : H.edge (⟨y, hy⟩ : H.Dart) =
        (⟨x, hx⟩ : H.Dart) := by
      change (H.face.trans H.node).symm (⟨y, hy⟩ : H.Dart) =
        (⟨x, hx⟩ : H.Dart)
      rw [← hcomp]
      simp
    calc
      (⟨y, hy⟩ : H.Dart) =
          H.edge.symm (H.edge (⟨y, hy⟩ : H.Dart)) := by simp
      _ = H.edge.symm (⟨x, hx⟩ : H.Dart) := by rw [hedgeH]
  · right
    have hnodeH : H.node (⟨x, hx⟩ : H.Dart) =
        (⟨y, hy⟩ : H.Dart) := by
      apply Subtype.ext
      calc
        (H.node (⟨x, hx⟩ : H.Dart)).1 = P.node x := by
          simpa [H] using
            (P.walkupE_node_apply_coe_of_ne
              (⟨x, hx⟩ : H.Dart)
              (by
                intro hfxz
                have hfxz' : G.face x = z := by
                  simpa [P, Hypermap.permNode] using hfxz
                exact hy (by rw [hface, hfxz'])))
        _ = y := by
          change G.face x = y
          exact hface.symm
    exact hnodeH.symm

/-- Coq `liftN`: a contour path avoiding `z`, with no tail hit of `face z`,
lifts through `WalkupN`. -/
theorem walkupN_liftCPath
    {z x : G.Dart} {p : List G.Dart}
    (havoidFace : G.face z ∉ p)
    (havoid : z ∉ x :: p)
    (hp : G.CPath x p) :
    ∃ q : List (G.walkupN z).Dart,
      q.map Subtype.val = p ∧
        (G.walkupN z).CPath
          (⟨x, by
            intro hxz
            exact havoid (by simp [hxz])⟩ : (G.walkupN z).Dart) q := by
  have hx : x ≠ z := by
    intro hxz
    exact havoid (by simp [hxz])
  have havoidTail : z ∉ p := by
    intro hz
    exact havoid (by simp [hz])
  have hgood : ∀ y ∈ p, y ≠ G.face z := by
    intro y hy hyFace
    subst y
    exact havoidFace hy
  simpa [CPath] using
    (liftRelPathThroughDeletedPoint
      (z := z) (x := x) (p := p)
      (R := G.CLink) (S := (G.walkupN z).CLink)
      (fun y => y ≠ G.face z) hx havoidTail hgood
      (fun ha hb hface hlink =>
        G.walkupN_cLink_lift ha hb hface hlink) hp)

/-- Special first-step link for the Coq `Dnx` branch: deleting the middle
dart `y` with `WalkupN` turns two face steps `x --F--> y --F--> z` into a
contour link from the lifted `x` to the lifted `z`. -/
theorem walkupN_cLink_of_face_eq_deleted_of_face_eq_deleted
    {x y z : G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z) :
    (G.walkupN y).CLink
      (⟨x, hx⟩ : (G.walkupN y).Dart)
      (⟨z, hz⟩ : (G.walkupN y).Dart) := by
  let P : Hypermap := G.permNode
  let K : Hypermap := P.walkupE y
  change (K.permFace).CLink
    (⟨x, hx⟩ : K.Dart) (⟨z, hz⟩ : K.Dart)
  right
  apply Subtype.ext
  have hnode_apply :
      (K.node (⟨x, hx⟩ : K.Dart)).1 = G.face y := by
    simpa [P, K, Hypermap.permNode] using
      (G.permNode.walkupE_node_apply_coe_of_eq
        (⟨x, hx⟩ : (G.permNode.walkupE y).Dart)
        (by
          change G.face x = y
          exact hface₁))
  exact (hnode_apply.trans hface₂).symm

/-- Path package for the Coq `Dnx` branch: after two consecutive face steps,
delete the middle dart with `WalkupN`, use the special first link, and lift
the remaining tail generically. -/
theorem walkupN_liftCPath_of_face_eq_deleted_of_face_eq_deleted
    {x y z : G.Dart} {p : List G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (havoidFace : G.face y ∉ p)
    (havoid : y ∉ z :: p)
    (hp : G.CPath z p) :
    ∃ q : List (G.walkupN y).Dart,
      q.map Subtype.val = z :: p ∧
        (G.walkupN y).CPath
          (⟨x, hx⟩ : (G.walkupN y).Dart) q := by
  rcases G.walkupN_liftCPath havoidFace havoid hp with
    ⟨q, hqmap, hqpath⟩
  have hqpath' :
      (G.walkupN y).CPath
        (⟨z, hz⟩ : (G.walkupN y).Dart) q := by
    convert hqpath using 1
  refine ⟨(⟨z, hz⟩ : (G.walkupN y).Dart) :: q, ?_, ?_⟩
  · change z :: q.map Subtype.val = z :: p
    exact congrArg (fun r : List G.Dart => z :: r) hqmap
  · constructor
    · exact G.walkupN_cLink_of_face_eq_deleted_of_face_eq_deleted
        hx hz hface₁ hface₂
    · exact hqpath'

/-- Coq `planar_Jordan`, `Dnx` branch: after `Dt`, the contrary assumption
`G.node x ≠ y` lifts the path to a Moebius path in `WalkupN y`. -/
theorem walkupN_liftMoebiusPath_of_face_eq_deleted_of_face_eq_deleted
    {x y z : G.Dart} {p : List G.Dart}
    (hx : x ≠ y) (hz : z ≠ y)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (havoid : y ∉ z :: p)
    (hpath : G.CPath z p)
    (hnodup : (x :: y :: z :: p).Nodup)
    (hendpoint :
      G.node.symm ((x :: y :: z :: p).getLastD x) = y)
    (hnode_x_ne : G.node x ≠ y)
    (hmem :
      ListMemBeforeEq (y :: z :: p)
        (G.node.symm ((x :: y :: z :: p).getLastD x)) (G.node x)) :
    ∃ q : List (G.walkupN y).Dart,
      q.map Subtype.val = z :: p ∧
        (G.walkupN y).MoebiusPath
          ((⟨x, hx⟩ : (G.walkupN y).Dart) :: q) := by
  let H : Hypermap := G.walkupN y
  let ux : H.Dart := ⟨x, hx⟩
  let uz : H.Dart := ⟨z, hz⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = z :: p ∧ H.MoebiusPath (ux :: q)
  have hnodup_yzp : (y :: z :: p).Nodup :=
    List.Nodup.of_cons hnodup
  have hnodup_zp : (z :: p).Nodup :=
    List.Nodup.of_cons hnodup_yzp
  have hz_not_p : z ∉ p :=
    List.Nodup.notMem hnodup_zp
  have havoidFace : G.face y ∉ p := by
    intro hmemFace
    exact hz_not_p (by
      simpa [hface₂] using hmemFace)
  rcases G.walkupN_liftCPath_of_face_eq_deleted_of_face_eq_deleted
      hx hz hface₁ hface₂ havoidFace havoid hpath with
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
  have hx_ne_z : x ≠ z := by
    intro hxz
    exact hx_not_zp (by
      rw [hxz]
      exact List.Mem.head p)
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
  have ha_eq : a = y := by
    simpa [a, L] using hendpoint
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
  have hnode_y_L : G.node y = L := by
    rw [← ha_eq]
    change G.node (G.node.symm L) = L
    simp
  have hnode_y_ne : G.node y ≠ y := by
    intro hyy
    exact hlast_ne (by
      rw [← hnode_y_L, hyy])
  have hb_ne : b ≠ y := by
    simpa [b] using hnode_x_ne
  let ub : H.Dart := ⟨b, hb_ne⟩
  have hnode_ux : H.node ux = ub := by
    apply Subtype.ext
    change ((G.permNode.walkupE y).edge
      (⟨x, hx⟩ : (G.permNode.walkupE y).Dart)).1 = b
    rw [G.permNode.walkupE_edge_apply_coe]
    change G.permNode.walkupSkipEdgeAux y x = b
    have hfe_x : G.edge (G.node x) ≠ y := by
      intro hbad
      have hxz : x = z := by
        calc
          x = G.face (G.edge (G.node x)) := (G.face_edge_node x).symm
          _ = G.face y := by rw [hbad]
          _ = z := hface₂
      exact hx_ne_z hxz
    unfold walkupSkipEdgeAux
    by_cases hny : G.node y = y
    · rw [if_pos (by simpa [Hypermap.permNode] using hny)]
      rfl
    · rw [if_neg (by simpa [Hypermap.permNode] using hny)]
      rw [if_neg (by simpa [Hypermap.permNode] using hfe_x)]
      rw [if_neg (by simpa [Hypermap.permNode] using hnode_x_ne)]
      rfl
  have hnode_uz : H.node uz = (ux :: q).getLastD ux := by
    apply Subtype.ext
    change ((G.permNode.walkupE y).edge
      (⟨z, hz⟩ : (G.permNode.walkupE y).Dart)).1 =
        ((ux :: q).getLastD ux).1
    rw [G.permNode.walkupE_edge_apply_coe]
    change G.permNode.walkupSkipEdgeAux y z =
      ((ux :: q).getLastD ux).1
    have hfe_z : G.edge (G.node z) = y := by
      rw [← hface₂]
      exact G.edge_node_face y
    unfold walkupSkipEdgeAux
    rw [if_neg (by simpa [Hypermap.permNode] using hnode_y_ne)]
    rw [if_pos (by simpa [Hypermap.permNode] using hfe_z)]
    exact hnode_y_L.trans hlast_val.symm
  have hnodeSymm_last :
      H.node.symm ((ux :: q).getLastD ux) = uz := by
    calc
      H.node.symm ((ux :: q).getLastD ux) =
          H.node.symm (H.node uz) := by rw [hnode_uz]
      _ = uz := by simp
  have hb_mem_full : b ∈ y :: z :: p := by
    have hb_mem :
        G.node x ∈ y :: z :: p :=
      ListMemBeforeEq.right_mem hmem
    simpa [b] using hb_mem
  have hb_mem_tail : b ∈ z :: p := by
    rw [List.mem_cons] at hb_mem_full
    rcases hb_mem_full with hby | hb_tail
    · exact (hb_ne hby).elim
    · exact hb_tail
  have hmem_map : ListMemBeforeEq (q.map Subtype.val) z b := by
    rw [hqmap]
    exact ListMemBeforeEq.cons_self p z b hb_mem_tail
  have hmem_lift : ListMemBeforeEq q uz ub :=
    ListMemBeforeEq.of_map_injective
      (f := Subtype.val) Subtype.val_injective
      (by simpa [uz, ub] using hmem_map)
  refine ⟨q, hqmap, ?_⟩
  apply MoebiusPath.of_cons (G := H) hnodup_lift hqpath
  rw [hnodeSymm_last, hnode_ux]
  exact hmem_lift

/-- Coq `planar_Jordan`, `Dnx`: after the two face steps and the `Dt`
endpoint reduction, Jordan for `WalkupN y` forces `G.node x = y`. -/
theorem walkupN_forces_initial_node_of_two_faces_endpoint
    {x y z : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupN y).Jordan)
    (hm : G.MoebiusPath (x :: y :: z :: p))
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (hendpoint :
      G.node.symm ((x :: y :: z :: p).getLastD x) = y) :
    G.node x = y := by
  by_contra hnode_x_ne
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
  rcases G.walkupN_liftMoebiusPath_of_face_eq_deleted_of_face_eq_deleted
      hx hz hface₁ hface₂ havoid hpath hnodup hendpoint hnode_x_ne hmem with
    ⟨q, _hqmap, hq⟩
  exact hJ ((⟨x, hx⟩ : (G.walkupN y).Dart) :: q) hq

end Hypermap
end FourColor
end Schematic.Math.GraphTheory
