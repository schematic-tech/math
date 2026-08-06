import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.WalkupE.DeletedMiddleFace

/-!
The later `WalkupE` branch obtained by deleting the third face dart.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- Path package for the Coq `Dnt` branch: after `x --F--> y --F--> z`
and contrary `z --F--> t`, delete `z` with `WalkupE`; the first link
`x -> y` lifts generically and the second link skips over the deleted dart. -/
theorem walkupE_liftCPath_of_two_faces_delete_third
    {x y z t : G.Dart} {p : List G.Dart}
    (hxz : x ≠ z) (hyz : y ≠ z) (htz : t ≠ z)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (hface₃ : G.face z = t)
    (havoid : z ∉ t :: p)
    (hp : G.CPath t p) :
    ∃ q : List (G.walkupE z).Dart,
      q.map Subtype.val = y :: t :: p ∧
        (G.walkupE z).CPath
          (⟨x, hxz⟩ : (G.walkupE z).Dart) q := by
  let H : Hypermap := G.walkupE z
  let ux : H.Dart := ⟨x, hxz⟩
  let uy : H.Dart := ⟨y, hyz⟩
  let ut : H.Dart := ⟨t, htz⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = y :: t :: p ∧ H.CPath ux q
  rcases G.walkupE_liftCPath havoid hp with ⟨r, hrmap, hrpath⟩
  have hrpath' : H.CPath ut r := by
    simpa [H, ut] using hrpath
  refine ⟨uy :: ut :: r, ?_, ?_⟩
  · change y :: t :: r.map Subtype.val = y :: t :: p
    exact congrArg (fun s : List G.Dart => y :: t :: s) hrmap
  · constructor
    · exact G.walkupE_cLink_lift hxz hyz (Or.inr hface₁.symm)
    · constructor
      · exact G.walkupE_cLink_of_face_eq_deleted_of_face_eq_deleted
          hyz htz hface₂ hface₃
      · exact hrpath'

/-- Coq `planar_Jordan`, `Dnt` branch: under the previously forced
`face x = y`, `face y = z`, endpoint `y`, and `node x = y`, a contrary face
step `face z = t` lifts to a Moebius path in `WalkupE z`. -/
theorem walkupE_liftMoebiusPath_of_two_faces_delete_third
    {x y z t : G.Dart} {p : List G.Dart}
    (hxz : x ≠ z) (hyz : y ≠ z) (htz : t ≠ z)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (hface₃ : G.face z = t)
    (hnode_x : G.node x = y)
    (hendpoint :
      G.node.symm ((x :: y :: z :: t :: p).getLastD x) = y)
    (havoid : z ∉ t :: p)
    (hpath : G.CPath t p)
    (hnodup : (x :: y :: z :: t :: p).Nodup) :
    ∃ q : List (G.walkupE z).Dart,
      q.map Subtype.val = y :: t :: p ∧
        (G.walkupE z).MoebiusPath
          ((⟨x, hxz⟩ : (G.walkupE z).Dart) :: q) := by
  let H : Hypermap := G.walkupE z
  let ux : H.Dart := ⟨x, hxz⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = y :: t :: p ∧ H.MoebiusPath (ux :: q)
  rcases G.walkupE_liftCPath_of_two_faces_delete_third
      hxz hyz htz hface₁ hface₂ hface₃ havoid hpath with
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
    change ((G.walkupE z).node (⟨x, hxz⟩ : (G.walkupE z).Dart)).1 = y
    rw [G.walkupE_node_apply_coe_of_ne]
    · exact hnode_x
    · simpa [hnode_x] using hyz
  have hnode_uy : H.node uy = (ux :: q).getLastD ux := by
    apply Subtype.ext
    change ((G.walkupE z).node uy).1 = ((ux :: q).getLastD ux).1
    rw [G.walkupE_node_apply_coe_of_ne]
    · exact hnode_y_L.trans hlast_val.symm
    · exact hnode_y_ne
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

/-- Coq `planar_Jordan`, `Dnt`: after the first three reductions, Jordan for
`WalkupE z` rules out the face-step case from `z` to the fourth dart, so the
fourth dart must be a reverse-node predecessor of `z`. -/
theorem walkupE_forces_fourth_initial_node_of_two_faces_endpoint
    {x y z t : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupE z).Jordan)
    (hm : G.MoebiusPath (x :: y :: z :: t :: p))
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (hnode_x : G.node x = y)
    (hendpoint :
      G.node.symm ((x :: y :: z :: t :: p).getLastD x) = y) :
    G.node t = z := by
  have hnodup : (x :: y :: z :: t :: p).Nodup :=
    MoebiusPath.nodup (G := G) hm
  have hnodup_yztp : (y :: z :: t :: p).Nodup :=
    List.Nodup.of_cons hnodup
  have hnodup_ztp : (z :: t :: p).Nodup :=
    List.Nodup.of_cons hnodup_yztp
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
  have havoid : z ∉ t :: p :=
    List.Nodup.notMem hnodup_ztp
  have hcp : G.CPath x (y :: z :: t :: p) :=
    MoebiusPath.cPath (G := G) hm
  rcases hcp with ⟨_hxy, hyztp⟩
  rcases hyztp with ⟨_hyz, hztp⟩
  rcases hztp with ⟨hzt, hpath⟩
  rcases hzt with hnodeSymm | hface_zt
  · simp [hnodeSymm]
  · exfalso
    have hface₃ : G.face z = t := hface_zt.symm
    rcases G.walkupE_liftMoebiusPath_of_two_faces_delete_third
        hxz hyz htz hface₁ hface₂ hface₃ hnode_x hendpoint
        havoid hpath hnodup with
      ⟨q, _hqmap, hq⟩
    exact hJ ((⟨x, hxz⟩ : (G.walkupE z).Dart) :: q) hq

end Hypermap
end FourColor
end Schematic.Math.GraphTheory

