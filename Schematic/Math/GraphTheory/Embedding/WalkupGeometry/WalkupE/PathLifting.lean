import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.PathTransport

/-!
Generic contour-path lifting and the first Jordan branches for `WalkupE`.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- Coq `liftE`, one-step form: a contour link avoiding the deleted dart
lifts through `WalkupE`. -/
theorem walkupE_cLink_lift
    {z x y : G.Dart}
    (hx : x ≠ z) (hy : y ≠ z)
    (hxy : G.CLink x y) :
    (G.walkupE z).CLink
      (⟨x, hx⟩ : (G.walkupE z).Dart)
      (⟨y, hy⟩ : (G.walkupE z).Dart) := by
  rcases hxy with hnode | hface
  · left
    have hnode' : G.node y = x := by
      simp [hnode]
    have hskip :
        (G.walkupE z).node (⟨y, hy⟩ : (G.walkupE z).Dart) =
          (⟨x, hx⟩ : (G.walkupE z).Dart) := by
      apply Subtype.ext
      rw [G.walkupE_node_apply_coe_of_ne]
      · exact hnode'
      · simpa [hnode'] using hx
    calc
      (⟨y, hy⟩ : (G.walkupE z).Dart) =
          (G.walkupE z).node.symm
            ((G.walkupE z).node
              (⟨y, hy⟩ : (G.walkupE z).Dart)) := by simp
      _ = (G.walkupE z).node.symm
          (⟨x, hx⟩ : (G.walkupE z).Dart) := by rw [hskip]
  · right
    apply Subtype.ext
    rw [G.walkupE_face_apply_coe_of_ne]
    · exact hface
    · simpa [hface] using hy

/-- Coq `liftE`: a contour path avoiding the deleted dart lifts through
`WalkupE`. -/
theorem walkupE_liftCPath
    {z x : G.Dart} {p : List G.Dart}
    (havoid : z ∉ x :: p)
    (hp : G.CPath x p) :
    ∃ q : List (G.walkupE z).Dart,
      q.map Subtype.val = p ∧
        (G.walkupE z).CPath
          (⟨x, by
            intro hxz
            exact havoid (by simp [hxz])⟩ : (G.walkupE z).Dart) q := by
  have hx : x ≠ z := by
    intro hxz
    exact havoid (by simp [hxz])
  have havoidTail : z ∉ p := by
    intro hz
    exact havoid (by simp [hz])
  simpa [CPath] using
    (liftRelPathThroughDeletedPoint
      (z := z) (x := x) (p := p)
      (R := G.CLink) (S := (G.walkupE z).CLink)
      (fun _ => True) hx havoidTail (by simp)
      (fun ha hb _ hlink => G.walkupE_cLink_lift ha hb hlink) hp)

/-- First Coq `planar_Jordan` use of `liftE`: a Moebius path avoiding the
deleted dart lifts to a Moebius path in `WalkupE`. -/
theorem walkupE_liftMoebiusPath_of_not_mem
    {z x : G.Dart} {p : List G.Dart}
    (havoid : z ∉ x :: p)
    (hm : G.MoebiusPath (x :: p)) :
    ∃ q : List (G.walkupE z).Dart,
      q.map Subtype.val = p ∧
        (G.walkupE z).MoebiusPath
          ((⟨x, by
            intro hxz
            exact havoid (by simp [hxz])⟩ : (G.walkupE z).Dart) :: q) := by
  let H : Hypermap := G.walkupE z
  let u : H.Dart := ⟨x, by
    intro hxz
    exact havoid (by simp [hxz])⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = p ∧ H.MoebiusPath (u :: q)
  rcases G.walkupE_liftCPath havoid (MoebiusPath.cPath (G := G) hm) with
    ⟨q, hqmap, hqpath⟩
  change H.CPath u q at hqpath
  have hmap_all : (u :: q).map Subtype.val = x :: p := by
    change x :: q.map Subtype.val = x :: p
    rw [hqmap]
  have hnodup_map : ((u :: q).map Subtype.val).Nodup := by
    rw [hmap_all]
    exact MoebiusPath.nodup (G := G) hm
  have hnodup : (u :: q).Nodup :=
    (List.nodup_map_iff Subtype.val_injective).mp hnodup_map
  let a : G.Dart := G.node.symm ((x :: p).getLastD x)
  let b : G.Dart := G.node x
  have hmb : ListMemBeforeEq p a b := by
    simpa [a, b] using MoebiusPath.memBefore (G := G) hm
  have ha_mem : a ∈ p := ListMemBeforeEq.left_mem hmb
  have hb_mem : b ∈ p := ListMemBeforeEq.right_mem hmb
  have ha_ne : a ≠ z := by
    intro haz
    exact havoid (by
      right
      simpa [haz] using ha_mem)
  have hb_ne : b ≠ z := by
    intro hbz
    exact havoid (by
      right
      simpa [hbz] using hb_mem)
  let ua : H.Dart := ⟨a, ha_ne⟩
  let ub : H.Dart := ⟨b, hb_ne⟩
  have hnode_u : H.node u = ub := by
    apply Subtype.ext
    change ((G.walkupE z).node u).1 = b
    rw [G.walkupE_node_apply_coe_of_ne]
    change G.node x ≠ z
    exact hb_ne
  have hlast_val :
      ((u :: q).getLastD u).1 = (x :: p).getLastD x := by
    have h1 : ((u :: q).map Subtype.val).getLastD x =
        (x :: p).getLastD x := by
      simpa [u] using
        congrArg (fun l : List G.Dart => l.getLastD x) hmap_all
    have h2 : ((u :: q).map Subtype.val).getLastD x =
        ((u :: q).getLastD u).1 := by
      simpa [u] using
        (List.getLastD_map (f := Subtype.val) (l := u :: q) (a := u))
    exact h2.symm.trans h1
  have hlast_ne : (x :: p).getLastD x ≠ z := by
    intro hlast
    have hmemlast : (x :: p).getLastD x ∈ x :: p := by
      cases p with
      | nil =>
          simp
      | cons y ys =>
          simpa using (List.getLastD_mem_cons (l := y :: ys) (a := x))
    rw [hlast] at hmemlast
    exact havoid hmemlast
  have hnode_a_ne : G.node a ≠ z := by
    intro hnodea
    exact hlast_ne (by
      calc
        (x :: p).getLastD x = G.node a := by simp [a]
        _ = z := hnodea)
  have hnode_ua : H.node ua = (u :: q).getLastD u := by
    apply Subtype.ext
    change ((G.walkupE z).node ua).1 = ((u :: q).getLastD u).1
    rw [G.walkupE_node_apply_coe_of_ne]
    · calc
        G.node a = (x :: p).getLastD x := by simp [a]
        _ = ((u :: q).getLastD u).1 := hlast_val.symm
    · exact hnode_a_ne
  have hnodeSymm_last :
      H.node.symm ((u :: q).getLastD u) = ua := by
    calc
      H.node.symm ((u :: q).getLastD u) =
          H.node.symm (H.node ua) := by rw [hnode_ua]
      _ = ua := by simp
  have hmb_map : ListMemBeforeEq (q.map Subtype.val) a b := by
    rw [hqmap]
    exact hmb
  have hmb_lift : ListMemBeforeEq q ua ub :=
    ListMemBeforeEq.of_map_injective
      (f := Subtype.val) Subtype.val_injective
      (by simpa [ua, ub] using hmb_map)
  refine ⟨q, hqmap, ?_⟩
  apply MoebiusPath.of_cons (G := H) hnodup hqpath
  change ListMemBeforeEq q
    (H.node.symm ((u :: q).getLastD u)) (H.node u)
  rw [hnodeSymm_last, hnode_u]
  exact hmb_lift

theorem walkupE_jordan_not_moebiusPath_of_not_mem
    {z x : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupE z).Jordan)
    (havoid : z ∉ x :: p) :
    ¬ G.MoebiusPath (x :: p) := by
  intro hm
  rcases G.walkupE_liftMoebiusPath_of_not_mem havoid hm with
    ⟨q, _hqmap, hq⟩
  exact hJ ((⟨x, by
    intro hxz
    exact havoid (by simp [hxz])⟩ : (G.walkupE z).Dart) :: q) hq

theorem MoebiusPath.mem_of_forall_walkupE_jordan
    {x : G.Dart} {p : List G.Dart}
    (hJ : ∀ z : G.Dart, (G.walkupE z).Jordan)
    (hm : G.MoebiusPath (x :: p)) :
    ∀ z : G.Dart, z ∈ x :: p := by
  intro z
  by_contra havoid
  exact G.walkupE_jordan_not_moebiusPath_of_not_mem (hJ z) havoid hm

/-- Coq `planar_Jordan`, first-link branch: if the first step of a Moebius
path is a reverse-node step, deleting the initial dart by `WalkupE` lifts the
tail to a smaller Moebius path.  The final argument is the Coq `mem2` tail
condition already moved past the deleted head. -/
theorem walkupE_liftMoebiusPath_tail_of_node
    {x y : G.Dart} {p : List G.Dart}
    (havoid : x ∉ y :: p)
    (hnode : G.node y = x)
    (hpath : G.CPath y p)
    (hnodup : (x :: y :: p).Nodup)
    (hmemTail :
      ListMemBeforeEq p
        (G.node.symm ((x :: y :: p).getLastD x)) (G.node x)) :
    ∃ q : List (G.walkupE x).Dart,
      q.map Subtype.val = p ∧
        (G.walkupE x).MoebiusPath
          ((⟨y, by
            intro hyx
            exact havoid (by simp [hyx])⟩ : (G.walkupE x).Dart) :: q) := by
  let H : Hypermap := G.walkupE x
  let u : H.Dart := ⟨y, by
    intro hyx
    exact havoid (by simp [hyx])⟩
  change ∃ q : List H.Dart,
    q.map Subtype.val = p ∧ H.MoebiusPath (u :: q)
  rcases G.walkupE_liftCPath havoid hpath with ⟨q, hqmap, hqpath⟩
  change H.CPath u q at hqpath
  have hmap_all : (u :: q).map Subtype.val = y :: p := by
    change y :: q.map Subtype.val = y :: p
    rw [hqmap]
  have hnodup_tail : (y :: p).Nodup :=
    List.Nodup.of_cons hnodup
  have hnodup_map : ((u :: q).map Subtype.val).Nodup := by
    rw [hmap_all]
    exact hnodup_tail
  have hnodup_lift : (u :: q).Nodup :=
    (List.nodup_map_iff Subtype.val_injective).mp hnodup_map
  let a : G.Dart := G.node.symm ((x :: y :: p).getLastD x)
  let b : G.Dart := G.node x
  have hmem : ListMemBeforeEq p a b := by
    simpa [a, b] using hmemTail
  have ha_mem : a ∈ p := ListMemBeforeEq.left_mem hmem
  have hb_mem : b ∈ p := ListMemBeforeEq.right_mem hmem
  have ha_ne : a ≠ x := by
    intro hax
    exact havoid (by
      right
      simpa [hax] using ha_mem)
  have hb_ne : b ≠ x := by
    intro hbx
    exact havoid (by
      right
      simpa [hbx] using hb_mem)
  let ua : H.Dart := ⟨a, ha_ne⟩
  let ub : H.Dart := ⟨b, hb_ne⟩
  have hnode_u : H.node u = ub := by
    apply Subtype.ext
    change ((G.walkupE x).node u).1 = b
    have hnode_apply : ((G.walkupE x).node u).1 = G.node x :=
      G.walkupE_node_apply_coe_of_eq u (by
        change G.node y = x
        exact hnode)
    simpa [b] using hnode_apply
  have htail_last :
      (y :: p).getLastD y = (x :: y :: p).getLastD x := by
    cases p with
    | nil =>
        simp [List.getLastD]
    | cons z zs =>
        simp [List.getLastD]
  have hlast_val :
      ((u :: q).getLastD u).1 = (x :: y :: p).getLastD x := by
    have h1 : ((u :: q).map Subtype.val).getLastD y =
        (y :: p).getLastD y := by
      simpa [u] using
        congrArg (fun l : List G.Dart => l.getLastD y) hmap_all
    have h2 : ((u :: q).map Subtype.val).getLastD y =
        ((u :: q).getLastD u).1 := by
      simpa [u] using
        (List.getLastD_map (f := Subtype.val) (l := u :: q) (a := u))
    exact h2.symm.trans (h1.trans htail_last)
  have hlast_mem_tail : (x :: y :: p).getLastD x ∈ y :: p := by
    cases p with
    | nil =>
        simp [List.getLastD]
    | cons z zs =>
        right
        change (z :: zs).getLast (by simp) ∈ z :: zs
        exact List.getLast_mem (l := z :: zs) (by simp)
  have hlast_ne : (x :: y :: p).getLastD x ≠ x := by
    intro hlast
    rw [hlast] at hlast_mem_tail
    exact havoid hlast_mem_tail
  have hnode_a_ne : G.node a ≠ x := by
    intro hnodea
    exact hlast_ne (by
      calc
        (x :: y :: p).getLastD x = G.node a := by simp [a]
        _ = x := hnodea)
  have hnode_ua : H.node ua = (u :: q).getLastD u := by
    apply Subtype.ext
    change ((G.walkupE x).node ua).1 = ((u :: q).getLastD u).1
    rw [G.walkupE_node_apply_coe_of_ne]
    · calc
        G.node a = (x :: y :: p).getLastD x := by simp [a]
        _ = ((u :: q).getLastD u).1 := hlast_val.symm
    · exact hnode_a_ne
  have hnodeSymm_last :
      H.node.symm ((u :: q).getLastD u) = ua := by
    calc
      H.node.symm ((u :: q).getLastD u) =
          H.node.symm (H.node ua) := by rw [hnode_ua]
      _ = ua := by simp
  have hmem_map : ListMemBeforeEq (q.map Subtype.val) a b := by
    rw [hqmap]
    exact hmem
  have hmem_lift : ListMemBeforeEq q ua ub :=
    ListMemBeforeEq.of_map_injective
      (f := Subtype.val) Subtype.val_injective
      (by simpa [ua, ub] using hmem_map)
  refine ⟨q, hqmap, ?_⟩
  apply MoebiusPath.of_cons (G := H) hnodup_lift hqpath
  change ListMemBeforeEq q
    (H.node.symm ((u :: q).getLastD u)) (H.node u)
  rw [hnodeSymm_last, hnode_u]
  exact hmem_lift

theorem walkupE_jordan_not_initial_node_of_memBefore_tail
    {x y : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupE x).Jordan)
    (havoid : x ∉ y :: p)
    (hnode : G.node y = x)
    (hpath : G.CPath y p)
    (hnodup : (x :: y :: p).Nodup)
    (hmemTail :
      ListMemBeforeEq p
        (G.node.symm ((x :: y :: p).getLastD x)) (G.node x)) :
    False := by
  rcases G.walkupE_liftMoebiusPath_tail_of_node
      havoid hnode hpath hnodup hmemTail with
    ⟨q, _hqmap, hq⟩
  exact hJ ((⟨y, by
    intro hyx
    exact havoid (by simp [hyx])⟩ : (G.walkupE x).Dart) :: q) hq

theorem walkupE_forces_initial_face_of_memBefore_tail
    {x y : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupE x).Jordan)
    (hm : G.MoebiusPath (x :: y :: p))
    (hmemTail :
      ListMemBeforeEq p
        (G.node.symm ((x :: y :: p).getLastD x)) (G.node x)) :
    y = G.face x := by
  have hnodup : (x :: y :: p).Nodup :=
    MoebiusPath.nodup (G := G) hm
  have havoid : x ∉ y :: p :=
    List.Nodup.notMem hnodup
  have hcp : G.CPath x (y :: p) :=
    MoebiusPath.cPath (G := G) hm
  rcases hcp with ⟨hxy, hpath⟩
  rcases hxy with hnodeSymm | hface
  · exfalso
    have hnode : G.node y = x := by
      simp [hnodeSymm]
    exact G.walkupE_jordan_not_initial_node_of_memBefore_tail
      hJ havoid hnode hpath hnodup hmemTail
  · exact hface

/-- Coq `planar_Jordan`, first-step wrapper using the full Moebius order:
Jordan for `WalkupE x` forces the first contour step to be a face step. -/
theorem walkupE_forces_initial_face
    {x y : G.Dart} {p : List G.Dart}
    (hJ : (G.walkupE x).Jordan)
    (hm : G.MoebiusPath (x :: y :: p)) :
    y = G.face x := by
  have hnodup : (x :: y :: p).Nodup :=
    MoebiusPath.nodup (G := G) hm
  have havoid : x ∉ y :: p :=
    List.Nodup.notMem hnodup
  have hcp : G.CPath x (y :: p) :=
    MoebiusPath.cPath (G := G) hm
  have hmem :
      ListMemBeforeEq (y :: p)
        (G.node.symm ((x :: y :: p).getLastD x)) (G.node x) :=
    MoebiusPath.memBefore (G := G) hm
  rcases hcp with ⟨hxy, hpath⟩
  rcases hxy with hnodeSymm | hface
  · exfalso
    have hnode : G.node y = x := by
      simp [hnodeSymm]
    let a : G.Dart := G.node.symm ((x :: y :: p).getLastD x)
    have hlast_tail :
        (x :: y :: p).getLastD x ∈ y :: p := by
      cases p with
      | nil =>
          simp [List.getLastD]
      | cons w ws =>
          right
          change (w :: ws).getLastD y ∈ w :: ws
          rw [List.getLastD_cons]
          exact List.getLastD_mem_cons
    have ha_ne_y : a ≠ y := by
      intro hay
      have hlast_eq_x : (x :: y :: p).getLastD x = x := by
        calc
          (x :: y :: p).getLastD x = G.node a := by
            simp [a]
          _ = G.node y := by rw [hay]
          _ = x := hnode
      have hx_tail : x ∈ y :: p := by
        rw [← hlast_eq_x]
        exact hlast_tail
      exact havoid hx_tail
    have hmemTail :
        ListMemBeforeEq p
          (G.node.symm ((x :: y :: p).getLastD x)) (G.node x) := by
      exact ListMemBeforeEq.tail_of_cons_ne hmem ha_ne_y
    exact G.walkupE_jordan_not_initial_node_of_memBefore_tail
      hJ havoid hnode hpath hnodup hmemTail
  · exact hface

end Hypermap
end FourColor
end Schematic.Math.GraphTheory
