import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.WalkupE.DeletedThirdFace
import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.WalkupN.PathLifting
import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.WalkupF.DeletedMiddleNode

/-!
Terminal finite-dart analysis and the Jordan theorem for Walkup transforms.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- The three-dart terminal case in Coq `planar_Jordan`: once all darts are
`x,y,z` and both node and face start with the same 3-cycle, Euler genus is
positive. -/
theorem not_eulerPlanar_of_three_dart_moebius_forced
    {x y z : G.Dart}
    (hcover : ∀ u : G.Dart, u = x ∨ u = y ∨ u = z)
    (hnodup : (x :: y :: z :: ([] : List G.Dart)).Nodup)
    (hface₁ : G.face x = y)
    (hface₂ : G.face y = z)
    (hnode_x : G.node x = y)
    (hendpoint :
      G.node.symm ((x :: y :: z :: ([] : List G.Dart)).getLastD x) = y) :
    ¬ G.EulerPlanar := by
  have hx_not_yz : x ∉ y :: z :: ([] : List G.Dart) :=
    List.Nodup.notMem hnodup
  have hnodup_yz : (y :: z :: ([] : List G.Dart)).Nodup :=
    List.Nodup.of_cons hnodup
  have hy_not_z : y ∉ z :: ([] : List G.Dart) :=
    List.Nodup.notMem hnodup_yz
  have hx_ne_y : x ≠ y := by
    intro hxy
    exact hx_not_yz (by
      rw [hxy]
      exact List.Mem.head (z :: ([] : List G.Dart)))
  have hx_ne_z : x ≠ z := by
    intro hxz
    exact hx_not_yz (by
      right
      rw [hxz]
      exact List.Mem.head ([] : List G.Dart))
  have hy_ne_z : y ≠ z := by
    intro hyz
    exact hy_not_z (by
      rw [hyz]
      exact List.Mem.head ([] : List G.Dart))
  have hendpoint' : G.node.symm z = y := by
    simpa [List.getLastD] using hendpoint
  have hnode_y : G.node y = z := by
    calc
      G.node y = G.node (G.node.symm z) := by rw [hendpoint']
      _ = z := by simp
  have hface_z : G.face z = x := by
    rcases hcover (G.face z) with hfzx | hfzy | hfzz
    · exact hfzx
    · exfalso
      have hzx : z = x :=
        G.face.injective (hfzy.trans hface₁.symm)
      exact hx_ne_z hzx.symm
    · exfalso
      have hzy : z = y :=
        G.face.injective (hfzz.trans hface₂.symm)
      exact hy_ne_z hzy.symm
  have hnode_z : G.node z = x := by
    rcases hcover (G.node z) with hnzx | hnzy | hnzz
    · exact hnzx
    · exfalso
      have hzx : z = x :=
        G.node.injective (hnzy.trans hnode_x.symm)
      exact hx_ne_z hzx.symm
    · exfalso
      have hzy : z = y :=
        G.node.injective (hnzz.trans hnode_y.symm)
      exact hy_ne_z hzy.symm
  have hedge_x : G.edge x = y := by
    rw [← hnode_z, ← hface₂]
    exact G.edge_node_face y
  have hedge_y : G.edge y = z := by
    rw [← hnode_x, ← hface_z]
    exact G.edge_node_face z
  have hedge_z : G.edge z = x := by
    rw [← hnode_y, ← hface₁]
    exact G.edge_node_face x
  have hcard : Fintype.card G.Dart = 3 := by
    have huniv : ({x, y, z} : Finset G.Dart) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro u
      rcases hcover u with rfl | rfl | rfl <;> simp
    rw [← Finset.card_univ, ← huniv]
    simp [hx_ne_y, hx_ne_z, hy_ne_z]
  have hedgeReach :
      ∀ a b : G.Dart, PermReachable G.edge a b :=
    permReachable_of_three_cycle_cover G.edge hcover hedge_x hedge_y hedge_z
  have hnodeReach :
      ∀ a b : G.Dart, PermReachable G.node a b :=
    permReachable_of_three_cycle_cover G.node hcover hnode_x hnode_y hnode_z
  have hfaceReach :
      ∀ a b : G.Dart, PermReachable G.face a b :=
    permReachable_of_three_cycle_cover G.face hcover hface₁ hface₂ hface_z
  have hcomp : G.componentCount = 1 := by
    exact G.componentCount_eq_one_of_forall_reachable x
      (fun a b => G.edgePermReachable_reachable (hedgeReach a b))
  have hedgeCount : G.edgeOrbitCount = 1 := by
    unfold edgeOrbitCount
    exact permOrbit_count_eq_one_of_forall_reachable G.edge x hedgeReach
  have hnodeCount : G.nodeOrbitCount = 1 := by
    unfold nodeOrbitCount
    exact permOrbit_count_eq_one_of_forall_reachable G.node x hnodeReach
  have hfaceCount : G.faceOrbitCount = 1 := by
    unfold faceOrbitCount
    exact permOrbit_count_eq_one_of_forall_reachable G.face x hfaceReach
  have hgenus : G.genus = 1 := by
    simp [genus, eulerLeft, eulerRight, hcomp, hcard, hedgeCount,
      hnodeCount, hfaceCount]
  simp [EulerPlanar, hgenus]

theorem not_moebiusPath_singleton
    (x : G.Dart) :
    ¬ G.MoebiusPath [x] := by
  intro hm
  have hmem :=
    ListMemBeforeEq.left_mem (MoebiusPath.memBefore (G := G) hm)
  simp at hmem

theorem not_moebiusPath_pair
    (x y : G.Dart) :
    ¬ G.MoebiusPath [x, y] := by
  intro hm
  have hnodup : (x :: y :: ([] : List G.Dart)).Nodup :=
    MoebiusPath.nodup (G := G) hm
  have hx_ne_y : x ≠ y := by
    have hx_not_y : x ∉ y :: ([] : List G.Dart) :=
      List.Nodup.notMem hnodup
    intro hxy
    exact hx_not_y (by
      rw [hxy]
      exact List.Mem.head ([] : List G.Dart))
  have hmem :=
    MoebiusPath.memBefore (G := G) hm
  have ha : G.node.symm y = y := by
    have hleft := ListMemBeforeEq.left_mem hmem
    simpa [List.getLastD] using hleft
  have hb : G.node x = y := by
    have hright := ListMemBeforeEq.right_mem hmem
    simpa using hright
  have hnode_y : G.node y = y := by
    calc
      G.node y = G.node (G.node.symm y) := by rw [ha]
      _ = y := by simp
  have hxy : x = y :=
    G.node.injective (hb.trans hnode_y.symm)
  exact hx_ne_y hxy

/-- One inductive step of Coq `planar_Jordan`: if all three one-dart Walkup
deletions are already Jordan, then an Euler-planar hypermap is Jordan. -/
theorem jordan_of_walkup_jordan_and_eulerPlanar
    (hE : ∀ z : G.Dart, (G.walkupE z).Jordan)
    (hN : ∀ z : G.Dart, (G.walkupN z).Jordan)
    (hF : ∀ z : G.Dart, (G.walkupF z).Jordan)
    (hplanar : G.EulerPlanar) :
    G.Jordan := by
  intro q hm
  cases q with
  | nil =>
      exact hm
  | cons x p =>
      cases p with
      | nil =>
          exact G.not_moebiusPath_singleton x hm
      | cons y p =>
          cases p with
          | nil =>
              exact G.not_moebiusPath_pair x y hm
          | cons z p =>
              have hface₁ : G.face x = y := by
                exact (G.walkupE_forces_initial_face (hE x) hm).symm
              have hface₂ : G.face y = z :=
                G.walkupF_forces_second_face_of_first_face (hF y) hm hface₁
              have hendpoint :
                  G.node.symm ((x :: y :: z :: p).getLastD x) = y :=
                G.walkupE_forces_inverse_node_endpoint_of_two_faces
                  (hE y) hm hface₁ hface₂
              have hnode_x : G.node x = y :=
                G.walkupN_forces_initial_node_of_two_faces_endpoint
                  (hN y) hm hface₁ hface₂ hendpoint
              cases p with
              | nil =>
                  have hcoverMem :
                      ∀ u : G.Dart,
                        u ∈ x :: y :: z :: ([] : List G.Dart) :=
                    MoebiusPath.mem_of_forall_walkupE_jordan
                      (G := G) hE hm
                  have hcover :
                      ∀ u : G.Dart, u = x ∨ u = y ∨ u = z := by
                    intro u
                    have hu := hcoverMem u
                    simpa using hu
                  exact G.not_eulerPlanar_of_three_dart_moebius_forced
                    hcover (MoebiusPath.nodup (G := G) hm)
                    hface₁ hface₂ hnode_x hendpoint hplanar
              | cons t p =>
                  have hnode_t : G.node t = z :=
                    G.walkupE_forces_fourth_initial_node_of_two_faces_endpoint
                      (hE z) hm hface₁ hface₂ hnode_x hendpoint
                  exact G.walkupF_jordan_not_after_forced_fourth_node
                    (hF z) hm hface₁ hface₂ hnode_x hnode_t hendpoint

end Hypermap
end FourColor
end Schematic.Math.GraphTheory

