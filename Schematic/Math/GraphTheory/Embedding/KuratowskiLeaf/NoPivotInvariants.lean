import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.OrbitCounts

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace LeafExtension

@[simp]
theorem leafHypermap_face_new_none
    (G : Hypermap.{u}) :
    (leafHypermap G none).face ExtDart.new = ExtDart.newEdge :=
  rfl

@[simp]
theorem leafHypermap_face_newEdge_none
    (G : Hypermap.{u}) :
    (leafHypermap G none).face ExtDart.newEdge = ExtDart.new :=
  rfl

@[simp]
theorem leafHypermap_face_old_none
    (G : Hypermap.{u}) (x : G.Dart) :
    (leafHypermap G none).face (ExtDart.old x) =
      ExtDart.old (G.face x) := by
  show ExtDart.old (G.node.symm (G.edge.symm x)) =
    ExtDart.old (G.face x)
  congr 1
  apply G.node.injective
  simpa using (G.node_face_edge (G.edge.symm x)).symm

@[simp]
theorem leafHypermap_face_symm_old_none
    (G : Hypermap.{u}) (x : G.Dart) :
    (leafHypermap G none).face.symm (ExtDart.old x) =
      ExtDart.old (G.face.symm x) := by
  show ExtDart.old (G.edge (G.node x)) = ExtDart.old (G.face.symm x)
  congr 1
  apply G.face.injective
  simp

def leafHypermapFaceNoneOrbitCode
    (G : Hypermap.{u}) :
    (leafHypermap G none).Dart -> Option G.FaceOrbit :=
  ExtDart.code none none (fun x => some (PermOrbit.of G.face x))

theorem leafHypermapFaceNoneOrbitCode_of_link
    (G : Hypermap.{u})
    {x y : (leafHypermap G none).Dart}
    (hxy : PermLink (leafHypermap G none).face x y) :
    leafHypermapFaceNoneOrbitCode G x =
      leafHypermapFaceNoneOrbitCode G y := by
  cases hxy with
  | forward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          rw [leafHypermap_face_old_none]
          simp [leafHypermapFaceNoneOrbitCode]
          exact (PermOrbit.of_apply G.face x).symm
  | backward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          rw [leafHypermap_face_symm_old_none]
          simp [leafHypermapFaceNoneOrbitCode]
          exact (PermOrbit.of_symm_apply G.face x).symm

theorem leafHypermapFaceNoneOrbitCode_of_reachable
    (G : Hypermap.{u})
    {x y : (leafHypermap G none).Dart}
    (hxy : PermReachable (leafHypermap G none).face x y) :
    leafHypermapFaceNoneOrbitCode G x =
      leafHypermapFaceNoneOrbitCode G y :=
  code_eq_of_reflTransGen (leafHypermapFaceNoneOrbitCode G)
    (leafHypermapFaceNoneOrbitCode_of_link G) hxy

theorem leafHypermap_old_faceReachable_of_face_link_none
    (G : Hypermap.{u})
    {x y : G.Dart}
    (hxy : PermLink G.face x y) :
    PermReachable (leafHypermap G none).face
      (ExtDart.old x) (ExtDart.old y) := by
  cases hxy with
  | forward =>
      have h :=
        PermReachable.forward (leafHypermap G none).face (ExtDart.old x)
      convert h using 1
      exact (leafHypermap_face_old_none G x).symm
  | backward =>
      have h :=
        PermReachable.backward (leafHypermap G none).face (ExtDart.old x)
      convert h using 1
      exact (leafHypermap_face_symm_old_none G x).symm

theorem leafHypermap_old_faceReachable_of_faceReachable_none
    (G : Hypermap.{u})
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (leafHypermap G none).face
      (ExtDart.old x) (ExtDart.old y) :=
  hxy.lift' ExtDart.old fun _ _ hlink =>
    leafHypermap_old_faceReachable_of_face_link_none G hlink

noncomputable def leafHypermapFaceNoneOrbitEquiv
    (G : Hypermap.{u}) :
    (leafHypermap G none).FaceOrbit ≃ Option G.FaceOrbit where
  toFun :=
    Quotient.lift
      (leafHypermapFaceNoneOrbitCode G)
      (by
        intro x y hxy
        exact leafHypermapFaceNoneOrbitCode_of_reachable G hxy)
  invFun
    | none => PermOrbit.of (leafHypermap G none).face ExtDart.new
    | some q =>
        Quotient.lift
          (fun x => PermOrbit.of (leafHypermap G none).face (ExtDart.old x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (leafHypermap G none).face
              (leafHypermap_old_faceReachable_of_faceReachable_none G hxy))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new => rfl
        | newEdge =>
            apply PermOrbit.of_eq_of
            exact PermReachable.forward (leafHypermap G none).face ExtDart.new
        | old x => rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q =>
        induction q using Quotient.inductionOn with
        | h x => rfl

theorem leafHypermap_faceOrbitCount_none
    (G : Hypermap.{u}) :
    (leafHypermap G none).faceOrbitCount = G.faceOrbitCount + 1 := by
  unfold Hypermap.faceOrbitCount Hypermap.FaceOrbit
  rw [Nat.card_congr (leafHypermapFaceNoneOrbitEquiv G)]
  haveI : Finite G.FaceOrbit :=
    Quotient.finite (permOrbitSetoid G.face)
  exact Finite.card_option

def leafHypermapComponentNoneCode
    (G : Hypermap.{u}) :
    (leafHypermap G none).Dart -> Option G.Component :=
  ExtDart.code none none (fun x => some (G.componentOf x))

theorem leafHypermapComponentNoneCode_of_link
    (G : Hypermap.{u})
    {x y : (leafHypermap G none).Dart}
    (hxy : (leafHypermap G none).Link x y) :
    leafHypermapComponentNoneCode G x =
      leafHypermapComponentNoneCode G y := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        simp [leafHypermapComponentNoneCode]
        exact (G.componentOf_edge x).symm
  · subst y
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        simp [leafHypermapComponentNoneCode]
        exact (G.componentOf_node x).symm
  · subst y
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        rw [leafHypermap_face_old_none]
        simp [leafHypermapComponentNoneCode]
        exact (G.componentOf_face x).symm

theorem leafHypermapComponentNoneCode_of_reachable
    (G : Hypermap.{u})
    {x y : (leafHypermap G none).Dart}
    (hxy : (leafHypermap G none).Reachable x y) :
    leafHypermapComponentNoneCode G x =
      leafHypermapComponentNoneCode G y :=
  code_eq_of_reflTransGen (leafHypermapComponentNoneCode G)
    (leafHypermapComponentNoneCode_of_link G) hxy

theorem leafHypermap_old_reachable_of_link_none
    (G : Hypermap.{u})
    {x y : G.Dart}
    (hxy : G.Link x y) :
    (leafHypermap G none).Reachable (ExtDart.old x) (ExtDart.old y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    simpa using (leafHypermap G none).reachable_edge (ExtDart.old x)
  · subst y
    simpa using (leafHypermap G none).reachable_node (ExtDart.old x)
  · subst y
    have h := (leafHypermap G none).reachable_face (ExtDart.old x)
    rw [leafHypermap_face_old_none] at h
    exact h

theorem leafHypermap_old_reachable_of_reachable_none
    (G : Hypermap.{u})
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (leafHypermap G none).Reachable (ExtDart.old x) (ExtDart.old y) :=
  hxy.lift' ExtDart.old fun _ _ hlink =>
    leafHypermap_old_reachable_of_link_none G hlink

noncomputable def leafHypermapComponentNoneEquiv
    (G : Hypermap.{u}) :
    (leafHypermap G none).Component ≃ Option G.Component where
  toFun :=
    Quotient.lift
      (leafHypermapComponentNoneCode G)
      (by
        intro x y hxy
        exact leafHypermapComponentNoneCode_of_reachable G hxy)
  invFun
    | none => (leafHypermap G none).componentOf ExtDart.new
    | some c =>
        Quotient.lift
          (fun x => (leafHypermap G none).componentOf (ExtDart.old x))
          (by
            intro x y hxy
            exact (leafHypermap G none).componentOf_eq_componentOf
              (leafHypermap_old_reachable_of_reachable_none G hxy))
          c
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new => rfl
        | newEdge =>
            apply (leafHypermap G none).componentOf_eq_componentOf
            exact (leafHypermap G none).reachable_edge ExtDart.new
        | old x => rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q =>
        induction q using Quotient.inductionOn with
        | h x => rfl

theorem leafHypermap_componentCount_none
    (G : Hypermap.{u}) :
    (leafHypermap G none).componentCount = G.componentCount + 1 := by
  unfold Hypermap.componentCount
  rw [Nat.card_congr (leafHypermapComponentNoneEquiv G)]
  haveI : Finite G.Component :=
    Quotient.finite G.reachableSetoid
  exact Finite.card_option


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
