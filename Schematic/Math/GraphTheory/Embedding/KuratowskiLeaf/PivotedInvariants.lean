import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.OrbitCounts

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace LeafExtension

@[simp]
theorem leafHypermap_face_new_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).face ExtDart.new = ExtDart.old p :=
  rfl

@[simp]
theorem leafHypermap_face_newEdge_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).face ExtDart.newEdge = ExtDart.new :=
  rfl

theorem leafHypermap_face_old_some_eq
    (G : Hypermap.{u}) (p x : G.Dart)
    (hx : x = G.edge (G.node p)) :
    (leafHypermap G (some p)).face (ExtDart.old x) =
      ExtDart.newEdge := by
  show (insertedLeafNode G.node (some p)).symm
      (ExtDart.old (G.edge.symm x)) =
    ExtDart.newEdge
  have hsymm : G.edge.symm x = G.node p := by
    simp [hx]
  simp [hsymm]

theorem leafHypermap_face_old_some_ne
    (G : Hypermap.{u}) (p x : G.Dart)
    (hx : x ≠ G.edge (G.node p)) :
    (leafHypermap G (some p)).face (ExtDart.old x) =
      ExtDart.old (G.face x) := by
  show (insertedLeafNode G.node (some p)).symm
      (ExtDart.old (G.edge.symm x)) =
    ExtDart.old (G.face x)
  have hne : G.edge.symm x ≠ G.node p := by
    intro h
    apply hx
    calc
      x = G.edge (G.edge.symm x) := by simp
      _ = G.edge (G.node p) := by rw [h]
  rw [insertedLeafNode_symm_old_some_of_ne G.node p (G.edge.symm x) hne]
  congr 1
  apply G.node.injective
  simpa using (G.node_face_edge (G.edge.symm x)).symm

@[simp]
theorem leafHypermap_face_symm_new_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).face.symm ExtDart.new =
      ExtDart.newEdge :=
  rfl

@[simp]
theorem leafHypermap_face_symm_newEdge_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).face.symm ExtDart.newEdge =
      ExtDart.old (G.edge (G.node p)) :=
  rfl

theorem leafHypermap_face_symm_old_some_eq
    (G : Hypermap.{u}) (p x : G.Dart)
    (hx : x = p) :
    (leafHypermap G (some p)).face.symm (ExtDart.old x) =
      ExtDart.new := by
  subst x
  show ExtDart.Perm.edge G.edge
      (insertedLeafNode G.node (some p) (ExtDart.old p)) =
    ExtDart.new
  simp [insertedLeafNode_old_some]

theorem leafHypermap_face_symm_old_some_ne
    (G : Hypermap.{u}) (p x : G.Dart)
    (hx : x ≠ p) :
    (leafHypermap G (some p)).face.symm (ExtDart.old x) =
      ExtDart.old (G.face.symm x) := by
  show ExtDart.Perm.edge G.edge
      (insertedLeafNode G.node (some p) (ExtDart.old x)) =
    ExtDart.old (G.face.symm x)
  rw [insertedLeafNode_old_some]
  simp only [hx, ↓reduceIte, ExtDart.Perm.edge_old]
  show ExtDart.old (G.edge (G.node x)) = ExtDart.old (G.face.symm x)
  congr 1
  apply G.face.injective
  simp

theorem leafHypermap_face_some_splice_orbit
    (G : Hypermap.{u}) (p : G.Dart) :
    PermOrbit.of G.face (G.edge (G.node p)) =
      PermOrbit.of G.face p := by
  calc
    PermOrbit.of G.face (G.edge (G.node p)) =
        PermOrbit.of G.face (G.face (G.edge (G.node p))) :=
      (PermOrbit.of_apply G.face (G.edge (G.node p))).symm
    _ = PermOrbit.of G.face p := by simp

def leafHypermapFaceSomeOrbitCode
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).Dart -> G.FaceOrbit :=
  ExtDart.code (PermOrbit.of G.face p) (PermOrbit.of G.face p)
    (PermOrbit.of G.face)

theorem leafHypermapFaceSomeOrbitCode_of_link
    (G : Hypermap.{u}) (p : G.Dart)
    {x y : (leafHypermap G (some p)).Dart}
    (hxy : PermLink (leafHypermap G (some p)).face x y) :
    leafHypermapFaceSomeOrbitCode G p x =
      leafHypermapFaceSomeOrbitCode G p y := by
  cases hxy with
  | forward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          by_cases hx : x = G.edge (G.node p)
          · rw [leafHypermap_face_old_some_eq G p x hx]
            simpa [leafHypermapFaceSomeOrbitCode, hx] using
              leafHypermap_face_some_splice_orbit G p
          · rw [leafHypermap_face_old_some_ne G p x hx]
            simp [leafHypermapFaceSomeOrbitCode]
            exact (PermOrbit.of_apply G.face x).symm
  | backward =>
      cases x with
      | new => rfl
      | newEdge =>
          simp [leafHypermapFaceSomeOrbitCode]
          exact (leafHypermap_face_some_splice_orbit G p).symm
      | old x =>
          by_cases hx : x = p
          · rw [leafHypermap_face_symm_old_some_eq G p x hx]
            simp [leafHypermapFaceSomeOrbitCode, hx]
          · rw [leafHypermap_face_symm_old_some_ne G p x hx]
            simp [leafHypermapFaceSomeOrbitCode]
            exact (PermOrbit.of_symm_apply G.face x).symm

theorem leafHypermapFaceSomeOrbitCode_of_reachable
    (G : Hypermap.{u}) (p : G.Dart)
    {x y : (leafHypermap G (some p)).Dart}
    (hxy : PermReachable (leafHypermap G (some p)).face x y) :
    leafHypermapFaceSomeOrbitCode G p x =
      leafHypermapFaceSomeOrbitCode G p y :=
  code_eq_of_reflTransGen (leafHypermapFaceSomeOrbitCode G p)
    (leafHypermapFaceSomeOrbitCode_of_link G p) hxy

theorem leafHypermap_old_faceReachable_forward_some
    (G : Hypermap.{u}) (p x : G.Dart) :
    PermReachable (leafHypermap G (some p)).face
      (ExtDart.old x) (ExtDart.old (G.face x)) := by
  by_cases hx : x = G.edge (G.node p)
  · have h1 :
        PermReachable (leafHypermap G (some p)).face
          (ExtDart.old x) ExtDart.newEdge := by
      have h := PermReachable.forward (leafHypermap G (some p)).face
        (ExtDart.old x)
      rw [leafHypermap_face_old_some_eq G p x hx] at h
      exact h
    have h2 :
        PermReachable (leafHypermap G (some p)).face
          ExtDart.newEdge ExtDart.new :=
      PermReachable.forward (leafHypermap G (some p)).face ExtDart.newEdge
    have h3 :
        PermReachable (leafHypermap G (some p)).face
          ExtDart.new (ExtDart.old p) :=
      PermReachable.forward (leafHypermap G (some p)).face ExtDart.new
    have hface : G.face x = p := by
      rw [hx]
      simp
    simpa [hface] using
      PermReachable.trans (leafHypermap G (some p)).face h1
        (PermReachable.trans (leafHypermap G (some p)).face h2 h3)
  · have h := PermReachable.forward (leafHypermap G (some p)).face
      (ExtDart.old x)
    rw [leafHypermap_face_old_some_ne G p x hx] at h
    exact h

theorem leafHypermap_old_faceReachable_of_face_link_some
    (G : Hypermap.{u}) (p : G.Dart)
    {x y : G.Dart}
    (hxy : PermLink G.face x y) :
    PermReachable (leafHypermap G (some p)).face
      (ExtDart.old x) (ExtDart.old y) := by
  cases hxy with
  | forward =>
      exact leafHypermap_old_faceReachable_forward_some G p x
  | backward =>
      have hforward :=
        leafHypermap_old_faceReachable_forward_some G p (G.face.symm x)
      exact PermReachable.symm (leafHypermap G (some p)).face (by
        simpa using hforward)

theorem leafHypermap_old_faceReachable_of_faceReachable_some
    (G : Hypermap.{u}) (p : G.Dart)
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (leafHypermap G (some p)).face
      (ExtDart.old x) (ExtDart.old y) :=
  hxy.lift' ExtDart.old fun _ _ hlink =>
    leafHypermap_old_faceReachable_of_face_link_some G p hlink

noncomputable def leafHypermapFaceSomeOrbitEquiv
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).FaceOrbit ≃ G.FaceOrbit where
  toFun :=
    Quotient.lift
      (leafHypermapFaceSomeOrbitCode G p)
      (by
        intro x y hxy
        exact leafHypermapFaceSomeOrbitCode_of_reachable G p hxy)
  invFun :=
    Quotient.lift
      (fun x => PermOrbit.of (leafHypermap G (some p)).face (ExtDart.old x))
      (by
        intro x y hxy
        exact PermOrbit.of_eq_of (leafHypermap G (some p)).face
          (leafHypermap_old_faceReachable_of_faceReachable_some G p hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply PermOrbit.of_eq_of
            exact PermReachable.symm (leafHypermap G (some p)).face
              (PermReachable.forward (leafHypermap G (some p)).face
                ExtDart.new)
        | newEdge =>
            apply PermOrbit.of_eq_of
            have hnewEdge_old :
                PermReachable (leafHypermap G (some p)).face
                  ExtDart.newEdge (ExtDart.old p) :=
              PermReachable.trans (leafHypermap G (some p)).face
                (PermReachable.forward (leafHypermap G (some p)).face
                  ExtDart.newEdge)
                (PermReachable.forward (leafHypermap G (some p)).face
                  ExtDart.new)
            exact PermReachable.symm (leafHypermap G (some p)).face
              hnewEdge_old
        | old x => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => rfl

theorem leafHypermap_faceOrbitCount_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).faceOrbitCount = G.faceOrbitCount := by
  unfold Hypermap.faceOrbitCount Hypermap.FaceOrbit
  exact Nat.card_congr (leafHypermapFaceSomeOrbitEquiv G p)

theorem leafHypermap_component_some_splice_component
    (G : Hypermap.{u}) (p : G.Dart) :
    G.componentOf (G.edge (G.node p)) = G.componentOf p := by
  calc
    G.componentOf (G.edge (G.node p)) = G.componentOf (G.node p) :=
      G.componentOf_edge (G.node p)
    _ = G.componentOf p := G.componentOf_node p

def leafHypermapComponentSomeCode
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).Dart -> G.Component :=
  ExtDart.code (G.componentOf p) (G.componentOf p) G.componentOf

theorem leafHypermapComponentSomeCode_of_link
    (G : Hypermap.{u}) (p : G.Dart)
    {x y : (leafHypermap G (some p)).Dart}
    (hxy : (leafHypermap G (some p)).Link x y) :
    leafHypermapComponentSomeCode G p x =
      leafHypermapComponentSomeCode G p y := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        simp [leafHypermapComponentSomeCode]
        exact (G.componentOf_edge x).symm
  · subst y
    cases x with
    | new => rfl
    | newEdge =>
        simp [leafHypermapComponentSomeCode]
        exact (G.componentOf_node p).symm
    | old x =>
        by_cases hx : x = p
        · rw [leafHypermap_node]
          simp [leafHypermapComponentSomeCode, insertedLeafNode_old_some, hx]
        · rw [leafHypermap_node]
          simp [leafHypermapComponentSomeCode, insertedLeafNode_old_some, hx]
          exact (G.componentOf_node x).symm
  · subst y
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        by_cases hx : x = G.edge (G.node p)
        · rw [leafHypermap_face_old_some_eq G p x hx]
          simp [leafHypermapComponentSomeCode, hx]
          exact leafHypermap_component_some_splice_component G p
        · rw [leafHypermap_face_old_some_ne G p x hx]
          simp [leafHypermapComponentSomeCode]
          exact (G.componentOf_face x).symm

theorem leafHypermapComponentSomeCode_of_reachable
    (G : Hypermap.{u}) (p : G.Dart)
    {x y : (leafHypermap G (some p)).Dart}
    (hxy : (leafHypermap G (some p)).Reachable x y) :
    leafHypermapComponentSomeCode G p x =
      leafHypermapComponentSomeCode G p y :=
  code_eq_of_reflTransGen (leafHypermapComponentSomeCode G p)
    (leafHypermapComponentSomeCode_of_link G p) hxy

theorem leafHypermap_old_nodeReachable_forward_some
    (G : Hypermap.{u}) (p x : G.Dart) :
    (leafHypermap G (some p)).Reachable
      (ExtDart.old x) (ExtDart.old (G.node x)) := by
  by_cases hx : x = p
  · subst x
    have h1 :
        (leafHypermap G (some p)).Reachable
          (ExtDart.old p) ExtDart.newEdge := by
      have h := (leafHypermap G (some p)).reachable_node (ExtDart.old p)
      rw [leafHypermap_node, insertedLeafNode_old_some] at h
      simpa using h
    have h2 :
        (leafHypermap G (some p)).Reachable
          ExtDart.newEdge (ExtDart.old (G.node p)) := by
      simpa using (leafHypermap G (some p)).reachable_node ExtDart.newEdge
    exact h1.trans h2
  · have h := (leafHypermap G (some p)).reachable_node (ExtDart.old x)
    rw [leafHypermap_node, insertedLeafNode_old_some] at h
    simpa [hx] using h

theorem leafHypermap_old_reachable_of_link_some
    (G : Hypermap.{u}) (p : G.Dart)
    {x y : G.Dart}
    (hxy : G.Link x y) :
    (leafHypermap G (some p)).Reachable
      (ExtDart.old x) (ExtDart.old y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    simpa using (leafHypermap G (some p)).reachable_edge (ExtDart.old x)
  · subst y
    exact leafHypermap_old_nodeReachable_forward_some G p x
  · subst y
    exact (leafHypermap G (some p)).facePermReachable_reachable
      (leafHypermap_old_faceReachable_forward_some G p x)

theorem leafHypermap_old_reachable_of_reachable_some
    (G : Hypermap.{u}) (p : G.Dart)
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (leafHypermap G (some p)).Reachable
      (ExtDart.old x) (ExtDart.old y) :=
  hxy.lift' ExtDart.old fun _ _ hlink =>
    leafHypermap_old_reachable_of_link_some G p hlink

noncomputable def leafHypermapComponentSomeEquiv
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).Component ≃ G.Component where
  toFun :=
    Quotient.lift
      (leafHypermapComponentSomeCode G p)
      (by
        intro x y hxy
        exact leafHypermapComponentSomeCode_of_reachable G p hxy)
  invFun :=
    Quotient.lift
      (fun x => (leafHypermap G (some p)).componentOf (ExtDart.old x))
      (by
        intro x y hxy
        exact (leafHypermap G (some p)).componentOf_eq_componentOf
          (leafHypermap_old_reachable_of_reachable_some G p hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply (leafHypermap G (some p)).componentOf_eq_componentOf
            exact (leafHypermap G (some p)).reachable_symm
              ((leafHypermap G (some p)).reachable_face ExtDart.new)
        | newEdge =>
            apply (leafHypermap G (some p)).componentOf_eq_componentOf
            have h := (leafHypermap G (some p)).reachable_node (ExtDart.old p)
            rw [leafHypermap_node, insertedLeafNode_old_some] at h
            simpa using h
        | old x => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => rfl

theorem leafHypermap_componentCount_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).componentCount = G.componentCount := by
  unfold Hypermap.componentCount
  exact Nat.card_congr (leafHypermapComponentSomeEquiv G p)


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
