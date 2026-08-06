import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace EdgeSubdivision

/-- Edge map for subdividing the edge represented by dart `z`.  The old dart
`z` is paired with one fresh dart and `edge z` with the other; all other old
edge pairs are preserved. -/
def edgeToFun (G : Hypermap) (z : G.Dart) :
    ExtDart G.Dart -> ExtDart G.Dart
  | ExtDart.new => ExtDart.old (G.edge z)
  | ExtDart.newEdge => ExtDart.old z
  | ExtDart.old x =>
      if x = z then ExtDart.newEdge
      else if x = G.edge z then ExtDart.new
      else ExtDart.old (G.edge x)

theorem edgeToFun_involutive
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    Function.Involutive (edgeToFun G z) := by
  intro x
  cases x with
  | new =>
      have hne : G.edge z ≠ z := (hplain z).2
      simp [edgeToFun]
      exact hne
  | newEdge =>
      simp [edgeToFun]
  | old x =>
      by_cases hxz : x = z
      · subst x
        simp [edgeToFun]
      · by_cases hxez : x = G.edge z
        · subst x
          have hne : G.edge z ≠ z := (hplain z).2
          simp [edgeToFun, hne]
        · have hedge_ne_z : G.edge x ≠ z := by
            intro h
            apply hxez
            calc
              x = G.edge (G.edge x) := by rw [(hplain x).1]
              _ = G.edge z := by rw [h]
          have hedge_ne_edge_z : G.edge x ≠ G.edge z := by
            intro h
            exact hxz (G.edge.injective h)
          simp [edgeToFun, hxz, hxez, hedge_ne_z, hedge_ne_edge_z,
            (hplain x).1]

/-- Edge permutation for the pure edge-subdivision hypermap. -/
def edge (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    Equiv.Perm (ExtDart G.Dart) where
  toFun := edgeToFun G z
  invFun := edgeToFun G z
  left_inv := edgeToFun_involutive G z hplain
  right_inv := edgeToFun_involutive G z hplain

@[simp]
theorem edge_new (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    edge G z hplain ExtDart.new = ExtDart.old (G.edge z) :=
  rfl

@[simp]
theorem edge_newEdge (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    edge G z hplain ExtDart.newEdge = ExtDart.old z :=
  rfl

theorem edge_old_eq (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    edge G z hplain (ExtDart.old z) = ExtDart.newEdge := by
  simp [edge, edgeToFun]

theorem edge_old_edge_eq (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    edge G z hplain (ExtDart.old (G.edge z)) = ExtDart.new := by
  have hne : G.edge z ≠ z := (hplain z).2
  simp [edge, edgeToFun, hne]

theorem edge_old_ne (G : Hypermap) (z x : G.Dart) (hplain : G.Plain)
    (hxz : x ≠ z) (hxez : x ≠ G.edge z) :
    edge G z hplain (ExtDart.old x) = ExtDart.old (G.edge x) := by
  simp [edge, edgeToFun, hxz, hxez]

/-- Node permutation for pure edge subdivision: old node rotations are left
unchanged, while the two new darts form the new degree-two node. -/
def node (G : Hypermap) :
    Equiv.Perm (ExtDart G.Dart) where
  toFun
    | ExtDart.new => ExtDart.newEdge
    | ExtDart.newEdge => ExtDart.new
    | ExtDart.old x => ExtDart.old (G.node x)
  invFun
    | ExtDart.new => ExtDart.newEdge
    | ExtDart.newEdge => ExtDart.new
    | ExtDart.old x => ExtDart.old (G.node.symm x)
  left_inv := by
    intro x
    cases x <;> simp
  right_inv := by
    intro x
    cases x <;> simp

@[simp]
theorem node_new (G : Hypermap) :
    node G ExtDart.new = ExtDart.newEdge :=
  rfl

@[simp]
theorem node_newEdge (G : Hypermap) :
    node G ExtDart.newEdge = ExtDart.new :=
  rfl

@[simp]
theorem node_old (G : Hypermap) (x : G.Dart) :
    node G (ExtDart.old x) = ExtDart.old (G.node x) :=
  rfl

/-- Pure hypermap obtained by subdividing the edge represented by `z`.  The
face permutation is defined from `edge⁻¹` and `node⁻¹`, so the hypermap axiom
is automatic. -/
def hypermap (G : Hypermap) (z : G.Dart) (hplain : G.Plain) : Hypermap where
  Dart := ExtDart G.Dart
  edge := edge G z hplain
  node := node G
  face := (edge G z hplain).symm.trans (node G).symm
  node_face_edge := by
    intro x
    simp [Equiv.trans_apply]

@[simp]
theorem hypermap_card (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    Fintype.card (hypermap G z hplain).Dart = Fintype.card G.Dart + 2 :=
  ExtDart.card

/-- Subdividing a plain edge keeps the hypermap plain: the new edge
permutation is still a fixed-point-free involution. -/
theorem hypermap_plain
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).Plain := by
  intro x
  constructor
  · simpa [hypermap, edge] using edgeToFun_involutive G z hplain x
  · cases x with
    | new =>
        change edge G z hplain ExtDart.new ≠ ExtDart.new
        rw [edge_new]
        exact ExtDart.old_ne_new (G.edge z)
    | newEdge =>
        change edge G z hplain ExtDart.newEdge ≠ ExtDart.newEdge
        rw [edge_newEdge]
        exact ExtDart.old_ne_newEdge z
    | old x =>
        by_cases hxz : x = z
        · subst x
          change edge G z hplain (ExtDart.old z) ≠
            ExtDart.old z
          rw [edge_old_eq]
          intro h
          cases h
        · by_cases hxez : x = G.edge z
          · subst x
            change edge G z hplain (ExtDart.old (G.edge z)) ≠
              ExtDart.old (G.edge z)
            rw [edge_old_edge_eq]
            intro h
            cases h
          · have hedge_ne_x : G.edge x ≠ x := (hplain x).2
            change edge G z hplain (ExtDart.old x) ≠
              ExtDart.old x
            rw [edge_old_ne G z x hplain hxz hxez]
            intro h
            exact hedge_ne_x (ExtDart.old_injective h)

theorem edgeOrbitCount
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).edgeOrbitCount = G.edgeOrbitCount + 1 := by
  have hnew := (hypermap_plain G z hplain).card_dart_eq_two_mul_edgeOrbitCount
  have hold := hplain.card_dart_eq_two_mul_edgeOrbitCount
  have hcard := hypermap_card G z hplain
  omega

/-- Node-orbit code for a pure edge subdivision.  The two fresh darts form one
new degree-two node orbit; old node orbits are unchanged. -/
def nodeOrbitCode (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).Dart -> Option G.NodeOrbit
  | ExtDart.new => none
  | ExtDart.newEdge => none
  | ExtDart.old x => some (PermOrbit.of G.node x)

theorem nodeOrbitCode_of_link
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : (hypermap G z hplain).Dart}
    (hxy : PermLink (hypermap G z hplain).node x y) :
    nodeOrbitCode G z hplain x = nodeOrbitCode G z hplain y := by
  cases hxy with
  | forward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          change some (PermOrbit.of G.node x) =
            some (PermOrbit.of G.node (G.node x))
          exact congrArg some (PermOrbit.of_apply G.node x).symm
  | backward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          change some (PermOrbit.of G.node x) =
            some (PermOrbit.of G.node (G.node.symm x))
          exact congrArg some (PermOrbit.of_symm_apply G.node x).symm

theorem nodeOrbitCode_of_reachable
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : (hypermap G z hplain).Dart}
    (hxy : PermReachable (hypermap G z hplain).node x y) :
    nodeOrbitCode G z hplain x = nodeOrbitCode G z hplain y :=
  hxy.apply_eq (nodeOrbitCode G z hplain)
    (fun {_ _} h => nodeOrbitCode_of_link G z hplain h)

theorem old_nodeReachable_of_nodeReachable
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    PermReachable (hypermap G z hplain).node (ExtDart.old x) (ExtDart.old y) :=
  PermReachable.map_of_forward_simulation G.node
    (hypermap G z hplain).node ExtDart.old
    (fun b => by
      simpa [hypermap, node] using
        PermReachable.forward (hypermap G z hplain).node (ExtDart.old b)) hxy

noncomputable def nodeOrbitEquiv
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).NodeOrbit ≃ Option G.NodeOrbit where
  toFun :=
    Quotient.lift
      (nodeOrbitCode G z hplain)
      (by
        intro x y hxy
        exact nodeOrbitCode_of_reachable G z hplain hxy)
  invFun
    | none => PermOrbit.of (hypermap G z hplain).node ExtDart.new
    | some q =>
        Quotient.lift
          (fun x => PermOrbit.of (hypermap G z hplain).node (ExtDart.old x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (hypermap G z hplain).node
              (old_nodeReachable_of_nodeReachable G z hplain hxy))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new => rfl
        | newEdge =>
            apply PermOrbit.of_eq_of
            exact PermReachable.forward (hypermap G z hplain).node ExtDart.new
        | old x => rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q =>
        induction q using Quotient.inductionOn with
        | h x => rfl

theorem nodeOrbitCount
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).nodeOrbitCount = G.nodeOrbitCount + 1 := by
  unfold Hypermap.nodeOrbitCount Hypermap.NodeOrbit
  rw [Nat.card_congr (nodeOrbitEquiv G z hplain)]
  haveI : Finite G.NodeOrbit :=
    Quotient.finite (permOrbitSetoid G.node)
  exact Finite.card_option

theorem plain_edge_symm
    (G : Hypermap) (hplain : G.Plain) (x : G.Dart) :
    G.edge.symm x = G.edge x := by
  apply G.edge.injective
  simp [(hplain x).1]

theorem face_eq_node_symm_edge_symm
    (G : Hypermap) (x : G.Dart) :
    G.face x = G.node.symm (G.edge.symm x) := by
  apply G.node.injective
  simpa using G.node_face_edge (G.edge.symm x)

theorem node_symm_edge_eq_face
    (G : Hypermap) (hplain : G.Plain) (x : G.Dart) :
    G.node.symm (G.edge x) = G.face x := by
  rw [← plain_edge_symm G hplain x]
  exact (face_eq_node_symm_edge_symm G x).symm

@[simp]
theorem face_new
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).face ExtDart.new =
      ExtDart.old (G.face z) := by
  change (node G).symm ((edge G z hplain).symm ExtDart.new) =
    ExtDart.old (G.face z)
  change ExtDart.old (G.node.symm (G.edge z)) =
    ExtDart.old (G.face z)
  simp [node_symm_edge_eq_face G hplain z]

@[simp]
theorem face_newEdge
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).face ExtDart.newEdge =
      ExtDart.old (G.face (G.edge z)) := by
  change (node G).symm ((edge G z hplain).symm ExtDart.newEdge) =
    ExtDart.old (G.face (G.edge z))
  change ExtDart.old (G.node.symm z) =
    ExtDart.old (G.face (G.edge z))
  have hface := node_symm_edge_eq_face G hplain (G.edge z)
  simpa [(hplain z).1] using hface

theorem face_old_eq
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).face (ExtDart.old z) = ExtDart.new := by
  change (node G).symm ((edge G z hplain).symm (ExtDart.old z)) =
    ExtDart.new
  have hedge : (edge G z hplain).symm (ExtDart.old z) =
      ExtDart.newEdge := by
    change edgeToFun G z (ExtDart.old z) = ExtDart.newEdge
    simp [edgeToFun]
  rw [hedge]
  rfl

theorem face_old_edge_eq
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).face (ExtDart.old (G.edge z)) =
      ExtDart.newEdge := by
  change (node G).symm
      ((edge G z hplain).symm (ExtDart.old (G.edge z))) =
    ExtDart.newEdge
  have hedge : (edge G z hplain).symm (ExtDart.old (G.edge z)) =
      ExtDart.new := by
    change edgeToFun G z (ExtDart.old (G.edge z)) = ExtDart.new
    have hne : G.edge z ≠ z := (hplain z).2
    simp [edgeToFun, hne]
  rw [hedge]
  rfl

theorem face_old_ne
    (G : Hypermap) (z x : G.Dart) (hplain : G.Plain)
    (hxz : x ≠ z) (hxez : x ≠ G.edge z) :
    (hypermap G z hplain).face (ExtDart.old x) =
      ExtDart.old (G.face x) := by
  change (node G).symm ((edge G z hplain).symm (ExtDart.old x)) =
    ExtDart.old (G.face x)
  have hedge : (edge G z hplain).symm (ExtDart.old x) =
      ExtDart.old (G.edge x) := by
    change edgeToFun G z (ExtDart.old x) = ExtDart.old (G.edge x)
    simp [edgeToFun, hxz, hxez]
  rw [hedge]
  change ExtDart.old (G.node.symm (G.edge x)) = ExtDart.old (G.face x)
  simp [node_symm_edge_eq_face G hplain x]

@[simp]
theorem face_symm_new
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).face.symm ExtDart.new =
      ExtDart.old z := by
  rfl

@[simp]
theorem face_symm_newEdge
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).face.symm ExtDart.newEdge =
      ExtDart.old (G.edge z) := by
  rfl

theorem face_symm_old_face_z
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).face.symm (ExtDart.old (G.face z)) =
      ExtDart.new := by
  change (edge G z hplain) ((node G) (ExtDart.old (G.face z))) =
    ExtDart.new
  have hnode : G.node (G.face z) = G.edge z := by
    calc
      G.node (G.face z) = G.edge.symm z := by
        simpa using G.node_face_edge (G.edge.symm z)
      _ = G.edge z := plain_edge_symm G hplain z
  simp [node, hnode, edge_old_edge_eq]

theorem face_symm_old_face_edge_z
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).face.symm
        (ExtDart.old (G.face (G.edge z))) =
      ExtDart.newEdge := by
  change (edge G z hplain)
      ((node G) (ExtDart.old (G.face (G.edge z)))) =
    ExtDart.newEdge
  have hnode : G.node (G.face (G.edge z)) = z := by
    calc
      G.node (G.face (G.edge z)) = G.edge.symm (G.edge z) := by
        simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
          G.node_face_edge (G.edge.symm (G.edge z))
      _ = z := by
        rw [plain_edge_symm G hplain (G.edge z), (hplain z).1]
  simp [node, hnode, edge_old_eq]

theorem face_symm_old_ne
    (G : Hypermap) (z x : G.Dart) (hplain : G.Plain)
    (hx_face_z : x ≠ G.face z)
    (hx_face_edge_z : x ≠ G.face (G.edge z)) :
    (hypermap G z hplain).face.symm (ExtDart.old x) =
      ExtDart.old (G.face.symm x) := by
  change (edge G z hplain) ((node G) (ExtDart.old x)) =
    ExtDart.old (G.face.symm x)
  have hnode_ne_z : G.node x ≠ z := by
    intro h
    apply hx_face_edge_z
    calc
      x = G.node.symm z := by
        exact (Equiv.eq_symm_apply G.node).2 h
      _ = G.face (G.edge z) := by
        have hface := node_symm_edge_eq_face G hplain (G.edge z)
        simpa [(hplain z).1] using hface
  have hnode_ne_edge_z : G.node x ≠ G.edge z := by
    intro h
    apply hx_face_z
    calc
      x = G.node.symm (G.edge z) := by
        exact (Equiv.eq_symm_apply G.node).2 h
      _ = G.face z := by
        exact node_symm_edge_eq_face G hplain z
  have hface_symm : G.edge (G.node x) = G.face.symm x :=
    G.edge_node_eq_face_symm x
  simp [node, edge_old_ne G z (G.node x) hplain hnode_ne_z
    hnode_ne_edge_z, hface_symm]

def faceOrbitCode (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).Dart -> G.FaceOrbit
  | ExtDart.new => PermOrbit.of G.face z
  | ExtDart.newEdge => PermOrbit.of G.face (G.edge z)
  | ExtDart.old x => PermOrbit.of G.face x

theorem faceOrbitCode_of_link
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : (hypermap G z hplain).Dart}
    (hxy : PermLink (hypermap G z hplain).face x y) :
    faceOrbitCode G z hplain x = faceOrbitCode G z hplain y := by
  cases hxy with
  | forward =>
      cases x with
      | new =>
          rw [face_new]
          exact (PermOrbit.of_apply G.face z).symm
      | newEdge =>
          rw [face_newEdge]
          exact (PermOrbit.of_apply G.face (G.edge z)).symm
      | old x =>
          by_cases hxz : x = z
          · subst x
            rw [face_old_eq]
            rfl
          · by_cases hxez : x = G.edge z
            · subst x
              rw [face_old_edge_eq]
              rfl
            · rw [face_old_ne G z x hplain hxz hxez]
              exact (PermOrbit.of_apply G.face x).symm
  | backward =>
      cases x with
      | new =>
          rw [face_symm_new]
          rfl
      | newEdge =>
          rw [face_symm_newEdge]
          rfl
      | old x =>
          by_cases hx_face_z : x = G.face z
          · subst x
            rw [face_symm_old_face_z]
            exact PermOrbit.of_apply G.face z
          · by_cases hx_face_edge_z : x = G.face (G.edge z)
            · subst x
              rw [face_symm_old_face_edge_z]
              exact PermOrbit.of_apply G.face (G.edge z)
            · rw [face_symm_old_ne G z x hplain hx_face_z hx_face_edge_z]
              exact (PermOrbit.of_symm_apply G.face x).symm

theorem faceOrbitCode_of_reachable
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : (hypermap G z hplain).Dart}
    (hxy : PermReachable (hypermap G z hplain).face x y) :
    faceOrbitCode G z hplain x = faceOrbitCode G z hplain y :=
  hxy.apply_eq (faceOrbitCode G z hplain)
    (fun {_ _} h => faceOrbitCode_of_link G z hplain h)

theorem old_faceReachable_forward
    (G : Hypermap) (z x : G.Dart) (hplain : G.Plain) :
    PermReachable (hypermap G z hplain).face
      (ExtDart.old x) (ExtDart.old (G.face x)) := by
  by_cases hxz : x = z
  · subst x
    have h1 : PermReachable (hypermap G z hplain).face
        (ExtDart.old z) ExtDart.new := by
      simpa [face_old_eq G z hplain] using
        (PermReachable.forward (hypermap G z hplain).face (ExtDart.old z))
    have h2 : PermReachable (hypermap G z hplain).face
        ExtDart.new (ExtDart.old (G.face z)) := by
      simpa [face_new G z hplain] using
        (PermReachable.forward (hypermap G z hplain).face ExtDart.new)
    exact PermReachable.trans (hypermap G z hplain).face h1 h2
  · by_cases hxez : x = G.edge z
    · subst x
      have h1 : PermReachable (hypermap G z hplain).face
          (ExtDart.old (G.edge z)) ExtDart.newEdge := by
        simpa [face_old_edge_eq G z hplain] using
          (PermReachable.forward (hypermap G z hplain).face
            (ExtDart.old (G.edge z)))
      have h2 : PermReachable (hypermap G z hplain).face
          ExtDart.newEdge (ExtDart.old (G.face (G.edge z))) := by
        simpa [face_newEdge G z hplain] using
          (PermReachable.forward (hypermap G z hplain).face ExtDart.newEdge)
      exact PermReachable.trans (hypermap G z hplain).face h1 h2
    · have h := PermReachable.forward (hypermap G z hplain).face
        (ExtDart.old x)
      simpa [face_old_ne G z x hplain hxz hxez] using h

theorem old_faceReachable_of_face_link
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : PermLink G.face x y) :
    PermReachable (hypermap G z hplain).face
      (ExtDart.old x) (ExtDart.old y) := by
  cases hxy with
  | forward =>
      exact old_faceReachable_forward G z x hplain
  | backward =>
      have hforward :=
        old_faceReachable_forward G z (G.face.symm x) hplain
      exact PermReachable.symm (hypermap G z hplain).face (by
        simpa using hforward)

theorem old_faceReachable_of_faceReachable
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (hypermap G z hplain).face
      (ExtDart.old x) (ExtDart.old y) :=
  PermReachable.map_of_forward_simulation G.face
    (hypermap G z hplain).face ExtDart.old
    (old_faceReachable_forward G z · hplain) hxy

noncomputable def faceOrbitEquiv
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).FaceOrbit ≃ G.FaceOrbit where
  toFun :=
    Quotient.lift
      (faceOrbitCode G z hplain)
      (by
        intro x y hxy
        exact faceOrbitCode_of_reachable G z hplain hxy)
  invFun :=
    Quotient.lift
      (fun x => PermOrbit.of (hypermap G z hplain).face (ExtDart.old x))
      (by
        intro x y hxy
        exact PermOrbit.of_eq_of (hypermap G z hplain).face
          (old_faceReachable_of_faceReachable G z hplain hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply PermOrbit.of_eq_of
            simpa [face_old_eq G z hplain] using
              (PermReachable.forward (hypermap G z hplain).face
                (ExtDart.old z))
        | newEdge =>
            apply PermOrbit.of_eq_of
            simpa [face_old_edge_eq G z hplain] using
              (PermReachable.forward (hypermap G z hplain).face
                (ExtDart.old (G.edge z)))
        | old x => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => rfl

theorem faceOrbitCount
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).faceOrbitCount = G.faceOrbitCount := by
  unfold Hypermap.faceOrbitCount Hypermap.FaceOrbit
  exact Nat.card_congr (faceOrbitEquiv G z hplain)

def componentCode (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).Dart -> G.Component
  | ExtDart.new => G.componentOf z
  | ExtDart.newEdge => G.componentOf z
  | ExtDart.old x => G.componentOf x

theorem componentCode_of_link
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : (hypermap G z hplain).Dart}
    (hxy : (hypermap G z hplain).Link x y) :
    componentCode G z hplain x = componentCode G z hplain y := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    cases x with
    | new =>
        simp [componentCode]
        exact (G.componentOf_edge z).symm
    | newEdge =>
        rfl
    | old x =>
        by_cases hxz : x = z
        · subst x
          change componentCode G z hplain (ExtDart.old z) =
            componentCode G z hplain (edge G z hplain (ExtDart.old z))
          rw [edge_old_eq]
          rfl
        · by_cases hxez : x = G.edge z
          · subst x
            change componentCode G z hplain (ExtDart.old (G.edge z)) =
              componentCode G z hplain
                (edge G z hplain (ExtDart.old (G.edge z)))
            rw [edge_old_edge_eq]
            exact G.componentOf_edge z
          · change componentCode G z hplain (ExtDart.old x) =
              componentCode G z hplain (edge G z hplain (ExtDart.old x))
            rw [edge_old_ne G z x hplain hxz hxez]
            simp [componentCode]
            exact (G.componentOf_edge x).symm
  · subst y
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        simp [componentCode]
        exact (G.componentOf_node x).symm
  · subst y
    cases x with
    | new =>
        rw [face_new]
        simp [componentCode]
        exact (G.componentOf_face z).symm
    | newEdge =>
        rw [face_newEdge]
        simp [componentCode]
        calc
          G.componentOf z = G.componentOf (G.edge z) :=
            (G.componentOf_edge z).symm
          _ = G.componentOf (G.face (G.edge z)) :=
            (G.componentOf_face (G.edge z)).symm
    | old x =>
        by_cases hxz : x = z
        · subst x
          rw [face_old_eq]
          rfl
        · by_cases hxez : x = G.edge z
          · subst x
            rw [face_old_edge_eq]
            exact G.componentOf_edge z
          · rw [face_old_ne G z x hplain hxz hxez]
            simp [componentCode]
            exact (G.componentOf_face x).symm

theorem componentCode_of_reachable
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : (hypermap G z hplain).Dart}
    (hxy : (hypermap G z hplain).Reachable x y) :
    componentCode G z hplain x = componentCode G z hplain y :=
  hxy.apply_eq (componentCode G z hplain)
    (fun {_ _} h => componentCode_of_link G z hplain h)

theorem old_reachable_edge_forward
    (G : Hypermap) (z x : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).Reachable
      (ExtDart.old x) (ExtDart.old (G.edge x)) := by
  by_cases hxz : x = z
  · subst x
    have h1 : (hypermap G z hplain).Reachable
        (ExtDart.old z) ExtDart.newEdge := by
      have h := (hypermap G z hplain).reachable_edge (ExtDart.old z)
      change (hypermap G z hplain).Reachable (ExtDart.old z)
        (edge G z hplain (ExtDart.old z)) at h
      rw [edge_old_eq] at h
      exact h
    have h2 : (hypermap G z hplain).Reachable
        ExtDart.newEdge ExtDart.new := by
      simpa [hypermap, node] using
        (hypermap G z hplain).reachable_node ExtDart.newEdge
    have h3 : (hypermap G z hplain).Reachable
        ExtDart.new (ExtDart.old (G.edge z)) := by
      simpa [hypermap] using
        (hypermap G z hplain).reachable_edge ExtDart.new
    exact h1.trans (h2.trans h3)
  · by_cases hxez : x = G.edge z
    · subst x
      have h1 : (hypermap G z hplain).Reachable
          (ExtDart.old (G.edge z)) ExtDart.new := by
        have h := (hypermap G z hplain).reachable_edge
          (ExtDart.old (G.edge z))
        change (hypermap G z hplain).Reachable (ExtDart.old (G.edge z))
          (edge G z hplain (ExtDart.old (G.edge z))) at h
        rw [edge_old_edge_eq] at h
        exact h
      have h2 : (hypermap G z hplain).Reachable
          ExtDart.new ExtDart.newEdge := by
        simpa [hypermap, node] using
          (hypermap G z hplain).reachable_node ExtDart.new
      have h3 : (hypermap G z hplain).Reachable
          ExtDart.newEdge (ExtDart.old z) := by
        simpa [hypermap] using
          (hypermap G z hplain).reachable_edge ExtDart.newEdge
      simpa [(hplain z).1] using h1.trans (h2.trans h3)
    · have h := (hypermap G z hplain).reachable_edge (ExtDart.old x)
      change (hypermap G z hplain).Reachable (ExtDart.old x)
        (edge G z hplain (ExtDart.old x)) at h
      rw [edge_old_ne G z x hplain hxz hxez] at h
      exact h

theorem old_reachable_of_link
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : G.Link x y) :
    (hypermap G z hplain).Reachable
      (ExtDart.old x) (ExtDart.old y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    exact old_reachable_edge_forward G z x hplain
  · subst y
    simpa [hypermap, node] using
      (hypermap G z hplain).reachable_node (ExtDart.old x)
  · subst y
    exact (hypermap G z hplain).facePermReachable_reachable
      (old_faceReachable_forward G z x hplain)

theorem old_reachable_of_reachable
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (hypermap G z hplain).Reachable
      (ExtDart.old x) (ExtDart.old y) :=
  hxy.lift' ExtDart.old fun _ _ h => old_reachable_of_link G z hplain h

noncomputable def componentEquiv
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).Component ≃ G.Component where
  toFun :=
    Quotient.lift
      (componentCode G z hplain)
      (by
        intro x y hxy
        exact componentCode_of_reachable G z hplain hxy)
  invFun :=
    Quotient.lift
      (fun x => (hypermap G z hplain).componentOf (ExtDart.old x))
      (by
        intro x y hxy
        exact (hypermap G z hplain).componentOf_eq_componentOf
          (old_reachable_of_reachable G z hplain hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply (hypermap G z hplain).componentOf_eq_componentOf
            simpa [face_old_eq G z hplain] using
              (hypermap G z hplain).reachable_face (ExtDart.old z)
        | newEdge =>
            apply (hypermap G z hplain).componentOf_eq_componentOf
            have h := (hypermap G z hplain).reachable_edge (ExtDart.old z)
            change (hypermap G z hplain).Reachable (ExtDart.old z)
              (edge G z hplain (ExtDart.old z)) at h
            rw [edge_old_eq] at h
            exact h
        | old x => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => rfl

theorem componentCount
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).componentCount = G.componentCount := by
  unfold Hypermap.componentCount
  exact Nat.card_congr (componentEquiv G z hplain)

theorem eulerLeft
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).eulerLeft = G.eulerLeft + 2 := by
  unfold Hypermap.eulerLeft
  rw [componentCount G z hplain, hypermap_card]
  omega

theorem eulerRight
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).eulerRight = G.eulerRight + 2 := by
  unfold Hypermap.eulerRight
  rw [edgeOrbitCount G z hplain, nodeOrbitCount G z hplain,
    faceOrbitCount G z hplain]
  omega

theorem genus
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).genus = G.genus := by
  unfold Hypermap.genus
  rw [eulerLeft G z hplain, eulerRight G z hplain,
    Nat.add_sub_add_right]

theorem eulerPlanar_iff
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain) :
    (hypermap G z hplain).EulerPlanar ↔ G.EulerPlanar := by
  simp [Hypermap.EulerPlanar, genus G z hplain]

end EdgeSubdivision

end FourColor

end Schematic.Math.GraphTheory
