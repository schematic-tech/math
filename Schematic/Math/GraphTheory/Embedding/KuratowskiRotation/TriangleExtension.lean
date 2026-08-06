import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.EdgeSubdivision

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace TriangleExtension

/-- Darts for adding a triangle on top of a pointed dart.  The outer
`ExtDart` contributes the `w -> v` and `v -> w` darts; the inner fresh darts
contribute `v -> u` and `u -> v`; `old (old x)` are the original darts. -/
abbrev Dart (α : Type u) :=
  ExtDart (ExtDart α)

def old {α : Type u} (x : α) : Dart α :=
  ExtDart.old (ExtDart.old x)

def edgeToFun (G : Hypermap) :
    Dart G.Dart -> Dart G.Dart
  | ExtDart.new => ExtDart.newEdge
  | ExtDart.newEdge => ExtDart.new
  | ExtDart.old ExtDart.new => ExtDart.old ExtDart.newEdge
  | ExtDart.old ExtDart.newEdge => ExtDart.old ExtDart.new
  | ExtDart.old (ExtDart.old x) => old (G.edge x)

def edgeInvFun (G : Hypermap) :
    Dart G.Dart -> Dart G.Dart
  | ExtDart.new => ExtDart.newEdge
  | ExtDart.newEdge => ExtDart.new
  | ExtDart.old ExtDart.new => ExtDart.old ExtDart.newEdge
  | ExtDart.old ExtDart.newEdge => ExtDart.old ExtDart.new
  | ExtDart.old (ExtDart.old x) => old (G.edge.symm x)

def edge (G : Hypermap) : Equiv.Perm (Dart G.Dart) where
  toFun := edgeToFun G
  invFun := edgeInvFun G
  left_inv := by
    intro x
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        cases x with
        | new => rfl
        | newEdge => rfl
        | old x => simp [edgeToFun, edgeInvFun, old]
  right_inv := by
    intro x
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        cases x with
        | new => rfl
        | newEdge => rfl
        | old x => simp [edgeToFun, edgeInvFun, old]

@[simp]
theorem edge_new (G : Hypermap) :
    edge G ExtDart.new = ExtDart.newEdge :=
  rfl

@[simp]
theorem edge_newEdge (G : Hypermap) :
    edge G ExtDart.newEdge = ExtDart.new :=
  rfl

@[simp]
theorem edge_old_new (G : Hypermap) :
    edge G (ExtDart.old ExtDart.new) = ExtDart.old ExtDart.newEdge :=
  rfl

@[simp]
theorem edge_old_newEdge (G : Hypermap) :
    edge G (ExtDart.old ExtDart.newEdge) = ExtDart.old ExtDart.new :=
  rfl

@[simp]
theorem edge_old_old (G : Hypermap) (x : G.Dart) :
    edge G (old x) = old (G.edge x) :=
  rfl

theorem edge_involutive (G : Hypermap) (hplain : G.Plain) :
    Function.Involutive (edge G) := by
  intro x
  cases x with
  | new => rfl
  | newEdge => rfl
  | old x =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          change old (G.edge (G.edge x)) = old x
          rw [(hplain x).1]

def nodeToFun (G : Hypermap) (z : G.Dart) :
    Dart G.Dart -> Dart G.Dart
  | ExtDart.new => old (G.node z)
  | ExtDart.newEdge => ExtDart.old ExtDart.new
  | ExtDart.old ExtDart.new => ExtDart.newEdge
  | ExtDart.old ExtDart.newEdge => old (G.edge z)
  | ExtDart.old (ExtDart.old x) =>
      if x = z then ExtDart.new
      else if x = G.node.symm (G.edge z) then ExtDart.old ExtDart.newEdge
      else old (G.node x)

def nodeInvFun (G : Hypermap) (z : G.Dart) :
    Dart G.Dart -> Dart G.Dart
  | ExtDart.new => old z
  | ExtDart.newEdge => ExtDart.old ExtDart.new
  | ExtDart.old ExtDart.new => ExtDart.newEdge
  | ExtDart.old ExtDart.newEdge => old (G.node.symm (G.edge z))
  | ExtDart.old (ExtDart.old x) =>
      if x = G.node z then ExtDart.new
      else if x = G.edge z then ExtDart.old ExtDart.newEdge
      else old (G.node.symm x)

def node (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    Equiv.Perm (Dart G.Dart) where
  toFun := nodeToFun G z
  invFun := nodeInvFun G z
  left_inv := by
    have : G.edge z ≠ z := hedge_ne
    intro x
    cases x with
    | new =>
        simp [nodeToFun, nodeInvFun, old]
    | newEdge =>
        rfl
    | old x =>
        cases x with
        | new =>
            rfl
        | newEdge =>
            have hnode_ne' : G.edge z ≠ G.node z := hnode_ne.symm
            simp [nodeToFun, nodeInvFun, old, hnode_ne']
        | old x =>
            by_cases hxz : x = z
            · subst x
              simp [nodeToFun, nodeInvFun, old]
            · by_cases hxez : x = G.node.symm (G.edge z)
              · subst x
                have hpz : G.node.symm (G.edge z) ≠ z := by
                  intro h
                  exact hnode_ne (by
                    calc
                      G.node z = G.node (G.node.symm (G.edge z)) := by rw [h]
                      _ = G.edge z := by simp)
                simp [nodeToFun, nodeInvFun, old, hpz]
              · have hnxz : G.node x ≠ G.node z := by
                  intro h
                  exact hxz (G.node.injective h)
                have hnxez : G.node x ≠ G.edge z := by
                  intro h
                  apply hxez
                  calc
                    x = G.node.symm (G.node x) := by simp
                    _ = G.node.symm (G.edge z) := by rw [h]
                simp [nodeToFun, nodeInvFun, old, hxz, hxez, hnxz, hnxez]
  right_inv := by
    intro x
    cases x with
    | new =>
        simp [nodeToFun, nodeInvFun, old]
    | newEdge =>
        rfl
    | old x =>
        cases x with
        | new =>
            rfl
        | newEdge =>
            have hpz : G.node.symm (G.edge z) ≠ z := by
              intro h
              exact hnode_ne (by
                calc
                  G.node z = G.node (G.node.symm (G.edge z)) := by rw [h]
                  _ = G.edge z := by simp)
            simp [nodeToFun, nodeInvFun, old, hpz]
        | old x =>
            by_cases hxz : x = G.node z
            · subst x
              simp [nodeToFun, nodeInvFun, old]
            · by_cases hxez : x = G.edge z
              · subst x
                have hnode_ne' : G.edge z ≠ G.node z := hnode_ne.symm
                simp [nodeToFun, nodeInvFun, old, hnode_ne']
              · have hsx_z : G.node.symm x ≠ z := by
                  intro h
                  exact hxz (by
                    calc
                      x = G.node (G.node.symm x) := by simp
                      _ = G.node z := by rw [h])
                have hsx_ez : G.node.symm x ≠ G.node.symm (G.edge z) := by
                  intro h
                  exact hxez (by
                    calc
                      x = G.node (G.node.symm x) := by simp
                      _ = G.node (G.node.symm (G.edge z)) := by rw [h]
                      _ = G.edge z := by simp)
                simp [nodeToFun, nodeInvFun, old, hxz, hxez, hsx_z, hsx_ez]

@[simp]
theorem node_new (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    node G z hedge_ne hnode_ne ExtDart.new = old (G.node z) :=
  rfl

@[simp]
theorem node_newEdge (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    node G z hedge_ne hnode_ne ExtDart.newEdge = ExtDart.old ExtDart.new :=
  rfl

@[simp]
theorem node_old_new (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    node G z hedge_ne hnode_ne (ExtDart.old ExtDart.new) = ExtDart.newEdge :=
  rfl

@[simp]
theorem node_old_newEdge (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    node G z hedge_ne hnode_ne (ExtDart.old ExtDart.newEdge) =
      old (G.edge z) :=
  rfl

theorem node_old_old (G : Hypermap) (z x : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    node G z hedge_ne hnode_ne (old x) =
      if x = z then ExtDart.new
      else if x = G.node.symm (G.edge z) then ExtDart.old ExtDart.newEdge
      else old (G.node x) :=
  rfl

/-- Pure hypermap operation adding a degree-two triangle over a pointed dart:
the old edge remains, and two fresh edge orbits form the path through the new
degree-two vertex. -/
def hypermap (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    Hypermap where
  Dart := Dart G.Dart
  edge := edge G
  node := node G z hedge_ne hnode_ne
  face := (edge G).symm.trans (node G z hedge_ne hnode_ne).symm
  node_face_edge := by
    intro x
    simp [Equiv.trans_apply]

@[simp]
theorem hypermap_card (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    Fintype.card (hypermap G z hedge_ne hnode_ne).Dart =
      Fintype.card G.Dart + 4 := by
  change Fintype.card (ExtDart (ExtDart G.Dart)) = Fintype.card G.Dart + 4
  rw [ExtDart.card, ExtDart.card]

theorem hypermap_plain (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).Plain := by
  intro x
  constructor
  · exact edge_involutive G hplain x
  · cases x with
    | new =>
        intro h
        cases h
    | newEdge =>
        intro h
        cases h
    | old x =>
        cases x with
        | new =>
            intro h
            cases h
        | newEdge =>
            intro h
            cases h
        | old x =>
            intro h
            change old (G.edge x) = old x at h
            exact (hplain x).2 (ExtDart.old_injective (ExtDart.old_injective h))

theorem edgeOrbitCount (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).edgeOrbitCount =
      G.edgeOrbitCount + 2 := by
  have hnew :=
    (hypermap_plain G z hedge_ne hnode_ne hplain).card_dart_eq_two_mul_edgeOrbitCount
  have hold := hplain.card_dart_eq_two_mul_edgeOrbitCount
  have hcard := hypermap_card G z hedge_ne hnode_ne
  omega

/-- Node-orbit code for the pure triangle expansion.  The two darts at the
restored degree-two vertex form one new orbit; the `w -> v` dart is inserted
into the old node orbit of `z`, and the `u -> v` dart is inserted into the old
node orbit of `G.edge z`. -/
def nodeOrbitCode (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).Dart -> Option G.NodeOrbit
  | ExtDart.new => some (PermOrbit.of G.node z)
  | ExtDart.newEdge => none
  | ExtDart.old ExtDart.new => none
  | ExtDart.old ExtDart.newEdge => some (PermOrbit.of G.node (G.edge z))
  | ExtDart.old (ExtDart.old x) => some (PermOrbit.of G.node x)

theorem nodeOrbitCode_of_link
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    {x y : (hypermap G z hedge_ne hnode_ne).Dart}
    (hxy : PermLink (hypermap G z hedge_ne hnode_ne).node x y) :
    nodeOrbitCode G z hedge_ne hnode_ne x =
      nodeOrbitCode G z hedge_ne hnode_ne y := by
  cases hxy with
  | forward =>
      cases x with
      | new =>
          change nodeOrbitCode G z hedge_ne hnode_ne ExtDart.new =
            nodeOrbitCode G z hedge_ne hnode_ne
              (node G z hedge_ne hnode_ne ExtDart.new)
          simp [nodeOrbitCode, old, PermOrbit.of_apply]
      | newEdge =>
          rfl
      | old x =>
          cases x with
          | new =>
              rfl
          | newEdge =>
              change nodeOrbitCode G z hedge_ne hnode_ne
                  (ExtDart.old ExtDart.newEdge) =
                nodeOrbitCode G z hedge_ne hnode_ne
                  (node G z hedge_ne hnode_ne
                    (ExtDart.old ExtDart.newEdge))
              simp [nodeOrbitCode, old]
          | old x =>
              by_cases hxz : x = z
              · subst x
                have hstep :
                    (hypermap G z hedge_ne hnode_ne).node
                        (ExtDart.old (ExtDart.old z)) =
                      ExtDart.new := by
                  change nodeToFun G z (old z) = ExtDart.new
                  simp [nodeToFun, old]
                rw [hstep]
                rfl
              · by_cases hxez : x = G.node.symm (G.edge z)
                · subst x
                  have hpz : G.node.symm (G.edge z) ≠ z := by
                    intro h
                    exact hnode_ne (by
                      calc
                        G.node z = G.node (G.node.symm (G.edge z)) := by rw [h]
                        _ = G.edge z := by simp)
                  have hstep :
                      (hypermap G z hedge_ne hnode_ne).node
                          (ExtDart.old
                            (ExtDart.old (G.node.symm (G.edge z)))) =
                        ExtDart.old ExtDart.newEdge := by
                    change nodeToFun G z (old (G.node.symm (G.edge z))) =
                      ExtDart.old ExtDart.newEdge
                    simp [nodeToFun, old, hpz]
                  rw [hstep]
                  change some
                      (PermOrbit.of G.node (G.node.symm (G.edge z))) =
                    some (PermOrbit.of G.node (G.edge z))
                  simpa using congrArg some
                    (PermOrbit.of_apply G.node
                      (G.node.symm (G.edge z))).symm
                · change nodeOrbitCode G z hedge_ne hnode_ne (old x) =
                    nodeOrbitCode G z hedge_ne hnode_ne
                      ((hypermap G z hedge_ne hnode_ne).node (old x))
                  have hstep :
                      (hypermap G z hedge_ne hnode_ne).node (old x) =
                        old (G.node x) := by
                    change nodeToFun G z (old x) = old (G.node x)
                    simp [nodeToFun, old, hxz, hxez]
                  rw [hstep]
                  simp [nodeOrbitCode, old, PermOrbit.of_apply]
  | backward =>
      cases x with
      | new =>
          rfl
      | newEdge =>
          rfl
      | old x =>
          cases x with
          | new =>
              rfl
          | newEdge =>
              have hstep :
                  (hypermap G z hedge_ne hnode_ne).node.symm
                      (ExtDart.old ExtDart.newEdge) =
                    old (G.node.symm (G.edge z)) := by
                rfl
              rw [hstep]
              change some (PermOrbit.of G.node (G.edge z)) =
                some (PermOrbit.of G.node (G.node.symm (G.edge z)))
              simpa using congrArg some
                (PermOrbit.of_apply G.node (G.node.symm (G.edge z)))
          | old x =>
              by_cases hxz : x = G.node z
              · subst x
                change nodeOrbitCode G z hedge_ne hnode_ne
                    (old (G.node z)) =
                  nodeOrbitCode G z hedge_ne hnode_ne
                    (nodeInvFun G z (old (G.node z)))
                simp [nodeOrbitCode, nodeInvFun, old, PermOrbit.of_apply]
              · by_cases hxez : x = G.edge z
                · subst x
                  change nodeOrbitCode G z hedge_ne hnode_ne
                      (old (G.edge z)) =
                    nodeOrbitCode G z hedge_ne hnode_ne
                      (nodeInvFun G z (old (G.edge z)))
                  have hnode_ne' : G.edge z ≠ G.node z := hnode_ne.symm
                  simp [nodeOrbitCode, nodeInvFun, old, hnode_ne']
                · change nodeOrbitCode G z hedge_ne hnode_ne (old x) =
                    nodeOrbitCode G z hedge_ne hnode_ne
                      (nodeInvFun G z (old x))
                  simp [nodeOrbitCode, nodeInvFun, old, hxz, hxez,
                    PermOrbit.of_symm_apply]

theorem nodeOrbitCode_of_reachable
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    {x y : (hypermap G z hedge_ne hnode_ne).Dart}
    (hxy : PermReachable (hypermap G z hedge_ne hnode_ne).node x y) :
    nodeOrbitCode G z hedge_ne hnode_ne x =
      nodeOrbitCode G z hedge_ne hnode_ne y :=
  hxy.apply_eq (nodeOrbitCode G z hedge_ne hnode_ne)
    (fun {_ _} h => nodeOrbitCode_of_link G z hedge_ne hnode_ne h)

theorem old_nodeReachable_forward
    (G : Hypermap) (z x : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    PermReachable (hypermap G z hedge_ne hnode_ne).node
      (old x) (old (G.node x)) := by
  by_cases hxz : x = z
  · subst x
    have h1 :
        PermReachable (hypermap G z hedge_ne hnode_ne).node
          (old z) ExtDart.new := by
      have h :=
        (PermReachable.forward (hypermap G z hedge_ne hnode_ne).node
          (old z))
      change PermReachable (node G z hedge_ne hnode_ne)
        (old z) (nodeToFun G z (old z)) at h
      simpa [nodeToFun, old] using h
    have h2 :
        PermReachable (hypermap G z hedge_ne hnode_ne).node
          ExtDart.new (old (G.node z)) := by
      simpa [hypermap, node, nodeToFun, old] using
        (PermReachable.forward (hypermap G z hedge_ne hnode_ne).node
          ExtDart.new)
    exact PermReachable.trans (hypermap G z hedge_ne hnode_ne).node h1 h2
  · by_cases hxez : x = G.node.symm (G.edge z)
    · subst x
      have hpz : G.node.symm (G.edge z) ≠ z := by
        intro h
        exact hnode_ne (by
          calc
            G.node z = G.node (G.node.symm (G.edge z)) := by rw [h]
            _ = G.edge z := by simp)
      have h1 :
          PermReachable (hypermap G z hedge_ne hnode_ne).node
            (old (G.node.symm (G.edge z))) (ExtDart.old ExtDart.newEdge) := by
        have h :=
          (PermReachable.forward (hypermap G z hedge_ne hnode_ne).node
            (old (G.node.symm (G.edge z))))
        change PermReachable (node G z hedge_ne hnode_ne)
          (old (G.node.symm (G.edge z)))
          (nodeToFun G z (old (G.node.symm (G.edge z)))) at h
        simpa [nodeToFun, old, hpz] using h
      have h2 :
          PermReachable (hypermap G z hedge_ne hnode_ne).node
            (ExtDart.old ExtDart.newEdge) (old (G.edge z)) := by
        simpa [hypermap, node, nodeToFun, old] using
          (PermReachable.forward (hypermap G z hedge_ne hnode_ne).node
            (ExtDart.old ExtDart.newEdge))
      simpa using
        (PermReachable.trans (hypermap G z hedge_ne hnode_ne).node h1 h2)
    · have h :=
        (PermReachable.forward (hypermap G z hedge_ne hnode_ne).node
          (old x))
      change PermReachable (node G z hedge_ne hnode_ne)
        (old x) (nodeToFun G z (old x)) at h
      simpa [nodeToFun, old, hxz, hxez] using h

theorem old_nodeReachable_of_node_link
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    {x y : G.Dart}
    (hxy : PermLink G.node x y) :
    PermReachable (hypermap G z hedge_ne hnode_ne).node
      (old x) (old y) := by
  cases hxy with
  | forward =>
      exact old_nodeReachable_forward G z x hedge_ne hnode_ne
  | backward =>
      have hforward :=
        old_nodeReachable_forward G z (G.node.symm x) hedge_ne hnode_ne
      exact PermReachable.symm (hypermap G z hedge_ne hnode_ne).node (by
        simpa using hforward)

theorem old_nodeReachable_of_nodeReachable
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    PermReachable (hypermap G z hedge_ne hnode_ne).node
      (old x) (old y) :=
  PermReachable.map_of_forward_simulation G.node
    (hypermap G z hedge_ne hnode_ne).node old
    (old_nodeReachable_forward G z · hedge_ne hnode_ne) hxy

noncomputable def nodeOrbitEquiv
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).NodeOrbit ≃ Option G.NodeOrbit where
  toFun :=
    Quotient.lift
      (nodeOrbitCode G z hedge_ne hnode_ne)
      (by
        intro x y hxy
        exact nodeOrbitCode_of_reachable G z hedge_ne hnode_ne hxy)
  invFun
    | none =>
        PermOrbit.of (hypermap G z hedge_ne hnode_ne).node ExtDart.newEdge
    | some q =>
        Quotient.lift
          (fun x => PermOrbit.of (hypermap G z hedge_ne hnode_ne).node (old x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (hypermap G z hedge_ne hnode_ne).node
              (old_nodeReachable_of_nodeReachable G z hedge_ne hnode_ne hxy))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply PermOrbit.of_eq_of
            have h :=
              (PermReachable.forward (hypermap G z hedge_ne hnode_ne).node
                (old z))
            change PermReachable (node G z hedge_ne hnode_ne)
              (old z) (nodeToFun G z (old z)) at h
            simpa [nodeToFun, old] using h
        | newEdge =>
            rfl
        | old x =>
            cases x with
            | new =>
                apply PermOrbit.of_eq_of
                exact PermReachable.forward
                  (hypermap G z hedge_ne hnode_ne).node ExtDart.newEdge
            | newEdge =>
                apply PermOrbit.of_eq_of
                have h :=
                  (PermReachable.backward
                    (hypermap G z hedge_ne hnode_ne).node (old (G.edge z)))
                change PermReachable (node G z hedge_ne hnode_ne)
                  (old (G.edge z))
                  (nodeInvFun G z (old (G.edge z))) at h
                have hnode_ne' : G.edge z ≠ G.node z := hnode_ne.symm
                simpa [nodeInvFun, old, hnode_ne'] using h
            | old x =>
                rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q =>
        induction q using Quotient.inductionOn with
        | h x => rfl

theorem nodeOrbitCount (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).nodeOrbitCount =
      G.nodeOrbitCount + 1 := by
  unfold Hypermap.nodeOrbitCount Hypermap.NodeOrbit
  rw [Nat.card_congr (nodeOrbitEquiv G z hedge_ne hnode_ne)]
  haveI : Finite G.NodeOrbit :=
    Quotient.finite (permOrbitSetoid G.node)
  exact Finite.card_option

theorem face_z_ne_self (G : Hypermap) (z : G.Dart)
    (hplain : G.Plain)
    (hnode_ne : G.node z ≠ G.edge z) :
    G.face z ≠ z := by
  intro hz
  rw [← EdgeSubdivision.node_symm_edge_eq_face G hplain z] at hz
  have h := congrArg G.node hz
  simp at h
  exact hnode_ne h.symm

@[simp]
theorem face_new (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).face ExtDart.new =
      ExtDart.old ExtDart.new :=
  rfl

@[simp]
theorem face_newEdge (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).face ExtDart.newEdge =
      old z :=
  rfl

@[simp]
theorem face_old_newEdge (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).face
        (ExtDart.old ExtDart.newEdge) =
      ExtDart.newEdge :=
  rfl

theorem face_old_new (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).face
        (ExtDart.old ExtDart.new) =
      old (G.face z) := by
  change old (G.node.symm (G.edge z)) = old (G.face z)
  rw [EdgeSubdivision.node_symm_edge_eq_face G hplain z]

theorem face_old_z (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).face (old z) =
      ExtDart.old ExtDart.newEdge := by
  change nodeInvFun G z (old (G.edge.symm z)) =
    ExtDart.old ExtDart.newEdge
  rw [Hypermap.Plain.edge_symm_eq (G := G) hplain z]
  have hnode_ne' : G.edge z ≠ G.node z := hnode_ne.symm
  simp [nodeInvFun, old, hnode_ne']

theorem face_old_face_symm_z (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).face (old (G.face.symm z)) =
      ExtDart.new := by
  change nodeInvFun G z (old (G.edge.symm (G.face.symm z))) =
    ExtDart.new
  rw [Hypermap.Plain.edge_symm_eq (G := G) hplain (G.face.symm z)]
  have hedge_face :
      G.edge (G.face.symm z) = G.node z := by
    calc
      G.edge (G.face.symm z) =
          G.edge (G.edge (G.node z)) := by rw [G.edge_node_eq_face_symm z]
      _ = G.node z := (hplain (G.node z)).1
  simp [nodeInvFun, old, hedge_face]

theorem face_old_ne (G : Hypermap) (z x : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    (hxz : x ≠ z)
    (hx_face_symm : x ≠ G.face.symm z) :
    (hypermap G z hedge_ne hnode_ne).face (old x) =
      old (G.face x) := by
  change nodeInvFun G z (old (G.edge.symm x)) = old (G.face x)
  rw [Hypermap.Plain.edge_symm_eq (G := G) hplain x]
  have hedge_ne_node : G.edge x ≠ G.node z := by
    intro h
    apply hx_face_symm
    calc
      x = G.edge (G.edge x) := by rw [(hplain x).1]
      _ = G.edge (G.node z) := by rw [h]
      _ = G.face.symm z := G.edge_node_eq_face_symm z
  have hedge_ne_edge : G.edge x ≠ G.edge z := by
    intro h
    exact hxz (G.edge.injective h)
  have hface : G.node.symm (G.edge x) = G.face x :=
    EdgeSubdivision.node_symm_edge_eq_face G hplain x
  simp [nodeInvFun, old, hedge_ne_node, hedge_ne_edge, hface]

def faceOrbitCode (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).Dart -> Option G.FaceOrbit
  | ExtDart.new => some (PermOrbit.of G.face z)
  | ExtDart.newEdge => none
  | ExtDart.old ExtDart.new => some (PermOrbit.of G.face z)
  | ExtDart.old ExtDart.newEdge => none
  | ExtDart.old (ExtDart.old x) =>
      if x = z then none else some (PermOrbit.of G.face x)

theorem faceOrbitCode_forward
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    (x : (hypermap G z hedge_ne hnode_ne).Dart) :
    faceOrbitCode G z hedge_ne hnode_ne x =
      faceOrbitCode G z hedge_ne hnode_ne
        ((hypermap G z hedge_ne hnode_ne).face x) := by
  cases x with
  | new =>
      rw [face_new]
      rfl
  | newEdge =>
      rw [face_newEdge]
      simp [faceOrbitCode, old]
  | old x =>
      cases x with
      | new =>
          rw [face_old_new G z hedge_ne hnode_ne hplain]
          have hz : G.face z ≠ z := face_z_ne_self G z hplain hnode_ne
          simp [faceOrbitCode, old, hz]
          exact (PermOrbit.of_apply G.face z).symm
      | newEdge =>
          rw [face_old_newEdge]
          rfl
      | old x =>
          by_cases hxz : x = z
          · subst x
            change faceOrbitCode G z hedge_ne hnode_ne (old z) =
              faceOrbitCode G z hedge_ne hnode_ne
                ((hypermap G z hedge_ne hnode_ne).face (old z))
            rw [face_old_z G z hedge_ne hnode_ne hplain]
            simp [faceOrbitCode, old]
          · by_cases hx_face_symm : x = G.face.symm z
            · subst x
              change
                faceOrbitCode G z hedge_ne hnode_ne (old (G.face.symm z)) =
                  faceOrbitCode G z hedge_ne hnode_ne
                    ((hypermap G z hedge_ne hnode_ne).face
                      (old (G.face.symm z)))
              rw [face_old_face_symm_z G z hedge_ne hnode_ne hplain]
              simp [faceOrbitCode, old, hxz]
              exact PermOrbit.of_symm_apply G.face z
            · change faceOrbitCode G z hedge_ne hnode_ne (old x) =
                faceOrbitCode G z hedge_ne hnode_ne
                  ((hypermap G z hedge_ne hnode_ne).face (old x))
              rw [face_old_ne G z x hedge_ne hnode_ne hplain hxz hx_face_symm]
              have hface_ne_z : G.face x ≠ z := by
                intro h
                apply hx_face_symm
                exact (Equiv.eq_symm_apply G.face).2 h
              simp [faceOrbitCode, old, hxz, hface_ne_z]
              exact (PermOrbit.of_apply G.face x).symm

theorem faceOrbitCode_of_link
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    {x y : (hypermap G z hedge_ne hnode_ne).Dart}
    (hxy : PermLink (hypermap G z hedge_ne hnode_ne).face x y) :
    faceOrbitCode G z hedge_ne hnode_ne x =
      faceOrbitCode G z hedge_ne hnode_ne y := by
  cases hxy with
  | forward =>
      exact faceOrbitCode_forward G z hedge_ne hnode_ne hplain x
  | backward =>
      have h :=
        faceOrbitCode_forward G z hedge_ne hnode_ne hplain
          ((hypermap G z hedge_ne hnode_ne).face.symm x)
      simpa using h.symm

theorem faceOrbitCode_of_reachable
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    {x y : (hypermap G z hedge_ne hnode_ne).Dart}
    (hxy : PermReachable (hypermap G z hedge_ne hnode_ne).face x y) :
    faceOrbitCode G z hedge_ne hnode_ne x =
      faceOrbitCode G z hedge_ne hnode_ne y :=
  hxy.apply_eq (faceOrbitCode G z hedge_ne hnode_ne)
    (fun {_ _} h => faceOrbitCode_of_link G z hedge_ne hnode_ne hplain h)

def faceOrbitInvDart
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (x : G.Dart) :
    (hypermap G z hedge_ne hnode_ne).Dart :=
  if x = z then old (G.face z) else old x

theorem faceReachable_new_old_face_z
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    PermReachable (hypermap G z hedge_ne hnode_ne).face
      ExtDart.new (old (G.face z)) := by
  have h1 :
      PermReachable (hypermap G z hedge_ne hnode_ne).face
        ExtDart.new (ExtDart.old ExtDart.new) := by
    simpa [face_new G z hedge_ne hnode_ne] using
      (PermReachable.forward (hypermap G z hedge_ne hnode_ne).face
        ExtDart.new)
  have h2 :
      PermReachable (hypermap G z hedge_ne hnode_ne).face
        (ExtDart.old ExtDart.new) (old (G.face z)) := by
    simpa [face_old_new G z hedge_ne hnode_ne hplain] using
      (PermReachable.forward (hypermap G z hedge_ne hnode_ne).face
        (ExtDart.old ExtDart.new))
  exact PermReachable.trans (hypermap G z hedge_ne hnode_ne).face h1 h2

theorem faceReachable_old_z_old_newEdge
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    PermReachable (hypermap G z hedge_ne hnode_ne).face
      (old z) (ExtDart.old ExtDart.newEdge) := by
  simpa [face_old_z G z hedge_ne hnode_ne hplain] using
    (PermReachable.forward (hypermap G z hedge_ne hnode_ne).face (old z))

theorem faceReachable_old_z_newEdge
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    PermReachable (hypermap G z hedge_ne hnode_ne).face
      (old z) ExtDart.newEdge := by
  have h1 := faceReachable_old_z_old_newEdge G z hedge_ne hnode_ne hplain
  have h2 :
      PermReachable (hypermap G z hedge_ne hnode_ne).face
        (ExtDart.old ExtDart.newEdge) ExtDart.newEdge := by
    simpa [face_old_newEdge G z hedge_ne hnode_ne] using
      (PermReachable.forward (hypermap G z hedge_ne hnode_ne).face
        (ExtDart.old ExtDart.newEdge))
  exact PermReachable.trans (hypermap G z hedge_ne hnode_ne).face h1 h2

theorem faceReachable_old_face_symm_z_old_face_z
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    PermReachable (hypermap G z hedge_ne hnode_ne).face
      (old (G.face.symm z)) (old (G.face z)) := by
  have h0 :
      PermReachable (hypermap G z hedge_ne hnode_ne).face
        (old (G.face.symm z)) ExtDart.new := by
    simpa [face_old_face_symm_z G z hedge_ne hnode_ne hplain] using
      (PermReachable.forward (hypermap G z hedge_ne hnode_ne).face
        (old (G.face.symm z)))
  exact PermReachable.trans (hypermap G z hedge_ne hnode_ne).face h0
    (faceReachable_new_old_face_z G z hedge_ne hnode_ne hplain)

theorem faceOrbitInvDart_reachable_forward
    (G : Hypermap) (z x : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    PermReachable (hypermap G z hedge_ne hnode_ne).face
      (faceOrbitInvDart G z hedge_ne hnode_ne x)
      (faceOrbitInvDart G z hedge_ne hnode_ne (G.face x)) := by
  by_cases hxz : x = z
  · subst x
    have hz : G.face z ≠ z := face_z_ne_self G z hplain hnode_ne
    simpa [faceOrbitInvDart, hz] using
      (PermReachable.refl (hypermap G z hedge_ne hnode_ne).face
        (old (G.face z)))
  · by_cases hx_face_symm : x = G.face.symm z
    · subst x
      have hfs_ne : G.face.symm z ≠ z := by
        intro h
        exact face_z_ne_self G z hplain hnode_ne
          ((Equiv.symm_apply_eq G.face).mp h).symm
      simp [faceOrbitInvDart, hfs_ne]
      exact faceReachable_old_face_symm_z_old_face_z
        G z hedge_ne hnode_ne hplain
    · have h := PermReachable.forward
        (hypermap G z hedge_ne hnode_ne).face (old x)
      have hface_ne_z : G.face x ≠ z := by
        intro hfx
        exact hx_face_symm ((Equiv.eq_symm_apply G.face).2 hfx)
      simpa [faceOrbitInvDart, hxz, hface_ne_z,
        face_old_ne G z x hedge_ne hnode_ne hplain hxz hx_face_symm]
        using h

theorem faceOrbitInvDart_reachable_of_face_link
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : PermLink G.face x y) :
    PermReachable (hypermap G z hedge_ne hnode_ne).face
      (faceOrbitInvDart G z hedge_ne hnode_ne x)
      (faceOrbitInvDart G z hedge_ne hnode_ne y) := by
  cases hxy with
  | forward =>
      exact faceOrbitInvDart_reachable_forward G z x hedge_ne hnode_ne hplain
  | backward =>
      have hforward :=
        faceOrbitInvDart_reachable_forward G z (G.face.symm x)
          hedge_ne hnode_ne hplain
      exact PermReachable.symm (hypermap G z hedge_ne hnode_ne).face (by
        simpa using hforward)

theorem faceOrbitInvDart_reachable_of_faceReachable
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (hypermap G z hedge_ne hnode_ne).face
      (faceOrbitInvDart G z hedge_ne hnode_ne x)
      (faceOrbitInvDart G z hedge_ne hnode_ne y) :=
  PermReachable.map_of_forward_simulation G.face
    (hypermap G z hedge_ne hnode_ne).face
    (faceOrbitInvDart G z hedge_ne hnode_ne)
    (faceOrbitInvDart_reachable_forward G z · hedge_ne hnode_ne hplain) hxy

noncomputable def faceOrbitEquiv
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).FaceOrbit ≃ Option G.FaceOrbit where
  toFun :=
    Quotient.lift
      (faceOrbitCode G z hedge_ne hnode_ne)
      (by
        intro x y hxy
        exact faceOrbitCode_of_reachable G z hedge_ne hnode_ne hplain hxy)
  invFun
    | none =>
        PermOrbit.of (hypermap G z hedge_ne hnode_ne).face (old z)
    | some q =>
        Quotient.lift
          (fun x => PermOrbit.of (hypermap G z hedge_ne hnode_ne).face
            (faceOrbitInvDart G z hedge_ne hnode_ne x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (hypermap G z hedge_ne hnode_ne).face
              (faceOrbitInvDart_reachable_of_faceReachable G z hedge_ne hnode_ne
                hplain hxy))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply PermOrbit.of_eq_of
            have hz : G.face z ≠ z := face_z_ne_self G z hplain hnode_ne
            simpa [faceOrbitInvDart, hz] using
              (PermReachable.symm (hypermap G z hedge_ne hnode_ne).face
                (faceReachable_new_old_face_z G z hedge_ne hnode_ne hplain))
        | newEdge =>
            apply PermOrbit.of_eq_of
            exact faceReachable_old_z_newEdge G z hedge_ne hnode_ne hplain
        | old x =>
            cases x with
            | new =>
                apply PermOrbit.of_eq_of
                have h2 :
                    PermReachable (hypermap G z hedge_ne hnode_ne).face
                      (ExtDart.old ExtDart.new) (old (G.face z)) := by
                  simpa [face_old_new G z hedge_ne hnode_ne hplain] using
                    (PermReachable.forward
                      (hypermap G z hedge_ne hnode_ne).face
                      (ExtDart.old ExtDart.new))
                have hz : G.face z ≠ z := face_z_ne_self G z hplain hnode_ne
                simpa [faceOrbitInvDart, hz] using
                  (PermReachable.symm
                    (hypermap G z hedge_ne hnode_ne).face h2)
            | newEdge =>
                apply PermOrbit.of_eq_of
                exact faceReachable_old_z_old_newEdge
                  G z hedge_ne hnode_ne hplain
            | old x =>
                by_cases hxz : x = z
                · subst x
                  simp [faceOrbitCode, old, PermOrbit.of]
                · simp [faceOrbitCode, faceOrbitInvDart, old, hxz, PermOrbit.of]
  right_inv := by
    intro q
    cases q with
    | none =>
        change faceOrbitCode G z hedge_ne hnode_ne (old z) = none
        simp [faceOrbitCode, old]
    | some q =>
        induction q using Quotient.inductionOn with
        | h x =>
            change
              faceOrbitCode G z hedge_ne hnode_ne
                  (faceOrbitInvDart G z hedge_ne hnode_ne x) =
                some (PermOrbit.of G.face x)
            by_cases hxz : x = z
            · subst x
              have hz : G.face z ≠ z := face_z_ne_self G z hplain hnode_ne
              simp [faceOrbitInvDart, faceOrbitCode, old, hz]
              exact PermOrbit.of_apply G.face z
            · simp [faceOrbitInvDart, faceOrbitCode, old, hxz]

theorem faceOrbitCount
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).faceOrbitCount =
      G.faceOrbitCount + 1 := by
  unfold Hypermap.faceOrbitCount Hypermap.FaceOrbit
  rw [Nat.card_congr (faceOrbitEquiv G z hedge_ne hnode_ne hplain)]
  haveI : Finite G.FaceOrbit :=
    Quotient.finite (permOrbitSetoid G.face)
  exact Finite.card_option

def componentCode (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).Dart -> G.Component
  | ExtDart.new => G.componentOf z
  | ExtDart.newEdge => G.componentOf z
  | ExtDart.old ExtDart.new => G.componentOf z
  | ExtDart.old ExtDart.newEdge => G.componentOf z
  | ExtDart.old (ExtDart.old x) => G.componentOf x

theorem componentCode_node_old_splice
    (G : Hypermap) (z : G.Dart) :
    G.componentOf (G.node.symm (G.edge z)) = G.componentOf z := by
  calc
    G.componentOf (G.node.symm (G.edge z)) = G.componentOf (G.edge z) :=
      by simpa using (G.componentOf_node (G.node.symm (G.edge z))).symm
    _ = G.componentOf z := G.componentOf_edge z

theorem componentCode_face_symm_splice
    (G : Hypermap) (z : G.Dart) :
    G.componentOf (G.face.symm z) = G.componentOf z := by
  simpa using (G.componentOf_face (G.face.symm z)).symm

theorem componentCode_of_link
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    {x y : (hypermap G z hedge_ne hnode_ne).Dart}
    (hxy : (hypermap G z hedge_ne hnode_ne).Link x y) :
    componentCode G z hedge_ne hnode_ne x =
      componentCode G z hedge_ne hnode_ne y := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        cases x with
        | new => rfl
        | newEdge => rfl
        | old x =>
            simp [componentCode]
            exact (G.componentOf_edge x).symm
  · subst y
    cases x with
    | new =>
        simp [componentCode]
        exact (G.componentOf_node z).symm
    | newEdge => rfl
    | old x =>
        cases x with
        | new => rfl
        | newEdge =>
            simp [componentCode]
            exact (G.componentOf_edge z).symm
        | old x =>
            by_cases hxz : x = z
            · subst x
              change componentCode G z hedge_ne hnode_ne (old z) =
                componentCode G z hedge_ne hnode_ne
                  (node G z hedge_ne hnode_ne (old z))
              rw [node_old_old G z z hedge_ne hnode_ne]
              simp [componentCode, old]
            · by_cases hxez : x = G.node.symm (G.edge z)
              · subst x
                have hpz : G.node.symm (G.edge z) ≠ z := by
                  intro h
                  exact hnode_ne (by
                    calc
                      G.node z = G.node (G.node.symm (G.edge z)) := by rw [h]
                      _ = G.edge z := by simp)
                change componentCode G z hedge_ne hnode_ne
                    (old (G.node.symm (G.edge z))) =
                  componentCode G z hedge_ne hnode_ne
                    (node G z hedge_ne hnode_ne
                      (old (G.node.symm (G.edge z))))
                rw [node_old_old G z (G.node.symm (G.edge z))
                  hedge_ne hnode_ne]
                simp [componentCode, old, hpz,
                  componentCode_node_old_splice G z]
              · change componentCode G z hedge_ne hnode_ne (old x) =
                  componentCode G z hedge_ne hnode_ne
                    (node G z hedge_ne hnode_ne (old x))
                rw [node_old_old G z x hedge_ne hnode_ne]
                simp [componentCode, old, hxz, hxez]
                exact (G.componentOf_node x).symm
  · subst y
    cases x with
    | new => rfl
    | newEdge => rfl
    | old x =>
        cases x with
        | new =>
            rw [face_old_new G z hedge_ne hnode_ne hplain]
            simp [componentCode, old]
            exact (G.componentOf_face z).symm
        | newEdge => rfl
        | old x =>
            by_cases hxz : x = z
            · subst x
              change componentCode G z hedge_ne hnode_ne (old z) =
                componentCode G z hedge_ne hnode_ne
                  ((hypermap G z hedge_ne hnode_ne).face (old z))
              rw [face_old_z G z hedge_ne hnode_ne hplain]
              simp [componentCode, old]
            · by_cases hx_face_symm : x = G.face.symm z
              · subst x
                change componentCode G z hedge_ne hnode_ne
                    (old (G.face.symm z)) =
                  componentCode G z hedge_ne hnode_ne
                    ((hypermap G z hedge_ne hnode_ne).face
                      (old (G.face.symm z)))
                rw [face_old_face_symm_z G z hedge_ne hnode_ne hplain]
                simp [componentCode, old, componentCode_face_symm_splice G z]
              · change componentCode G z hedge_ne hnode_ne (old x) =
                  componentCode G z hedge_ne hnode_ne
                    ((hypermap G z hedge_ne hnode_ne).face (old x))
                rw [face_old_ne G z x hedge_ne hnode_ne hplain hxz hx_face_symm]
                simp [componentCode, old]
                exact (G.componentOf_face x).symm

theorem componentCode_of_reachable
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    {x y : (hypermap G z hedge_ne hnode_ne).Dart}
    (hxy : (hypermap G z hedge_ne hnode_ne).Reachable x y) :
    componentCode G z hedge_ne hnode_ne x =
      componentCode G z hedge_ne hnode_ne y :=
  hxy.apply_eq (componentCode G z hedge_ne hnode_ne)
    (fun {_ _} h => componentCode_of_link G z hedge_ne hnode_ne hplain h)

theorem old_reachable_edge_forward
    (G : Hypermap) (z x : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z) :
    (hypermap G z hedge_ne hnode_ne).Reachable
      (old x) (old (G.edge x)) := by
  simpa [old] using
    (hypermap G z hedge_ne hnode_ne).reachable_edge (old x)

theorem old_reachable_face_forward
    (G : Hypermap) (z x : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).Reachable
      (old x) (old (G.face x)) := by
  by_cases hxz : x = z
  · subst x
    have h1 :
        (hypermap G z hedge_ne hnode_ne).Reachable (old z) ExtDart.new := by
      have h := (hypermap G z hedge_ne hnode_ne).reachable_node (old z)
      change (hypermap G z hedge_ne hnode_ne).Reachable
        (old z) (nodeToFun G z (old z)) at h
      simpa [nodeToFun, old] using h
    have h2 :
        (hypermap G z hedge_ne hnode_ne).Reachable
          ExtDart.new (ExtDart.old ExtDart.new) := by
      simpa [face_new G z hedge_ne hnode_ne] using
        (hypermap G z hedge_ne hnode_ne).reachable_face ExtDart.new
    have h3 :
        (hypermap G z hedge_ne hnode_ne).Reachable
          (ExtDart.old ExtDart.new) (old (G.face z)) := by
      simpa [face_old_new G z hedge_ne hnode_ne hplain] using
        (hypermap G z hedge_ne hnode_ne).reachable_face
          (ExtDart.old ExtDart.new)
    exact h1.trans (h2.trans h3)
  · by_cases hx_face_symm : x = G.face.symm z
    · subst x
      have h1 :
          (hypermap G z hedge_ne hnode_ne).Reachable
            (old (G.face.symm z)) ExtDart.new := by
        simpa [face_old_face_symm_z G z hedge_ne hnode_ne hplain] using
          (hypermap G z hedge_ne hnode_ne).reachable_face
            (old (G.face.symm z))
      have h2 :
          (hypermap G z hedge_ne hnode_ne).Reachable
            ExtDart.new ExtDart.newEdge := by
        simpa using
          (hypermap G z hedge_ne hnode_ne).reachable_edge ExtDart.new
      have h3 :
          (hypermap G z hedge_ne hnode_ne).Reachable
            ExtDart.newEdge (old z) := by
        simpa [face_newEdge G z hedge_ne hnode_ne] using
          (hypermap G z hedge_ne hnode_ne).reachable_face ExtDart.newEdge
      simpa using h1.trans (h2.trans h3)
    · have h := (hypermap G z hedge_ne hnode_ne).reachable_face (old x)
      simpa [face_old_ne G z x hedge_ne hnode_ne hplain hxz hx_face_symm]
        using h

theorem old_reachable_of_link
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : G.Link x y) :
    (hypermap G z hedge_ne hnode_ne).Reachable
      (old x) (old y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    exact old_reachable_edge_forward G z x hedge_ne hnode_ne
  · subst y
    exact (hypermap G z hedge_ne hnode_ne).nodePermReachable_reachable
      (old_nodeReachable_forward G z x hedge_ne hnode_ne)
  · subst y
    exact old_reachable_face_forward G z x hedge_ne hnode_ne hplain

theorem old_reachable_of_reachable
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain)
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (hypermap G z hedge_ne hnode_ne).Reachable
      (old x) (old y) :=
  hxy.lift' old fun _ _ h =>
    old_reachable_of_link G z hedge_ne hnode_ne hplain h

noncomputable def componentEquiv
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).Component ≃ G.Component where
  toFun :=
    Quotient.lift
      (componentCode G z hedge_ne hnode_ne)
      (by
        intro x y hxy
        exact componentCode_of_reachable G z hedge_ne hnode_ne hplain hxy)
  invFun :=
    Quotient.lift
      (fun x => (hypermap G z hedge_ne hnode_ne).componentOf (old x))
      (by
        intro x y hxy
        exact (hypermap G z hedge_ne hnode_ne).componentOf_eq_componentOf
          (old_reachable_of_reachable G z hedge_ne hnode_ne hplain hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply (hypermap G z hedge_ne hnode_ne).componentOf_eq_componentOf
            have h := (hypermap G z hedge_ne hnode_ne).reachable_node (old z)
            change (hypermap G z hedge_ne hnode_ne).Reachable
              (old z) (nodeToFun G z (old z)) at h
            simpa [nodeToFun, old] using h
        | newEdge =>
            apply (hypermap G z hedge_ne hnode_ne).componentOf_eq_componentOf
            exact (hypermap G z hedge_ne hnode_ne).facePermReachable_reachable
              (faceReachable_old_z_newEdge G z hedge_ne hnode_ne hplain)
        | old x =>
            cases x with
            | new =>
                apply (hypermap G z hedge_ne hnode_ne).componentOf_eq_componentOf
                have h1 :
                    (hypermap G z hedge_ne hnode_ne).Reachable
                      (old z) ExtDart.new := by
                  have h := (hypermap G z hedge_ne hnode_ne).reachable_node (old z)
                  change (hypermap G z hedge_ne hnode_ne).Reachable
                    (old z) (nodeToFun G z (old z)) at h
                  simpa [nodeToFun, old] using h
                have h2 :
                    (hypermap G z hedge_ne hnode_ne).Reachable
                      ExtDart.new (ExtDart.old ExtDart.new) := by
                  simpa [face_new G z hedge_ne hnode_ne] using
                    (hypermap G z hedge_ne hnode_ne).reachable_face ExtDart.new
                exact h1.trans h2
            | newEdge =>
                apply (hypermap G z hedge_ne hnode_ne).componentOf_eq_componentOf
                exact (hypermap G z hedge_ne hnode_ne).facePermReachable_reachable
                  (faceReachable_old_z_old_newEdge G z hedge_ne hnode_ne hplain)
            | old x => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => rfl

theorem componentCount
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).componentCount =
      G.componentCount := by
  unfold Hypermap.componentCount
  exact Nat.card_congr (componentEquiv G z hedge_ne hnode_ne hplain)

theorem eulerLeft
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).eulerLeft = G.eulerLeft + 4 := by
  unfold Hypermap.eulerLeft
  rw [componentCount G z hedge_ne hnode_ne hplain,
    hypermap_card G z hedge_ne hnode_ne]
  omega

theorem eulerRight
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).eulerRight = G.eulerRight + 4 := by
  unfold Hypermap.eulerRight
  rw [edgeOrbitCount G z hedge_ne hnode_ne hplain,
    nodeOrbitCount G z hedge_ne hnode_ne,
    faceOrbitCount G z hedge_ne hnode_ne hplain]
  omega

theorem genus
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).genus = G.genus := by
  unfold Hypermap.genus
  rw [eulerLeft G z hedge_ne hnode_ne hplain,
    eulerRight G z hedge_ne hnode_ne hplain, Nat.add_sub_add_right]

theorem eulerPlanar_iff
    (G : Hypermap) (z : G.Dart)
    (hedge_ne : G.edge z ≠ z)
    (hnode_ne : G.node z ≠ G.edge z)
    (hplain : G.Plain) :
    (hypermap G z hedge_ne hnode_ne).EulerPlanar ↔ G.EulerPlanar := by
  simp [Hypermap.EulerPlanar, genus G z hedge_ne hnode_ne hplain]

end TriangleExtension

end FourColor

end Schematic.Math.GraphTheory
