import Schematic.Math.GraphTheory.Embedding.Hypermap

/-!
Relabelings of finite hypermaps.

Gonthier's development uses `eqm` to transport statements across hypermaps with
the same dart structure.  For the Lean port it is more convenient to use an
explicit permutation-preserving equivalence of dart types.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w

/-- An isomorphism of hypermaps: a bijection of darts commuting with edge,
node, and face permutations. -/
structure Iso (G : Hypermap.{u}) (H : Hypermap.{v}) where
  toEquiv : G.Dart ≃ H.Dart
  map_edge : ∀ x : G.Dart, toEquiv (G.edge x) = H.edge (toEquiv x)
  map_node : ∀ x : G.Dart, toEquiv (G.node x) = H.node (toEquiv x)
  map_face : ∀ x : G.Dart, toEquiv (G.face x) = H.face (toEquiv x)

namespace Iso

variable {G : Hypermap.{u}} {H : Hypermap.{v}} {K : Hypermap.{w}}

/-- The identity hypermap isomorphism. -/
def refl (G : Hypermap.{u}) : Iso G G where
  toEquiv := Equiv.refl G.Dart
  map_edge := by intro x; rfl
  map_node := by intro x; rfl
  map_face := by intro x; rfl

/-- Reverse a hypermap isomorphism. -/
def symm (φ : Iso G H) : Iso H G where
  toEquiv := φ.toEquiv.symm
  map_edge := perm_conj_symm_equiv φ.toEquiv G.edge H.edge φ.map_edge
  map_node := perm_conj_symm_equiv φ.toEquiv G.node H.node φ.map_node
  map_face := perm_conj_symm_equiv φ.toEquiv G.face H.face φ.map_face

/-- Compose hypermap isomorphisms. -/
def trans (φ : Iso G H) (ψ : Iso H K) : Iso G K where
  toEquiv := φ.toEquiv.trans ψ.toEquiv
  map_edge := by
    intro x
    calc
      ψ.toEquiv (φ.toEquiv (G.edge x)) =
          ψ.toEquiv (H.edge (φ.toEquiv x)) := by rw [φ.map_edge x]
      _ = K.edge (ψ.toEquiv (φ.toEquiv x)) := ψ.map_edge (φ.toEquiv x)
  map_node := by
    intro x
    calc
      ψ.toEquiv (φ.toEquiv (G.node x)) =
          ψ.toEquiv (H.node (φ.toEquiv x)) := by rw [φ.map_node x]
      _ = K.node (ψ.toEquiv (φ.toEquiv x)) := ψ.map_node (φ.toEquiv x)
  map_face := by
    intro x
    calc
      ψ.toEquiv (φ.toEquiv (G.face x)) =
          ψ.toEquiv (H.face (φ.toEquiv x)) := by rw [φ.map_face x]
      _ = K.face (ψ.toEquiv (φ.toEquiv x)) := ψ.map_face (φ.toEquiv x)

/-- Relabel a finite hypermap along an arbitrary equivalence of dart types. -/
def relabel (G : Hypermap.{u})
    {β : Type v} [Fintype β] [DecidableEq β]
    (e : G.Dart ≃ β) : Hypermap.{v} where
  Dart := β
  edge := e.symm.trans (G.edge.trans e)
  node := e.symm.trans (G.node.trans e)
  face := e.symm.trans (G.face.trans e)
  node_face_edge := by
    intro x
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply] using
      congrArg e (G.node_face_edge (e.symm x))

/-- The relabeling equivalence is a hypermap isomorphism. -/
def relabelIso (G : Hypermap.{u})
    {β : Type v} [Fintype β] [DecidableEq β]
    (e : G.Dart ≃ β) : Iso G (relabel G e) where
  toEquiv := e
  map_edge := by
    intro x
    change e (G.edge x) = e (G.edge (e.symm (e x)))
    rw [e.symm_apply_apply]
  map_node := by
    intro x
    change e (G.node x) = e (G.node (e.symm (e x)))
    rw [e.symm_apply_apply]
  map_face := by
    intro x
    change e (G.face x) = e (G.face (e.symm (e x)))
    rw [e.symm_apply_apply]

/-- Canonical universe-zero representative of a finite hypermap. -/
noncomputable def finRelabel (G : Hypermap.{u}) : Hypermap.{0} :=
  relabel G (Fintype.equivFin G.Dart)

/-- Every finite hypermap is isomorphic to its universe-zero representative. -/
noncomputable def finRelabelIso (G : Hypermap.{u}) : Iso G (finRelabel G) :=
  relabelIso G (Fintype.equivFin G.Dart)

/-- Taking the dual twice gives the original hypermap. -/
def dualDual (G : Hypermap.{u}) : Iso G.dual.dual G where
  toEquiv := Equiv.refl G.Dart
  map_edge := by intro x; rfl
  map_node := by intro x; rfl
  map_face := by intro x; rfl

/-- Three cyclic `permNode` rotations give the original hypermap. -/
def permNodeCycle (G : Hypermap.{u}) :
    Iso G.permNode.permNode.permNode G where
  toEquiv := Equiv.refl G.Dart
  map_edge := by intro x; rfl
  map_node := by intro x; rfl
  map_face := by intro x; rfl

/-- Three cyclic `permFace` rotations give the original hypermap. -/
def permFaceCycle (G : Hypermap.{u}) :
    Iso G.permFace.permFace.permFace G where
  toEquiv := Equiv.refl G.Dart
  map_edge := by intro x; rfl
  map_node := by intro x; rfl
  map_face := by intro x; rfl

theorem edgeReachable_iff
    (φ : Iso G H) {x y : G.Dart} :
    PermReachable G.edge x y ↔
      PermReachable H.edge (φ.toEquiv x) (φ.toEquiv y) :=
  permReachable_conj_iff φ.toEquiv G.edge H.edge φ.map_edge

theorem nodeReachable_iff
    (φ : Iso G H) {x y : G.Dart} :
    PermReachable G.node x y ↔
      PermReachable H.node (φ.toEquiv x) (φ.toEquiv y) :=
  permReachable_conj_iff φ.toEquiv G.node H.node φ.map_node

theorem faceReachable_iff
    (φ : Iso G H) {x y : G.Dart} :
    PermReachable G.face x y ↔
      PermReachable H.face (φ.toEquiv x) (φ.toEquiv y) :=
  permReachable_conj_iff φ.toEquiv G.face H.face φ.map_face

theorem link
    (φ : Iso G H) {x y : G.Dart}
    (hxy : G.Link x y) :
    H.Link (φ.toEquiv x) (φ.toEquiv y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    exact Or.inl (φ.map_edge x)
  · subst y
    exact Or.inr (Or.inl (φ.map_node x))
  · subst y
    exact Or.inr (Or.inr (φ.map_face x))

theorem reachable
    (φ : Iso G H) {x y : G.Dart}
    (hxy : G.Reachable x y) :
    H.Reachable (φ.toEquiv x) (φ.toEquiv y) := by
  induction hxy with
  | refl => exact H.reachable_refl (φ.toEquiv x)
  | tail hxb hbc ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (φ.link hbc))

theorem reachable_iff
    (φ : Iso G H) {x y : G.Dart} :
    G.Reachable x y ↔
      H.Reachable (φ.toEquiv x) (φ.toEquiv y) := by
  constructor
  · exact φ.reachable
  · intro hxy
    have hback := φ.symm.reachable hxy
    simpa [symm] using hback

theorem preconnected_iff
    (φ : Iso G H) :
    G.Preconnected ↔ H.Preconnected := by
  constructor
  · intro h x y
    have hxy := φ.reachable (h (φ.toEquiv.symm x) (φ.toEquiv.symm y))
    simpa using hxy
  · intro h x y
    have hxy := φ.symm.reachable (h (φ.toEquiv x) (φ.toEquiv y))
    simpa [symm] using hxy

theorem connected_iff
    (φ : Iso G H) :
    G.Connected ↔ H.Connected := by
  constructor
  · intro h
    constructor
    · rcases h.1 with ⟨x⟩
      exact ⟨φ.toEquiv x⟩
    · exact (φ.preconnected_iff).mp h.2
  · intro h
    constructor
    · rcases h.1 with ⟨x⟩
      exact ⟨φ.toEquiv.symm x⟩
    · exact (φ.preconnected_iff).mpr h.2

/-- Isomorphic hypermaps have equivalent generated dart components. -/
noncomputable def componentEquiv
    (φ : Iso G H) :
    G.Component ≃ H.Component :=
  Quotient.congr φ.toEquiv (by
    intro x y
    constructor
    · exact φ.reachable
    · intro hxy
      have hback := φ.symm.reachable hxy
      simpa [symm] using hback)

@[simp]
theorem componentEquiv_componentOf
    (φ : Iso G H)
    (x : G.Dart) :
    φ.componentEquiv (G.componentOf x) =
      H.componentOf (φ.toEquiv x) :=
  rfl

/-- Isomorphic hypermaps have equivalent edge orbits. -/
noncomputable def edgeOrbitEquiv
    (φ : Iso G H) :
    G.EdgeOrbit ≃ H.EdgeOrbit :=
  Quotient.congr φ.toEquiv (by
    intro x y
    exact φ.edgeReachable_iff)

@[simp]
theorem edgeOrbitEquiv_of
    (φ : Iso G H)
    (x : G.Dart) :
    φ.edgeOrbitEquiv (PermOrbit.of G.edge x) =
      PermOrbit.of H.edge (φ.toEquiv x) :=
  rfl

/-- Isomorphic hypermaps have equivalent node orbits. -/
noncomputable def nodeOrbitEquiv
    (φ : Iso G H) :
    G.NodeOrbit ≃ H.NodeOrbit :=
  Quotient.congr φ.toEquiv (by
    intro x y
    exact φ.nodeReachable_iff)

@[simp]
theorem nodeOrbitEquiv_of
    (φ : Iso G H)
    (x : G.Dart) :
    φ.nodeOrbitEquiv (PermOrbit.of G.node x) =
      PermOrbit.of H.node (φ.toEquiv x) :=
  rfl

/-- Isomorphic hypermaps have equivalent face orbits. -/
noncomputable def faceOrbitEquiv
    (φ : Iso G H) :
    G.FaceOrbit ≃ H.FaceOrbit :=
  Quotient.congr φ.toEquiv (by
    intro x y
    exact φ.faceReachable_iff)

@[simp]
theorem faceOrbitEquiv_of
    (φ : Iso G H)
    (x : G.Dart) :
    φ.faceOrbitEquiv (PermOrbit.of G.face x) =
      PermOrbit.of H.face (φ.toEquiv x) :=
  rfl

theorem componentCount_eq
    (φ : Iso G H) :
    G.componentCount = H.componentCount :=
  Nat.card_congr φ.componentEquiv

theorem edgeOrbitCount_eq
    (φ : Iso G H) :
    G.edgeOrbitCount = H.edgeOrbitCount :=
  Nat.card_congr φ.edgeOrbitEquiv

theorem nodeOrbitCount_eq
    (φ : Iso G H) :
    G.nodeOrbitCount = H.nodeOrbitCount :=
  Nat.card_congr φ.nodeOrbitEquiv

theorem faceOrbitCount_eq
    (φ : Iso G H) :
    G.faceOrbitCount = H.faceOrbitCount :=
  Nat.card_congr φ.faceOrbitEquiv

theorem dart_card_eq
    (φ : Iso G H) :
    Fintype.card G.Dart = Fintype.card H.Dart :=
  Fintype.card_congr φ.toEquiv

theorem eulerLeft_eq
    (φ : Iso G H) :
    G.eulerLeft = H.eulerLeft := by
  change
    2 * G.componentCount + Fintype.card G.Dart =
      2 * H.componentCount + Fintype.card H.Dart
  rw [φ.componentCount_eq, φ.dart_card_eq]

theorem eulerRight_eq
    (φ : Iso G H) :
    G.eulerRight = H.eulerRight := by
  change
    G.edgeOrbitCount + G.nodeOrbitCount + G.faceOrbitCount =
      H.edgeOrbitCount + H.nodeOrbitCount + H.faceOrbitCount
  rw [φ.edgeOrbitCount_eq, φ.nodeOrbitCount_eq, φ.faceOrbitCount_eq]

theorem genus_eq
    (φ : Iso G H) :
    G.genus = H.genus := by
  change (G.eulerLeft - G.eulerRight) / 2 =
    (H.eulerLeft - H.eulerRight) / 2
  rw [φ.eulerLeft_eq, φ.eulerRight_eq]

theorem evenGenus_iff
    (φ : Iso G H) :
    G.EvenGenus ↔ H.EvenGenus := by
  simp [EvenGenus, φ.eulerLeft_eq, φ.eulerRight_eq, φ.genus_eq]

theorem eulerPlanar_iff
    (φ : Iso G H) :
    G.EulerPlanar ↔ H.EulerPlanar := by
  simp [EulerPlanar, φ.genus_eq]

end Iso

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
