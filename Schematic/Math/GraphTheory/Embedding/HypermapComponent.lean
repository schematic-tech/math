import Schematic.Math.GraphTheory.Embedding.Coloring
import Schematic.Math.GraphTheory.Embedding.Counts
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Connected-component decomposition for finite hypermaps.

This file builds the induced hypermap on a generated dart component.  The
component construction is reusable background for the standard minimality
argument: if every component of a disconnected map is smaller and colourable,
then the original map is colourable componentwise.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

noncomputable section

variable (G : Hypermap.{u})

noncomputable instance componentFintype : Fintype G.Component := by
  classical
  letI : DecidableRel G.reachableSetoid.r := Classical.decRel _
  exact Quotient.fintype G.reachableSetoid

noncomputable instance componentDecidableEq : DecidableEq G.Component := by
  classical
  infer_instance

/-- Darts lying in one generated component of a hypermap. -/
def ComponentDart (c : G.Component) : Type u :=
  {x : G.Dart // G.componentOf x = c}

namespace ComponentDart

variable {G} {c : G.Component}

instance : Fintype (G.ComponentDart c) := by
  classical
  haveI : Finite (G.ComponentDart c) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

instance : DecidableEq (G.ComponentDart c) := by
  classical
  infer_instance

theorem componentOf_val (x : G.ComponentDart c) :
    G.componentOf x.1 = c :=
  x.2

theorem componentOf_edge_symm (x : G.Dart) :
    G.componentOf (G.edge.symm x) = G.componentOf x :=
  G.componentOf_eq_componentOf (by
    simpa using G.reachable_edge (G.edge.symm x))

theorem componentOf_node_symm (x : G.Dart) :
    G.componentOf (G.node.symm x) = G.componentOf x :=
  G.componentOf_eq_componentOf (by
    simpa using G.reachable_node (G.node.symm x))

theorem componentOf_face_symm (x : G.Dart) :
    G.componentOf (G.face.symm x) = G.componentOf x :=
  G.componentOf_eq_componentOf (by
    simpa using G.reachable_face (G.face.symm x))

/-- Restriction of the edge permutation to a generated component. -/
def edge (c : G.Component) : Equiv.Perm (G.ComponentDart c) where
  toFun x := ⟨G.edge x.1, by
    rw [G.componentOf_edge x.1, x.2]⟩
  invFun x := ⟨G.edge.symm x.1, by
    rw [componentOf_edge_symm (G := G) x.1, x.2]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- Restriction of the node permutation to a generated component. -/
def node (c : G.Component) : Equiv.Perm (G.ComponentDart c) where
  toFun x := ⟨G.node x.1, by
    rw [G.componentOf_node x.1, x.2]⟩
  invFun x := ⟨G.node.symm x.1, by
    rw [componentOf_node_symm (G := G) x.1, x.2]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- Restriction of the face permutation to a generated component. -/
def face (c : G.Component) : Equiv.Perm (G.ComponentDart c) where
  toFun x := ⟨G.face x.1, by
    rw [G.componentOf_face x.1, x.2]⟩
  invFun x := ⟨G.face.symm x.1, by
    rw [componentOf_face_symm (G := G) x.1, x.2]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

@[simp]
theorem edge_val (x : G.ComponentDart c) :
    (edge (G := G) c x).1 = G.edge x.1 :=
  rfl

@[simp]
theorem node_val (x : G.ComponentDart c) :
    (node (G := G) c x).1 = G.node x.1 :=
  rfl

@[simp]
theorem face_val (x : G.ComponentDart c) :
    (face (G := G) c x).1 = G.face x.1 :=
  rfl

end ComponentDart

/-- The hypermap induced by one generated dart component. -/
def componentHypermap (c : G.Component) : Hypermap.{u} where
  Dart := G.ComponentDart c
  edge := ComponentDart.edge (G := G) c
  node := ComponentDart.node (G := G) c
  face := ComponentDart.face (G := G) c
  node_face_edge := by
    intro x
    apply Subtype.ext
    exact G.node_face_edge x.1

namespace componentHypermap

variable {G} {c : G.Component}

@[simp]
theorem edge_val (x : (G.componentHypermap c).Dart) :
    ((G.componentHypermap c).edge x).1 = G.edge x.1 :=
  rfl

@[simp]
theorem node_val (x : (G.componentHypermap c).Dart) :
    ((G.componentHypermap c).node x).1 = G.node x.1 :=
  rfl

@[simp]
theorem face_val (x : (G.componentHypermap c).Dart) :
    ((G.componentHypermap c).face x).1 = G.face x.1 :=
  rfl

theorem edge_symm_val (x : (G.componentHypermap c).Dart) :
    ((G.componentHypermap c).edge.symm x).1 = G.edge.symm x.1 :=
  rfl

theorem node_symm_val (x : (G.componentHypermap c).Dart) :
    ((G.componentHypermap c).node.symm x).1 = G.node.symm x.1 :=
  rfl

theorem face_symm_val (x : (G.componentHypermap c).Dart) :
    ((G.componentHypermap c).face.symm x).1 = G.face.symm x.1 :=
  rfl

theorem edgeReachable_val
    {x y : (G.componentHypermap c).Dart}
    (hxy : PermReachable (G.componentHypermap c).edge x y) :
    PermReachable G.edge x.1 y.1 :=
  PermReachable.map_of_forward_simulation
    (G.componentHypermap c).edge G.edge Subtype.val
    (fun z => by simpa using PermReachable.forward G.edge z.1) hxy

theorem nodeReachable_val
    {x y : (G.componentHypermap c).Dart}
    (hxy : PermReachable (G.componentHypermap c).node x y) :
    PermReachable G.node x.1 y.1 :=
  PermReachable.map_of_forward_simulation
    (G.componentHypermap c).node G.node Subtype.val
    (fun z => by simpa using PermReachable.forward G.node z.1) hxy

theorem faceReachable_val
    {x y : (G.componentHypermap c).Dart}
    (hxy : PermReachable (G.componentHypermap c).face x y) :
    PermReachable G.face x.1 y.1 :=
  PermReachable.map_of_forward_simulation
    (G.componentHypermap c).face G.face Subtype.val
    (fun z => by simpa using PermReachable.forward G.face z.1) hxy

theorem componentOf_eq_of_edgeReachable
    {x y : G.Dart} (hxy : PermReachable G.edge x y) :
    G.componentOf x = G.componentOf y :=
  hxy.apply_eq G.componentOf fun {_ _} hbd => by
    cases hbd
    · simpa using (G.componentOf_edge _).symm
    · simpa using
        (ComponentDart.componentOf_edge_symm (G := G) _).symm

theorem componentOf_eq_of_nodeReachable
    {x y : G.Dart} (hxy : PermReachable G.node x y) :
    G.componentOf x = G.componentOf y :=
  hxy.apply_eq G.componentOf fun {_ _} hbd => by
    cases hbd
    · simpa using (G.componentOf_node _).symm
    · simpa using
        (ComponentDart.componentOf_node_symm (G := G) _).symm

theorem componentOf_eq_of_faceReachable
    {x y : G.Dart} (hxy : PermReachable G.face x y) :
    G.componentOf x = G.componentOf y :=
  hxy.apply_eq G.componentOf fun {_ _} hbd => by
    cases hbd
    · simpa using (G.componentOf_face _).symm
    · simpa using
        (ComponentDart.componentOf_face_symm (G := G) _).symm

theorem edgeLink_lift
    {x y : G.Dart} (hx : G.componentOf x = c) (hy : G.componentOf y = c)
    (hxy : PermLink G.edge x y) :
    PermLink (G.componentHypermap c).edge ⟨x, hx⟩ ⟨y, hy⟩ := by
  cases hxy
  · exact PermLink.forward _
  · simpa [edge_symm_val] using
      (PermLink.backward
        (σ := (G.componentHypermap c).edge)
        (⟨x, hx⟩ : (G.componentHypermap c).Dart))

theorem nodeLink_lift
    {x y : G.Dart} (hx : G.componentOf x = c) (hy : G.componentOf y = c)
    (hxy : PermLink G.node x y) :
    PermLink (G.componentHypermap c).node ⟨x, hx⟩ ⟨y, hy⟩ := by
  cases hxy
  · exact PermLink.forward _
  · simpa [node_symm_val] using
      (PermLink.backward
        (σ := (G.componentHypermap c).node)
        (⟨x, hx⟩ : (G.componentHypermap c).Dart))

theorem faceLink_lift
    {x y : G.Dart} (hx : G.componentOf x = c) (hy : G.componentOf y = c)
    (hxy : PermLink G.face x y) :
    PermLink (G.componentHypermap c).face ⟨x, hx⟩ ⟨y, hy⟩ := by
  cases hxy
  · exact PermLink.forward _
  · simpa [face_symm_val] using
      (PermLink.backward
        (σ := (G.componentHypermap c).face)
        (⟨x, hx⟩ : (G.componentHypermap c).Dart))

theorem edgeReachable_lift_of_val
    {x : (G.componentHypermap c).Dart} {y : G.Dart}
    (hy : G.componentOf y = c)
    (hxy : PermReachable G.edge x.1 y) :
    PermReachable (G.componentHypermap c).edge x ⟨y, hy⟩ :=
  Relation.ReflTransGen.liftSubtype
    (fun {_ _} h ha => (componentOf_eq_of_edgeReachable (G := G) h).symm.trans ha)
    (fun {_ _} ha hb h => edgeLink_lift (G := G) (c := c) ha hb h)
    x hy hxy

theorem nodeReachable_lift_of_val
    {x : (G.componentHypermap c).Dart} {y : G.Dart}
    (hy : G.componentOf y = c)
    (hxy : PermReachable G.node x.1 y) :
    PermReachable (G.componentHypermap c).node x ⟨y, hy⟩ :=
  Relation.ReflTransGen.liftSubtype
    (fun {_ _} h ha => (componentOf_eq_of_nodeReachable (G := G) h).symm.trans ha)
    (fun {_ _} ha hb h => nodeLink_lift (G := G) (c := c) ha hb h)
    x hy hxy

theorem faceReachable_lift_of_val
    {x : (G.componentHypermap c).Dart} {y : G.Dart}
    (hy : G.componentOf y = c)
    (hxy : PermReachable G.face x.1 y) :
    PermReachable (G.componentHypermap c).face x ⟨y, hy⟩ :=
  Relation.ReflTransGen.liftSubtype
    (fun {_ _} h ha => (componentOf_eq_of_faceReachable (G := G) h).symm.trans ha)
    (fun {_ _} ha hb h => faceLink_lift (G := G) (c := c) ha hb h)
    x hy hxy

theorem edgeReachable_lift
    {x y : (G.componentHypermap c).Dart}
    (hxy : PermReachable G.edge x.1 y.1) :
    PermReachable (G.componentHypermap c).edge x y :=
  edgeReachable_lift_of_val (G := G) (c := c) y.2 hxy

theorem nodeReachable_lift
    {x y : (G.componentHypermap c).Dart}
    (hxy : PermReachable G.node x.1 y.1) :
    PermReachable (G.componentHypermap c).node x y :=
  nodeReachable_lift_of_val (G := G) (c := c) y.2 hxy

theorem faceReachable_lift
    {x y : (G.componentHypermap c).Dart}
    (hxy : PermReachable G.face x.1 y.1) :
    PermReachable (G.componentHypermap c).face x y :=
  faceReachable_lift_of_val (G := G) (c := c) y.2 hxy

theorem link_lift
    {x y : G.Dart} (hx : G.componentOf x = c) (hy : G.componentOf y = c)
    (hxy : G.Link x y) :
    (G.componentHypermap c).Link ⟨x, hx⟩ ⟨y, hy⟩ := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    exact Or.inl (Subtype.ext rfl)
  · subst y
    exact Or.inr (Or.inl (Subtype.ext rfl))
  · subst y
    exact Or.inr (Or.inr (Subtype.ext rfl))

theorem reachable_lift_of_val
    {x : (G.componentHypermap c).Dart} {y : G.Dart}
    (hy : G.componentOf y = c)
    (hxy : G.Reachable x.1 y) :
    (G.componentHypermap c).Reachable x ⟨y, hy⟩ :=
  Relation.ReflTransGen.liftSubtype
    (fun {_ _} h ha => (G.componentOf_eq_componentOf h).symm.trans ha)
    (fun {_ _} ha hb h => link_lift (G := G) (c := c) ha hb h)
    x hy hxy

theorem reachable_lift
    {x y : (G.componentHypermap c).Dart}
    (hxy : G.Reachable x.1 y.1) :
    (G.componentHypermap c).Reachable x y :=
  reachable_lift_of_val (G := G) (c := c) y.2 hxy

theorem coloring_restrict
    {k : G.Dart → Color}
    (hk : G.Coloring k) :
    (G.componentHypermap c).Coloring
      (fun x : (G.componentHypermap c).Dart => k x.1) := by
  constructor
  · intro x hsame
    exact hk.1 x.1 hsame
  · intro x
    exact hk.2 x.1

theorem fourColorable_restrict
    (hG : G.FourColorable) :
    (G.componentHypermap c).FourColorable := by
  rcases hG with ⟨k, hk⟩
  exact ⟨fun x => k x.1, coloring_restrict (G := G) (c := c) hk⟩

theorem bridgeless
    (hG : G.Bridgeless) :
    (G.componentHypermap c).Bridgeless := by
  intro x hface
  exact hG x.1 (by
    simpa using faceReachable_val (G := G) (c := c) hface)

theorem plain
    (hG : G.Plain) :
    (G.componentHypermap c).Plain := by
  intro x
  constructor
  · apply Subtype.ext
    exact (hG x.1).1
  · intro hfixed
    exact (hG x.1).2 (Subtype.ext_iff.mp hfixed)

theorem precubic
    (hG : G.Precubic) :
    (G.componentHypermap c).Precubic := by
  intro x
  rcases hG x.1 with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

theorem planarBridgelessPlainPrecubic
    (hplanar : (G.componentHypermap c).EulerPlanar)
    (hG : G.PlanarBridgelessPlainPrecubic) :
    (G.componentHypermap c).PlanarBridgelessPlainPrecubic where
  base := {
    base := {
      planar := hplanar
      bridgeless := bridgeless (G := G) (c := c) hG.base.base.bridgeless }
    plain := plain (G := G) (c := c) hG.base.plain }
  precubic := precubic (G := G) (c := c) hG.precubic

theorem connected :
    (G.componentHypermap c).Connected := by
  have hnonempty : Nonempty (G.componentHypermap c).Dart := by
    refine ⟨⟨Quotient.out c, ?_⟩⟩
    exact Quotient.out_eq c
  refine ⟨hnonempty, ?_⟩
  intro x y
  exact reachable_lift (G := G) (c := c)
    (G.reachable_of_componentOf_eq (x.2.trans y.2.symm))

theorem componentCount_eq_one :
    (G.componentHypermap c).componentCount = 1 :=
  Connected.componentCount_eq_one
    (G := G.componentHypermap c) (connected (G := G) (c := c))

theorem component_card_eq_one :
    Fintype.card (G.componentHypermap c).Component = 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact componentCount_eq_one (G := G) (c := c)

/-- The dart set of a hypermap is the disjoint sum of its component dart sets. -/
noncomputable def dartSigmaEquiv :
    (Sigma fun c : G.Component => (G.componentHypermap c).Dart) ≃
      G.Dart where
  toFun p := p.2.1
  invFun x := ⟨G.componentOf x,
    (⟨x, rfl⟩ : (G.componentHypermap (G.componentOf x)).Dart)⟩
  left_inv p := by
    rcases p with ⟨c, x, hx⟩
    dsimp
    cases hx
    rfl
  right_inv x := rfl

theorem card_dart_eq_sum_componentDart :
    Fintype.card G.Dart =
      ∑ c : G.Component, Fintype.card (G.componentHypermap c).Dart := by
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (dartSigmaEquiv (G := G))).symm

/-- Send an edge orbit of a component to the corresponding edge orbit of the
ambient hypermap. -/
noncomputable def edgeOrbitMap :
    (G.componentHypermap c).EdgeOrbit → G.EdgeOrbit :=
  Quot.lift
    (fun x : (G.componentHypermap c).Dart => PermOrbit.of G.edge x.1)
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of G.edge
        (edgeReachable_val (G := G) (c := c) hxy))

@[simp]
theorem edgeOrbitMap_of (x : (G.componentHypermap c).Dart) :
    edgeOrbitMap (G := G) (c := c)
        (PermOrbit.of (G.componentHypermap c).edge x) =
      PermOrbit.of G.edge x.1 :=
  rfl

theorem edgeOrbitMap_injective :
    Function.Injective (edgeOrbitMap (G := G) (c := c)) := by
  intro o p hop
  refine Quotient.inductionOn₂ o p ?_ hop
  intro x y hxy
  change PermOrbit.of G.edge x.1 = PermOrbit.of G.edge y.1 at hxy
  exact Quot.sound
    (edgeReachable_lift (G := G) (c := c) (Quotient.exact hxy))

/-- Send a node orbit of a component to the corresponding node orbit of the
ambient hypermap. -/
noncomputable def nodeOrbitMap :
    (G.componentHypermap c).NodeOrbit → G.NodeOrbit :=
  Quot.lift
    (fun x : (G.componentHypermap c).Dart => PermOrbit.of G.node x.1)
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of G.node
        (nodeReachable_val (G := G) (c := c) hxy))

@[simp]
theorem nodeOrbitMap_of (x : (G.componentHypermap c).Dart) :
    nodeOrbitMap (G := G) (c := c)
        (PermOrbit.of (G.componentHypermap c).node x) =
      PermOrbit.of G.node x.1 :=
  rfl

theorem nodeOrbitMap_injective :
    Function.Injective (nodeOrbitMap (G := G) (c := c)) := by
  intro o p hop
  refine Quotient.inductionOn₂ o p ?_ hop
  intro x y hxy
  change PermOrbit.of G.node x.1 = PermOrbit.of G.node y.1 at hxy
  exact Quot.sound
    (nodeReachable_lift (G := G) (c := c) (Quotient.exact hxy))

/-- Send a face orbit of a component to the corresponding face orbit of the
ambient hypermap. -/
noncomputable def faceOrbitMap :
    (G.componentHypermap c).FaceOrbit → G.FaceOrbit :=
  Quot.lift
    (fun x : (G.componentHypermap c).Dart => PermOrbit.of G.face x.1)
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of G.face
        (faceReachable_val (G := G) (c := c) hxy))

@[simp]
theorem faceOrbitMap_of (x : (G.componentHypermap c).Dart) :
    faceOrbitMap (G := G) (c := c)
        (PermOrbit.of (G.componentHypermap c).face x) =
      PermOrbit.of G.face x.1 :=
  rfl

theorem faceOrbitMap_injective :
    Function.Injective (faceOrbitMap (G := G) (c := c)) := by
  intro o p hop
  refine Quotient.inductionOn₂ o p ?_ hop
  intro x y hxy
  change PermOrbit.of G.face x.1 = PermOrbit.of G.face y.1 at hxy
  exact Quot.sound
    (faceReachable_lift (G := G) (c := c) (Quotient.exact hxy))

theorem edgeOrbitCount_le :
    (G.componentHypermap c).edgeOrbitCount ≤ G.edgeOrbitCount := by
  unfold Hypermap.edgeOrbitCount
  exact Nat.card_le_card_of_injective
    (edgeOrbitMap (G := G) (c := c))
    (edgeOrbitMap_injective (G := G) (c := c))

/-- Global edge orbits are the disjoint sum of component edge orbits. -/
noncomputable def edgeOrbitSigmaMap :
    (Sigma fun c : G.Component => (G.componentHypermap c).EdgeOrbit) →
      G.EdgeOrbit
  | ⟨c, o⟩ => edgeOrbitMap (G := G) (c := c) o

theorem edgeOrbitSigmaMap_surjective :
    Function.Surjective (edgeOrbitSigmaMap (G := G)) := by
  intro o
  refine Quotient.inductionOn o ?_
  intro x
  refine ⟨⟨G.componentOf x,
    PermOrbit.of (G.componentHypermap (G.componentOf x)).edge
      (⟨x, rfl⟩ : (G.componentHypermap (G.componentOf x)).Dart)⟩, ?_⟩
  rfl

theorem edgeOrbitSigmaMap_injective :
    Function.Injective (edgeOrbitSigmaMap (G := G)) := by
  rintro ⟨c, o⟩ ⟨d, p⟩ hmap
  revert hmap
  refine Quotient.inductionOn₂ o p ?_
  intro x y hmap
  change PermOrbit.of G.edge x.1 = PermOrbit.of G.edge y.1 at hmap
  have hreach : PermReachable G.edge x.1 y.1 := Quotient.exact hmap
  have hcd : c = d := by
    calc
      c = G.componentOf x.1 := x.2.symm
      _ = G.componentOf y.1 :=
        componentOf_eq_of_edgeReachable (G := G) hreach
      _ = d := y.2
  cases hcd
  exact Sigma.ext rfl
    (heq_of_eq (Quot.sound
      (edgeReachable_lift (G := G) (c := c) hreach)))

noncomputable def edgeOrbitSigmaEquiv :
    (Sigma fun c : G.Component => (G.componentHypermap c).EdgeOrbit) ≃
      G.EdgeOrbit :=
  Equiv.ofBijective (edgeOrbitSigmaMap (G := G))
    ⟨edgeOrbitSigmaMap_injective (G := G),
      edgeOrbitSigmaMap_surjective (G := G)⟩

theorem edgeOrbitCount_eq_sum_components :
    G.edgeOrbitCount =
      ∑ c : G.Component, (G.componentHypermap c).edgeOrbitCount := by
  change Nat.card G.EdgeOrbit =
    ∑ c : G.Component, Nat.card (G.componentHypermap c).EdgeOrbit
  rw [← Nat.card_sigma]
  exact (Nat.card_congr (edgeOrbitSigmaEquiv (G := G))).symm

theorem nodeOrbitCount_le :
    (G.componentHypermap c).nodeOrbitCount ≤ G.nodeOrbitCount := by
  unfold Hypermap.nodeOrbitCount
  exact Nat.card_le_card_of_injective
    (nodeOrbitMap (G := G) (c := c))
    (nodeOrbitMap_injective (G := G) (c := c))

/-- Global node orbits are the disjoint sum of component node orbits. -/
noncomputable def nodeOrbitSigmaMap :
    (Sigma fun c : G.Component => (G.componentHypermap c).NodeOrbit) →
      G.NodeOrbit
  | ⟨c, o⟩ => nodeOrbitMap (G := G) (c := c) o

theorem nodeOrbitSigmaMap_surjective :
    Function.Surjective (nodeOrbitSigmaMap (G := G)) := by
  intro o
  refine Quotient.inductionOn o ?_
  intro x
  refine ⟨⟨G.componentOf x,
    PermOrbit.of (G.componentHypermap (G.componentOf x)).node
      (⟨x, rfl⟩ : (G.componentHypermap (G.componentOf x)).Dart)⟩, ?_⟩
  rfl

theorem nodeOrbitSigmaMap_injective :
    Function.Injective (nodeOrbitSigmaMap (G := G)) := by
  rintro ⟨c, o⟩ ⟨d, p⟩ hmap
  revert hmap
  refine Quotient.inductionOn₂ o p ?_
  intro x y hmap
  change PermOrbit.of G.node x.1 = PermOrbit.of G.node y.1 at hmap
  have hreach : PermReachable G.node x.1 y.1 := Quotient.exact hmap
  have hcd : c = d := by
    calc
      c = G.componentOf x.1 := x.2.symm
      _ = G.componentOf y.1 :=
        componentOf_eq_of_nodeReachable (G := G) hreach
      _ = d := y.2
  cases hcd
  exact Sigma.ext rfl
    (heq_of_eq (Quot.sound
      (nodeReachable_lift (G := G) (c := c) hreach)))

noncomputable def nodeOrbitSigmaEquiv :
    (Sigma fun c : G.Component => (G.componentHypermap c).NodeOrbit) ≃
      G.NodeOrbit :=
  Equiv.ofBijective (nodeOrbitSigmaMap (G := G))
    ⟨nodeOrbitSigmaMap_injective (G := G),
      nodeOrbitSigmaMap_surjective (G := G)⟩

theorem nodeOrbitCount_eq_sum_components :
    G.nodeOrbitCount =
      ∑ c : G.Component, (G.componentHypermap c).nodeOrbitCount := by
  change Nat.card G.NodeOrbit =
    ∑ c : G.Component, Nat.card (G.componentHypermap c).NodeOrbit
  rw [← Nat.card_sigma]
  exact (Nat.card_congr (nodeOrbitSigmaEquiv (G := G))).symm

theorem faceOrbitCount_le :
    (G.componentHypermap c).faceOrbitCount ≤ G.faceOrbitCount := by
  unfold Hypermap.faceOrbitCount
  exact Nat.card_le_card_of_injective
    (faceOrbitMap (G := G) (c := c))
    (faceOrbitMap_injective (G := G) (c := c))

/-- Global face orbits are the disjoint sum of component face orbits. -/
noncomputable def faceOrbitSigmaMap :
    (Sigma fun c : G.Component => (G.componentHypermap c).FaceOrbit) →
      G.FaceOrbit
  | ⟨c, o⟩ => faceOrbitMap (G := G) (c := c) o

theorem faceOrbitSigmaMap_surjective :
    Function.Surjective (faceOrbitSigmaMap (G := G)) := by
  intro o
  refine Quotient.inductionOn o ?_
  intro x
  refine ⟨⟨G.componentOf x,
    PermOrbit.of (G.componentHypermap (G.componentOf x)).face
      (⟨x, rfl⟩ : (G.componentHypermap (G.componentOf x)).Dart)⟩, ?_⟩
  rfl

theorem faceOrbitSigmaMap_injective :
    Function.Injective (faceOrbitSigmaMap (G := G)) := by
  rintro ⟨c, o⟩ ⟨d, p⟩ hmap
  revert hmap
  refine Quotient.inductionOn₂ o p ?_
  intro x y hmap
  change PermOrbit.of G.face x.1 = PermOrbit.of G.face y.1 at hmap
  have hreach : PermReachable G.face x.1 y.1 := Quotient.exact hmap
  have hcd : c = d := by
    calc
      c = G.componentOf x.1 := x.2.symm
      _ = G.componentOf y.1 :=
        componentOf_eq_of_faceReachable (G := G) hreach
      _ = d := y.2
  cases hcd
  exact Sigma.ext rfl
    (heq_of_eq (Quot.sound
      (faceReachable_lift (G := G) (c := c) hreach)))

noncomputable def faceOrbitSigmaEquiv :
    (Sigma fun c : G.Component => (G.componentHypermap c).FaceOrbit) ≃
      G.FaceOrbit :=
  Equiv.ofBijective (faceOrbitSigmaMap (G := G))
    ⟨faceOrbitSigmaMap_injective (G := G),
      faceOrbitSigmaMap_surjective (G := G)⟩

theorem faceOrbitCount_eq_sum_components :
    G.faceOrbitCount =
      ∑ c : G.Component, (G.componentHypermap c).faceOrbitCount := by
  change Nat.card G.FaceOrbit =
    ∑ c : G.Component, Nat.card (G.componentHypermap c).FaceOrbit
  rw [← Nat.card_sigma]
  exact (Nat.card_congr (faceOrbitSigmaEquiv (G := G))).symm

theorem eulerRight_eq_sum_components :
    G.eulerRight =
      ∑ c : G.Component, (G.componentHypermap c).eulerRight := by
  simp [Hypermap.eulerRight, edgeOrbitCount_eq_sum_components (G := G),
    nodeOrbitCount_eq_sum_components (G := G),
    faceOrbitCount_eq_sum_components (G := G),
    Finset.sum_add_distrib, add_left_comm, add_comm]

theorem eulerLeft_eq_sum_components :
    G.eulerLeft =
      ∑ c : G.Component, (G.componentHypermap c).eulerLeft := by
  simp [Hypermap.eulerLeft, Hypermap.componentCount, Nat.card_eq_fintype_card,
    card_dart_eq_sum_componentDart (G := G),
    component_card_eq_one (G := G),
    Finset.sum_add_distrib, Finset.sum_const, Nat.mul_comm]

theorem eulerPlanar_of_forall_component_eulerLeft_le_eulerRight
    (h :
      forall c : G.Component,
        (G.componentHypermap c).eulerLeft <=
          (G.componentHypermap c).eulerRight) :
    G.EulerPlanar := by
  have hleft :
      G.eulerLeft <= G.eulerRight := by
    rw [eulerLeft_eq_sum_components (G := G),
      eulerRight_eq_sum_components (G := G)]
    exact Finset.sum_le_sum (by
      intro c _hc
      exact h c)
  exact Hypermap.eulerPlanar_of_eulerLeft_le_eulerRight (G := G) hleft

theorem sum_nat_sub_eq_sum_sub_of_le
    {ι : Type v} [DecidableEq ι] (s : Finset ι)
    (a b : ι → Nat)
    (h : ∀ i ∈ s, b i ≤ a i) :
    (∑ i ∈ s, a i) - (∑ i ∈ s, b i) =
      ∑ i ∈ s, (a i - b i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s his ih =>
      have hi_le : b i ≤ a i := h i (by simp [his])
      have htail : ∀ j ∈ s, b j ≤ a j := by
        intro j hj
        exact h j (by simp [hj])
      have hsum_le : (∑ j ∈ s, b j) ≤ ∑ j ∈ s, a j :=
        Finset.sum_le_sum (fun j hj => htail j hj)
      have ih' := ih htail
      simp [Finset.sum_insert, his]
      omega

theorem card_lt_of_not_preconnected
    (hpre : ¬ G.Preconnected)
    (c : G.Component) :
    Fintype.card (G.componentHypermap c).Dart < Fintype.card G.Dart := by
  classical
  have hproper : ∃ y : G.Dart, G.componentOf y ≠ c := by
    by_contra hnone
    have hall : ∀ y : G.Dart, G.componentOf y = c := by
      intro y
      exact not_not.mp (by
        intro hy
        exact hnone ⟨y, hy⟩)
    apply hpre
    intro x y
    exact G.reachable_of_componentOf_eq ((hall x).trans (hall y).symm)
  rcases hproper with ⟨y, hy⟩
  exact Fintype.card_lt_of_injective_of_notMem
    (b := y)
    (fun x : (G.componentHypermap c).Dart => x.1)
    (fun x y hxy => Subtype.ext hxy)
    (by
      rintro ⟨x, hx⟩
      exact hy (by
        rw [← hx]
        exact x.2))

end componentHypermap

theorem fourColorable_of_forall_component_fourColorable
    (hcomp : ∀ c : G.Component, (G.componentHypermap c).FourColorable) :
    G.FourColorable := by
  classical
  let color :
      ∀ c : G.Component, (G.componentHypermap c).Dart → Color :=
    fun c => Classical.choose (hcomp c)
  have hcolor :
      ∀ c : G.Component,
        (G.componentHypermap c).Coloring (color c) :=
    fun c => Classical.choose_spec (hcomp c)
  let colorAt (c : G.Component) (x : G.Dart) : Color :=
    if h : G.componentOf x = c then
      color c ⟨x, h⟩
    else
      Color.zero
  refine ⟨fun x => colorAt (G.componentOf x) x, ?_⟩
  constructor
  · intro x
    have hcx : G.componentOf (G.edge x) = G.componentOf x :=
      G.componentOf_edge x
    have h := (hcolor (G.componentOf x)).1
      (⟨x, rfl⟩ : (G.componentHypermap (G.componentOf x)).Dart)
    have hxedge :
        ((G.componentHypermap (G.componentOf x)).edge
            (⟨x, rfl⟩ :
              (G.componentHypermap (G.componentOf x)).Dart)) =
          (⟨G.edge x, hcx⟩ :
            (G.componentHypermap (G.componentOf x)).Dart) := by
      apply Subtype.ext
      rfl
    rw [hxedge] at h
    simpa [colorAt, hcx] using h
  · intro x
    have hcx : G.componentOf (G.face x) = G.componentOf x :=
      G.componentOf_face x
    have h := (hcolor (G.componentOf x)).2
      (⟨x, rfl⟩ : (G.componentHypermap (G.componentOf x)).Dart)
    have hxface :
        ((G.componentHypermap (G.componentOf x)).face
            (⟨x, rfl⟩ :
              (G.componentHypermap (G.componentOf x)).Dart)) =
          (⟨G.face x, hcx⟩ :
            (G.componentHypermap (G.componentOf x)).Dart) := by
      apply Subtype.ext
      rfl
    rw [hxface] at h
    simpa [colorAt, hcx] using h

theorem exists_component_not_fourColorable_of_not_fourColorable
    (hG : ¬ G.FourColorable) :
    ∃ c : G.Component, ¬ (G.componentHypermap c).FourColorable := by
  classical
  by_contra hnone
  apply hG
  exact G.fourColorable_of_forall_component_fourColorable (by
    intro c
    exact not_not.mp (by
      intro hc
      exact hnone ⟨c, hc⟩))

theorem fourColorable_of_isEmpty [IsEmpty G.Dart] :
    G.FourColorable := by
  refine ⟨fun x => False.elim (isEmptyElim x), ?_⟩
  constructor <;> intro x
  · exact False.elim (isEmptyElim x)
  · exact False.elim (isEmptyElim x)

theorem nonempty_of_not_fourColorable
    (hG : ¬ G.FourColorable) :
    Nonempty G.Dart := by
  by_contra hnon
  haveI : IsEmpty G.Dart := ⟨fun x => hnon ⟨x⟩⟩
  exact hG (G.fourColorable_of_isEmpty)

end

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
