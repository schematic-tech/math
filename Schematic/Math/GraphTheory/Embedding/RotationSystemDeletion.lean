import Schematic.Math.GraphTheory.Embedding.RotationSystem
import Schematic.Math.GraphTheory.Embedding.WalkupPlanarity

/-!
Restriction of graph rotation systems under edge deletion.

The construction follows `embedding.v::subgraph_embedding` in the reference
Coq development. To remove the two darts of a graph edge, first apply
`WalkupF` to one orientation and then `WalkupE` to the opposite orientation.
For a plain graph hypermap, the first operation makes the opposite dart an
edge fixed point. The second operation therefore leaves the original edge
involution on every surviving dart.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace PermSkip

variable {α : Type u} {β : Type*} [DecidableEq α]

/-- Removing one point from a permutation preserves every quantity that the
original permutation preserves. -/
theorem skip_preserves
    (σ : Equiv.Perm α) (p : α → β)
    (hσ : ∀ x, p (σ x) = p x)
    {z : α} (x : DeletedPoint z) :
    p ((skip σ z x : DeletedPoint z) : α) = p x.1 := by
  rw [skip_apply_val]
  unfold skipAux
  split_ifs with hx
  · calc
      p (σ z) = p z := hσ z
      _ = p (σ x.1) := by rw [hx]
      _ = p x.1 := hσ x.1
  · exact hσ x.1

end PermSkip

namespace Hypermap

variable (G : Hypermap.{u})

@[simp]
theorem walkupF_edge_eq_skip (z : G.Dart) :
    (G.walkupF z).edge = PermSkip.skip G.edge z :=
  rfl

@[simp]
theorem walkupF_node_eq_skip (z : G.Dart) :
    (G.walkupF z).node = PermSkip.skip G.node z :=
  rfl

theorem walkupF_opposite_edge_fixed
    (hplain : G.Plain) (z : G.Dart) :
    (G.walkupF z).edge
        (⟨G.edge z, Plain.edge_ne (G := G) hplain z⟩ :
          (G.walkupF z).Dart) =
      (⟨G.edge z, Plain.edge_ne (G := G) hplain z⟩ :
        (G.walkupF z).Dart) := by
  apply Subtype.ext
  change PermSkip.skipAux G.edge z (G.edge z) = G.edge z
  simp [PermSkip.skipAux, Plain.edge_edge (G := G) hplain z]

theorem walkupF_walkupE_opposite_edge_apply_coe
    (hplain : G.Plain) (z : G.Dart)
    (w : ((G.walkupF z).walkupE
      (⟨G.edge z, Plain.edge_ne (G := G) hplain z⟩ :
        (G.walkupF z).Dart)).Dart) :
    ((((G.walkupF z).walkupE
        (⟨G.edge z, Plain.edge_ne (G := G) hplain z⟩ :
          (G.walkupF z).Dart)).edge w).1.1) =
      G.edge w.1.1 := by
  let u : (G.walkupF z).Dart :=
    ⟨G.edge z, Plain.edge_ne (G := G) hplain z⟩
  have hu : (G.walkupF z).edge u = u :=
    G.walkupF_opposite_edge_fixed hplain z
  have hxOpposite : w.1.1 ≠ G.edge z := by
    intro hx
    apply w.2
    apply Subtype.ext
    exact hx
  have hedgeNe : G.edge w.1.1 ≠ z := by
    intro hedge
    apply hxOpposite
    calc
      w.1.1 = G.edge (G.edge w.1.1) :=
        (Plain.edge_edge (G := G) hplain w.1.1).symm
      _ = G.edge z := by rw [hedge]
  calc
    ((((G.walkupF z).walkupE u).edge w).1.1) =
        ((G.walkupF z).edge w.1).1 := by
      rw [(G.walkupF z).walkupE_edge_eq_skip_edge_of_edge_eq hu]
      exact congrArg Subtype.val
        (PermSkip.skip_apply_of_fixed (G.walkupF z).edge hu w)
    _ = G.edge w.1.1 := by
      change
        ((PermSkip.skip G.edge z w.1 :
          G.DeletedDart z) : G.Dart) = G.edge w.1.1
      exact PermSkip.skip_apply_of_apply_ne G.edge w.1 hedgeNe

end Hypermap

namespace Hypermap.Iso

variable {G H : Hypermap.{u}}

/-- A dart equivalence commuting with edge and node automatically commutes
with face, by the hypermap cancellation law. -/
def ofEdgeNode
    (E : G.Dart ≃ H.Dart)
    (hEdge : ∀ x, E (G.edge x) = H.edge (E x))
    (hNode : ∀ x, E (G.node x) = H.node (E x)) :
    Hypermap.Iso G H where
  toEquiv := E
  map_edge := hEdge
  map_node := hNode
  map_face := by
    intro x
    apply H.node.injective
    calc
      H.node (E (G.face x)) = E (G.node (G.face x)) :=
        (hNode (G.face x)).symm
      _ = E (G.edge.symm x) := by rw [G.node_face_eq_edge_symm]
      _ = H.edge.symm (E x) :=
        perm_conj_symm_apply E G.edge H.edge hEdge x
      _ = H.node (H.face (E x)) := (H.node_face_eq_edge_symm (E x)).symm

end Hypermap.Iso

namespace EdgeDeletion

abbrev deletedGraph
    {V : Type u} (G : SimpleGraph V) (a b : V) : SimpleGraph V :=
  G.deleteEdges ({s(a, b)} : Set (Sym2 V))

def sourceDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (e : OrientedEdge (deletedGraph G a b)) :
    OrientedEdge G :=
  ⟨(e.tail, e.head),
    (SimpleGraph.deleteEdges_le ({s(a, b)} : Set (Sym2 V))) e.adj⟩

def oldDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (e : OrientedEdge G)
    (hnot : s(e.tail, e.head) ≠ s(a, b)) :
    OrientedEdge (deletedGraph G a b) := by
  refine ⟨(e.tail, e.head), ?_⟩
  rw [deletedGraph, SimpleGraph.deleteEdges_adj]
  exact ⟨e.adj, by simpa using hnot⟩

@[simp]
theorem sourceDart_oldDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (e : OrientedEdge G)
    (hnot : s(e.tail, e.head) ≠ s(a, b)) :
    sourceDart (G := G) (a := a) (b := b) (oldDart e hnot) = e := by
  apply Subtype.ext
  cases e with
  | mk e he =>
      cases e
      rfl

@[simp]
theorem oldDart_sourceDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (e : OrientedEdge (deletedGraph G a b))
    (hnot : s((sourceDart (G := G) (a := a) (b := b) e).tail,
        (sourceDart (G := G) (a := a) (b := b) e).head) ≠ s(a, b)) :
    oldDart (sourceDart (G := G) (a := a) (b := b) e) hnot = e := by
  apply Subtype.ext
  cases e with
  | mk e he =>
      cases e
      rfl

@[simp]
theorem oldDart_symm
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (e : OrientedEdge G)
    (hnot : s(e.tail, e.head) ≠ s(a, b))
    (hnot_symm : s(e.symm.tail, e.symm.head) ≠ s(a, b)) :
    (oldDart (G := G) (a := a) (b := b) e hnot).symm =
      oldDart (G := G) (a := a) (b := b) e.symm hnot_symm := by
  apply Subtype.ext
  cases e with
  | mk e he =>
      cases e
      rfl

def forwardDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    OrientedEdge G :=
  ⟨(a, b), hab⟩

def backwardDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    OrientedEdge G :=
  (forwardDart hab).symm

@[simp]
theorem forwardDart_tail
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    (forwardDart hab).tail = a :=
  rfl

@[simp]
theorem forwardDart_head
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    (forwardDart hab).head = b :=
  rfl

@[simp]
theorem backwardDart_tail
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    (backwardDart hab).tail = b :=
  rfl

@[simp]
theorem backwardDart_head
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    (backwardDart hab).head = a :=
  rfl

theorem backwardDart_ne_forwardDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    backwardDart hab ≠ forwardDart hab := by
  exact OrientedEdge.edgePerm_ne_self (forwardDart hab)

noncomputable def walkupFOppositeDart
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b) :
    ((R.toHypermap).walkupF (forwardDart hab)).Dart :=
  ⟨backwardDart hab, backwardDart_ne_forwardDart hab⟩

/-- The Coq `subgraph_embedding` edge-removal hypermap: remove one
orientation with `WalkupF`, then remove its opposite orientation with
`WalkupE`. -/
noncomputable def restrictedHypermap
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b) :
    Hypermap.{u} :=
  ((R.toHypermap).walkupF (forwardDart hab)).walkupE
    (walkupFOppositeDart R hab)

theorem walkupFOppositeDart_edge_fixed
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b) :
    ((R.toHypermap).walkupF (forwardDart hab)).edge
        (walkupFOppositeDart R hab) =
      walkupFOppositeDart R hab := by
  simpa [walkupFOppositeDart, backwardDart] using
    (R.toHypermap).walkupF_opposite_edge_fixed
      R.toHypermap_plain (forwardDart hab)

theorem sym2_ne_deleted_of_ne_darts
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {e : OrientedEdge G}
    (hforward : e ≠ forwardDart hab)
    (hbackward : e ≠ backwardDart hab) :
    s(e.tail, e.head) ≠ s(a, b) := by
  intro hs
  have hcases :
      (e.tail = a ∧ e.head = b) ∨
        (e.tail = b ∧ e.head = a) := by
    simpa [Sym2.eq_iff] using hs
  rcases hcases with h | h
  · apply hforward
    apply Subtype.ext
    exact Prod.ext h.1 h.2
  · apply hbackward
    apply Subtype.ext
    exact Prod.ext h.1 h.2

theorem deletedDart_sym2_ne
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (e : OrientedEdge (deletedGraph G a b)) :
    s(e.tail, e.head) ≠ s(a, b) := by
  have hdel :
      G.Adj e.tail e.head ∧
        s(e.tail, e.head) ∉ ({s(a, b)} : Set (Sym2 V)) := by
    simpa [deletedGraph, SimpleGraph.deleteEdges_adj] using e.adj
  intro heq
  exact hdel.2 (by simp [heq])

theorem sourceDart_ne_forwardDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    sourceDart e ≠ forwardDart hab := by
  intro heq
  apply deletedDart_sym2_ne e
  have hp := congrArg Subtype.val heq
  simpa [sourceDart, forwardDart, OrientedEdge.tail, OrientedEdge.head]
    using congrArg (fun p : V × V => s(p.1, p.2)) hp

theorem sourceDart_ne_backwardDart
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    sourceDart e ≠ backwardDart hab := by
  intro heq
  apply deletedDart_sym2_ne e
  have hp := congrArg Subtype.val heq
  simpa [sourceDart, backwardDart, forwardDart, OrientedEdge.symm,
    OrientedEdge.tail, OrientedEdge.head, Sym2.eq_swap]
    using congrArg (fun p : V × V => s(p.1, p.2)) hp

/-- The two surviving nested-deletion darts are exactly the oriented edges of
the graph with `ab` deleted. -/
noncomputable def restrictedDartEquiv
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b) :
    (restrictedHypermap R hab).Dart ≃
      OrientedEdge (deletedGraph G a b) where
  toFun w :=
    oldDart w.1.1
      (sym2_ne_deleted_of_ne_darts hab w.1.2 (by
        intro hbackward
        apply w.2
        apply Subtype.ext
        exact hbackward))
  invFun e :=
    ⟨⟨sourceDart e, sourceDart_ne_forwardDart hab e⟩, by
      intro hbackward
      exact sourceDart_ne_backwardDart hab e
        (congrArg Subtype.val hbackward)⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact sourceDart_oldDart w.1.1
      (sym2_ne_deleted_of_ne_darts hab w.1.2 (by
        intro hbackward
        apply w.2
        apply Subtype.ext
        exact hbackward))
  right_inv e := by
    apply Subtype.ext
    exact congrArg Subtype.val
      (oldDart_sourceDart e (deletedDart_sym2_ne e))

@[simp]
theorem restrictedDartEquiv_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (w : (restrictedHypermap R hab).Dart) :
    (restrictedDartEquiv R hab w).tail = w.1.1.tail :=
  rfl

@[simp]
theorem restrictedDartEquiv_symm_source
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    ((restrictedDartEquiv R hab).symm e).1.1 = sourceDart e :=
  rfl

theorem walkupF_node_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (z : OrientedEdge G)
    (x : ((R.toHypermap).walkupF z).Dart) :
    (((R.toHypermap).walkupF z).node x).1.tail = x.1.tail := by
  change
    (PermSkip.skip R.node z x).1.tail = x.1.tail
  exact PermSkip.skip_preserves R.node OrientedEdge.tail R.node_tail x

theorem restrictedHypermap_node_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (w : (restrictedHypermap R hab).Dart) :
    ((restrictedHypermap R hab).node w).1.1.tail = w.1.1.tail := by
  let H := (R.toHypermap).walkupF (forwardDart hab)
  change ((PermSkip.skip H.node (walkupFOppositeDart R hab) w).1.1).tail =
    w.1.1.tail
  exact
    PermSkip.skip_preserves H.node
      (fun x : H.Dart => x.1.tail)
      (walkupF_node_tail R (forwardDart hab)) w

noncomputable def restrictedNode
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b) :
    Equiv.Perm (OrientedEdge (deletedGraph G a b)) :=
  let E := restrictedDartEquiv R hab
  ((E.symm.trans (restrictedHypermap R hab).node).trans E)

theorem restrictedNode_conj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (w : (restrictedHypermap R hab).Dart) :
    restrictedDartEquiv R hab ((restrictedHypermap R hab).node w) =
      restrictedNode R hab (restrictedDartEquiv R hab w) := by
  simp [restrictedNode]

/-- Restrict a graph rotation system to the graph obtained by deleting one
edge. The node cycles are the original vertex rotations with the two removed
darts skipped. -/
noncomputable def restrictedRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b) :
    RotationSystem (deletedGraph G a b) where
  node := restrictedNode R hab
  node_tail := by
    intro e
    let E := restrictedDartEquiv R hab
    let w := E.symm e
    change (E ((restrictedHypermap R hab).node w)).tail = e.tail
    calc
      (E ((restrictedHypermap R hab).node w)).tail =
          ((restrictedHypermap R hab).node w).1.1.tail :=
        restrictedDartEquiv_tail R hab _
      _ = w.1.1.tail := restrictedHypermap_node_tail R hab w
      _ = e.tail := by
        change ((E.symm e).1.1).tail = e.tail
        rw [restrictedDartEquiv_symm_source]
        rfl
  node_orbit_of_same_tail := by
    intro e f hef
    let E := restrictedDartEquiv R hab
    let x := E.symm e
    let y := E.symm f
    let H₁ := (R.toHypermap).walkupF (forwardDart hab)
    have hxyTail : x.1.1.tail = y.1.1.tail := by
      change ((E.symm e).1.1).tail = ((E.symm f).1.1).tail
      rw [restrictedDartEquiv_symm_source,
        restrictedDartEquiv_symm_source]
      exact hef
    have h₀ : PermReachable R.node x.1.1 y.1.1 :=
      R.node_orbit_of_same_tail x.1.1 y.1.1 hxyTail
    have h₁ : PermReachable H₁.node x.1 y.1 := by
      change
        PermReachable (PermSkip.skip R.node (forwardDart hab))
          x.1 y.1
      exact PermSkip.skip_permReachable_of_permReachable R.node h₀
    have h₂ :
        PermReachable (restrictedHypermap R hab).node x y := by
      change
        PermReachable
          (PermSkip.skip H₁.node (walkupFOppositeDart R hab)) x y
      exact PermSkip.skip_permReachable_of_permReachable H₁.node h₁
    exact
      permReachable_conj E (restrictedHypermap R hab).node
        (restrictedNode R hab) (restrictedNode_conj R hab) h₂

theorem restrictedHypermap_edge_source
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (w : (restrictedHypermap R hab).Dart) :
    ((restrictedHypermap R hab).edge w).1.1 = w.1.1.symm := by
  simpa [restrictedHypermap, walkupFOppositeDart, backwardDart] using
    (R.toHypermap).walkupF_walkupE_opposite_edge_apply_coe
      R.toHypermap_plain (forwardDart hab) w

theorem restrictedDartEquiv_map_edge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (w : (restrictedHypermap R hab).Dart) :
    restrictedDartEquiv R hab ((restrictedHypermap R hab).edge w) =
      (restrictedDartEquiv R hab w).symm := by
  refine Subtype.ext ?_
  exact congrArg (fun e : OrientedEdge G => e.1)
    (restrictedHypermap_edge_source R hab w)

noncomputable def restrictedHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b) :
    Hypermap.Iso (restrictedHypermap R hab)
      ((restrictedRotationSystem R hab).toHypermap) :=
  Hypermap.Iso.ofEdgeNode (restrictedDartEquiv R hab)
    (by
      intro w
      exact restrictedDartEquiv_map_edge R hab w)
    (by
      intro w
      exact restrictedNode_conj R hab w)

theorem restrictedHypermap_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (hR : (R.toHypermap).EulerPlanar) :
    (restrictedHypermap R hab).EulerPlanar := by
  apply Unavoidability.walkupE_eulerPlanar_of_eulerPlanar
  exact
    Unavoidability.walkupF_eulerPlanar_of_eulerPlanar
      R.toHypermap (forwardDart hab) hR

theorem restrictedRotationSystem_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (hR : (R.toHypermap).EulerPlanar) :
    ((restrictedRotationSystem R hab).toHypermap).EulerPlanar :=
  (restrictedHypermapIso R hab).eulerPlanar_iff.mp
    (restrictedHypermap_eulerPlanar R hab hR)

theorem restrictedRotationSystem_dual_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (hR : (R.toHypermap).dual.EulerPlanar) :
    ((restrictedRotationSystem R hab).toHypermap).dual.EulerPlanar := by
  have hprimal : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
  have hrestricted :
      ((restrictedRotationSystem R hab).toHypermap).EulerPlanar :=
    restrictedRotationSystem_eulerPlanar R hab hprimal
  exact
    (Hypermap.dual_eulerPlanar_iff
      (G := (restrictedRotationSystem R hab).toHypermap)).mpr hrestricted

/-- A graph rotation system bundled with the Euler-planarity property used by
the graph/hypermap bridge. -/
structure PlanarRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  rotation : RotationSystem G
  dualEulerPlanar :
    ∃ d : DecidableRel G.Adj,
      letI : DecidableRel G.Adj := d
      (rotation.toHypermap).dual.EulerPlanar

namespace PlanarRotationSystem

noncomputable def cast
    {V : Type u} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V}
    (P : PlanarRotationSystem G) (h : G = H) :
    PlanarRotationSystem H := by
  subst H
  exact P

noncomputable def deleteEdge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (P : PlanarRotationSystem G) {a b : V} (hab : G.Adj a b) :
    PlanarRotationSystem (deletedGraph G a b) := by
  let dG : DecidableRel G.Adj :=
    Classical.choose P.dualEulerPlanar
  have hP :
      letI : DecidableRel G.Adj := dG
      (P.rotation.toHypermap).dual.EulerPlanar :=
    Classical.choose_spec P.dualEulerPlanar
  letI : DecidableRel G.Adj := dG
  let dDeleted : DecidableRel (deletedGraph G a b).Adj := inferInstance
  let RDeleted := restrictedRotationSystem P.rotation hab
  refine ⟨RDeleted, dDeleted, ?_⟩
  exact restrictedRotationSystem_dual_eulerPlanar
    P.rotation hab hP

theorem deleteEdges_insert_eq
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) (S : Finset (Sym2 V)) :
    (G.deleteEdges (↑(insert e S) : Set (Sym2 V))) =
      ((G.deleteEdges (↑S : Set (Sym2 V))).deleteEdges
        ({e} : Set (Sym2 V))) := by
  rw [SimpleGraph.deleteEdges_deleteEdges]
  congr 1
  ext x
  simp

theorem deleteFinset_nonempty
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (P : PlanarRotationSystem G) (S : Finset (Sym2 V)) :
    Nonempty (PlanarRotationSystem
      (G.deleteEdges (↑S : Set (Sym2 V)))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨by simpa [SimpleGraph.deleteEdges_empty] using P⟩
  | @insert e S he ih =>
      rcases ih with ⟨Q⟩
      induction e using Sym2.inductionOn with
      | _ a b =>
          by_cases habS :
              (G.deleteEdges (↑S : Set (Sym2 V))).Adj a b
          · exact ⟨(Q.deleteEdge habS).cast
              (deleteEdges_insert_eq G s(a, b) S).symm⟩
          · have hdelete :
                ((G.deleteEdges (↑S : Set (Sym2 V))).deleteEdges
                    ({s(a, b)} : Set (Sym2 V))) =
                  G.deleteEdges (↑S : Set (Sym2 V)) := by
              rw [SimpleGraph.deleteEdges_eq_self]
              refine Set.disjoint_singleton_right.mpr ?_
              intro hedge
              exact habS ((SimpleGraph.mem_edgeSet _).mp hedge)
            exact ⟨Q.cast
              ((deleteEdges_insert_eq G s(a, b) S).trans hdelete).symm⟩

noncomputable def deleteFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (P : PlanarRotationSystem G) (S : Finset (Sym2 V)) :
    PlanarRotationSystem
      (G.deleteEdges (↑S : Set (Sym2 V))) :=
  Classical.choice (deleteFinset_nonempty P S)

theorem deleteEdges_edgeFinset_sdiff_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) :
    G.deleteEdges
        (↑(G.edgeFinset \ H.edgeFinset) : Set (Sym2 V)) = H := by
  ext x y
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hG, hnot⟩
    by_contra hH
    apply hnot
    simp [hG, hH]
  · intro hH
    refine ⟨hHG hH, ?_⟩
    simp [hH]

/-- Every spanning subgraph of an Euler-planar graph rotation system inherits
an Euler-planar rotation system. This is the graph-rotation form of
`embedding.v::subgraph_embedding`. Isolated vertices require no separate
case because rotation-system darts only record graph edges. -/
noncomputable def mono
    {V : Type u} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (P : PlanarRotationSystem G) (hHG : H ≤ G) :
    PlanarRotationSystem H :=
  (P.deleteFinset (G.edgeFinset \ H.edgeFinset)).cast
    (deleteEdges_edgeFinset_sdiff_eq hHG)

end PlanarRotationSystem

end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
