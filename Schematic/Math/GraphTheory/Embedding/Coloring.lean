import Schematic.Math.GraphTheory.Embedding.Trace
import Schematic.Math.GraphTheory.Embedding.Geometry
import Schematic.Math.GraphTheory.Embedding.Hypermap
import Schematic.Math.GraphTheory.Embedding.Iso

/-!
Hypermap colourings.

This ports the first definitions and symmetry lemmas from Gonthier's
`coloring.v`: map colourings, graph colourings, and their behaviour under dual
and mirror hypermaps.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- A map colouring: adjacent faces across an edge have different colours, and
all darts in a face orbit have the same colour. -/
def Coloring (k : G.Dart → Color) : Prop :=
  (∀ x : G.Dart, k (G.edge x) ≠ k x) ∧
    (∀ x : G.Dart, k (G.face x) = k x)

/-- The hypermap has a four-colouring. -/
def FourColorable : Prop :=
  Exists fun k : G.Dart → Color => G.Coloring k

instance coloringDecidable
    (k : G.Dart → Color) :
    Decidable (G.Coloring k) := by
  unfold Coloring
  infer_instance

instance fourColorableDecidable :
    Decidable G.FourColorable := by
  unfold FourColorable
  infer_instance

/-- A graph colouring of the underlying map: edge-neighbours differ and node
orbits are monochromatic. -/
def GraphColoring (k : G.Dart → Color) : Prop :=
  (∀ x : G.Dart, k (G.edge x) ≠ k x) ∧
    (∀ x : G.Dart, k (G.node x) = k x)

/-- The underlying graph of the hypermap has a four-colouring. -/
def GraphFourColorable : Prop :=
  Exists fun k : G.Dart → Color => G.GraphColoring k

instance graphColoringDecidable
    (k : G.Dart → Color) :
    Decidable (G.GraphColoring k) := by
  unfold GraphColoring
  infer_instance

instance graphFourColorableDecidable :
    Decidable G.GraphFourColorable := by
  unfold GraphFourColorable
  infer_instance

theorem Coloring.edge_ne
    {k : G.Dart → Color}
    (hk : G.Coloring k)
    (x : G.Dart) :
    k (G.edge x) ≠ k x :=
  hk.1 x

theorem Coloring.ne_edge
    {k : G.Dart → Color}
    (hk : G.Coloring k)
    (x : G.Dart) :
    k x ≠ k (G.edge x) := by
  intro h
  exact Coloring.edge_ne (G := G) hk x h.symm

theorem Coloring.face_eq
    {k : G.Dart → Color}
    (hk : G.Coloring k)
    (x : G.Dart) :
    k (G.face x) = k x :=
  hk.2 x

theorem Coloring.eq_face
    {k : G.Dart → Color}
    (hk : G.Coloring k)
    (x : G.Dart) :
    k x = k (G.face x) :=
  (Coloring.face_eq (G := G) hk x).symm

theorem GraphColoring.edge_ne
    {k : G.Dart → Color}
    (hk : G.GraphColoring k)
    (x : G.Dart) :
    k (G.edge x) ≠ k x :=
  hk.1 x

theorem GraphColoring.ne_edge
    {k : G.Dart → Color}
    (hk : G.GraphColoring k)
    (x : G.Dart) :
    k x ≠ k (G.edge x) := by
  intro h
  exact GraphColoring.edge_ne (G := G) hk x h.symm

theorem GraphColoring.node_eq
    {k : G.Dart → Color}
    (hk : G.GraphColoring k)
    (x : G.Dart) :
    k (G.node x) = k x :=
  hk.2 x

theorem GraphColoring.eq_node
    {k : G.Dart → Color}
    (hk : G.GraphColoring k)
    (x : G.Dart) :
    k x = k (G.node x) :=
  (GraphColoring.node_eq (G := G) hk x).symm

theorem coloring_of_injective_color_map
    {k : G.Dart → Color}
    {f : Color → Color}
    (hf : Function.Injective f)
    (hk : G.Coloring k) :
    G.Coloring (f ∘ k) := by
  constructor
  · intro x hsame
    exact hk.1 x (hf hsame)
  · intro x
    exact congrArg f (hk.2 x)

theorem Coloring.perm
    {k : G.Dart → Color}
    (hk : G.Coloring k)
    (g : EdgePerm) :
    G.Coloring (g ∘ k) :=
  G.coloring_of_injective_color_map (EdgePerm.injective g) hk

theorem coloring_perm_iff
    (g : EdgePerm) (k : G.Dart → Color) :
    G.Coloring (g ∘ k) ↔ G.Coloring k := by
  constructor
  · intro hk
    have h := G.coloring_of_injective_color_map
      (EdgePerm.injective (EdgePerm.inv g)) hk
    convert h using 1
    funext x
    simp [Function.comp]
  · intro hk
    exact Coloring.perm (G := G) hk g

theorem graphColoring_of_injective_color_map
    {k : G.Dart → Color}
    {f : Color → Color}
    (hf : Function.Injective f)
    (hk : G.GraphColoring k) :
    G.GraphColoring (f ∘ k) := by
  constructor
  · intro x hsame
    exact hk.1 x (hf hsame)
  · intro x
    exact congrArg f (hk.2 x)

theorem GraphColoring.perm
    {k : G.Dart → Color}
    (hk : G.GraphColoring k)
    (g : EdgePerm) :
    G.GraphColoring (g ∘ k) :=
  G.graphColoring_of_injective_color_map (EdgePerm.injective g) hk

theorem graphColoring_perm_iff
    (g : EdgePerm) (k : G.Dart → Color) :
    G.GraphColoring (g ∘ k) ↔ G.GraphColoring k := by
  constructor
  · intro hk
    have h := G.graphColoring_of_injective_color_map
      (EdgePerm.injective (EdgePerm.inv g)) hk
    convert h using 1
    funext x
    simp [Function.comp]
  · intro hk
    exact GraphColoring.perm (G := G) hk g

theorem GraphColoring.eq_of_node_link
    {k : G.Dart → Color}
    (hk : G.GraphColoring k)
    {x y : G.Dart}
    (hxy : PermLink G.node x y) :
    k y = k x := by
  cases hxy with
  | forward => exact hk.2 x
  | backward =>
      have h := hk.2 (G.node.symm x)
      simpa using h.symm

theorem GraphColoring.eq_of_node_reachable
    {k : G.Dart → Color}
    (hk : G.GraphColoring k)
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    k y = k x :=
  (hxy.apply_eq k (fun {_ _} h =>
    (GraphColoring.eq_of_node_link (G := G) hk h).symm)).symm

theorem GraphColoring.loopless
    {k : G.Dart → Color}
    (hk : G.GraphColoring k) :
    G.Loopless := by
  intro x hnode
  exact hk.1 x (GraphColoring.eq_of_node_reachable (G := G) hk hnode)

theorem GraphColoring.dual_bridgeless
    {k : G.Dart → Color}
    (hk : G.GraphColoring k) :
    G.dual.Bridgeless :=
  (GraphColoring.loopless (G := G) hk).dual_bridgeless

theorem graphFourColorable_loopless
    (hG : G.GraphFourColorable) :
    G.Loopless := by
  rcases hG with ⟨k, hk⟩
  exact hk.loopless

theorem graphFourColorable_dual_bridgeless
    (hG : G.GraphFourColorable) :
    G.dual.Bridgeless := by
  rcases hG with ⟨k, hk⟩
  exact hk.dual_bridgeless

theorem Coloring.eq_of_face_link
    {k : G.Dart → Color}
    (hk : G.Coloring k)
    {x y : G.Dart}
    (hxy : PermLink G.face x y) :
    k y = k x := by
  cases hxy with
  | forward => exact hk.2 x
  | backward =>
      have h := hk.2 (G.face.symm x)
      simpa using h.symm

theorem Coloring.eq_of_face_reachable
    {k : G.Dart → Color}
    (hk : G.Coloring k)
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    k y = k x :=
  (hxy.apply_eq k (fun {_ _} h =>
    (Coloring.eq_of_face_link (G := G) hk h).symm)).symm

theorem Coloring.bridgeless
    {k : G.Dart → Color}
    (hk : G.Coloring k) :
    G.Bridgeless := by
  intro x hface
  exact hk.1 x (Coloring.eq_of_face_reachable (G := G) hk hface)

theorem Coloring.dual_loopless
    {k : G.Dart → Color}
    (hk : G.Coloring k) :
    G.dual.Loopless :=
  (Coloring.bridgeless (G := G) hk).dual_loopless

theorem fourColorable_bridgeless
    (hG : G.FourColorable) :
    G.Bridgeless := by
  rcases hG with ⟨k, hk⟩
  exact hk.bridgeless

theorem fourColorable_dual_loopless
    (hG : G.FourColorable) :
    G.dual.Loopless := by
  rcases hG with ⟨k, hk⟩
  exact hk.dual_loopless

theorem coloring_dual_iff
    (k : G.Dart → Color) :
    G.dual.Coloring k ↔ G.GraphColoring k := by
  constructor
  · intro hk
    constructor
    · intro x hsame
      have h := hk.1 (G.edge x)
      apply h
      convert hsame.symm using 1
      exact congrArg k (G.edge.symm_apply_apply x)
    · intro x
      have h := hk.2 (G.node x)
      convert h.symm using 1
      exact (congrArg k (G.node.symm_apply_apply x)).symm
  · intro hk
    constructor
    · intro x hsame
      have h := hk.1 (G.edge.symm x)
      apply h
      simpa [dual] using hsame.symm
    · intro x
      have h := hk.2 (G.node.symm x)
      simpa [dual] using h.symm

theorem fourColorable_dual_iff :
    G.dual.FourColorable ↔ G.GraphFourColorable := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (G.coloring_dual_iff k).mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (G.coloring_dual_iff k).mpr hk⟩

theorem graphFourColorable_dual_iff :
    G.dual.GraphFourColorable ↔ G.FourColorable := by
  constructor
  · intro hdual
    have hdd : G.dual.dual.FourColorable :=
      (G.dual.fourColorable_dual_iff).2 hdual
    simpa [FourColorable, Coloring, Hypermap.dual] using hdd
  · intro hcolor
    have hdd : G.dual.dual.FourColorable := by
      simpa [FourColorable, Coloring, Hypermap.dual] using hcolor
    exact (G.dual.fourColorable_dual_iff).1 hdd

theorem coloring_of_mirror_coloring
    {k : G.Dart → Color}
    (hk : G.mirror.Coloring k) :
    G.Coloring k := by
  have hface : ∀ x : G.Dart, k (G.face x) = k x := by
    intro x
    have h := hk.2 (G.face x)
    convert h.symm using 1
    exact (congrArg k (G.face.symm_apply_apply x)).symm
  constructor
  · intro x hsame
    have h := hk.1 (G.face (G.edge x))
    apply h
    calc
      k (G.mirror.edge (G.face (G.edge x))) = k (G.face x) := by
        change k (G.face (G.node (G.face (G.edge x)))) = k (G.face x)
        rw [G.node_face_edge x]
      _ = k x := hface x
      _ = k (G.edge x) := hsame.symm
      _ = k (G.face (G.edge x)) := (hface (G.edge x)).symm
  · exact hface

theorem coloring_mirror_of_coloring
    {k : G.Dart → Color}
    (hk : G.Coloring k) :
    G.mirror.Coloring k := by
  have hfaceSymm : ∀ x : G.Dart, k (G.face.symm x) = k x := by
    intro x
    simpa using (hk.2 (G.face.symm x)).symm
  constructor
  · intro x hsame
    have hmirror : k (G.face (G.node x)) = k x := by
      simpa [Hypermap.mirror] using hsame
    exact hk.1 (G.node x) (by
      calc
        k (G.edge (G.node x)) = k (G.face.symm x) := by
          rw [G.edge_node_eq_face_symm x]
        _ = k x := hfaceSymm x
        _ = k (G.face (G.node x)) := hmirror.symm
        _ = k (G.node x) := hk.2 (G.node x))
  · intro x
    change k (G.face.symm x) = k x
    exact hfaceSymm x

theorem coloring_mirror_iff
    (k : G.Dart → Color) :
    G.mirror.Coloring k ↔ G.Coloring k := by
  constructor
  · exact G.coloring_of_mirror_coloring
  · exact G.coloring_mirror_of_coloring

theorem fourColorable_of_mirror_fourColorable
    (hG : G.mirror.FourColorable) :
    G.FourColorable := by
  rcases hG with ⟨k, hk⟩
  exact ⟨k, G.coloring_of_mirror_coloring hk⟩

theorem fourColorable_mirror_of_fourColorable
    (hG : G.FourColorable) :
    G.mirror.FourColorable := by
  rcases hG with ⟨k, hk⟩
  exact ⟨k, G.coloring_mirror_of_coloring hk⟩

theorem fourColorable_mirror_iff :
    G.mirror.FourColorable ↔ G.FourColorable := by
  constructor
  · exact G.fourColorable_of_mirror_fourColorable
  · exact G.fourColorable_mirror_of_fourColorable

namespace Iso

universe u v

variable {G : Hypermap.{u}} {H : Hypermap.{v}} (φ : Iso G H)

theorem coloring_pull
    {k : H.Dart → Color}
    (hk : H.Coloring k) :
    G.Coloring (k ∘ φ.toEquiv) := by
  constructor
  · intro x hsame
    exact hk.1 (φ.toEquiv x) (by
      simpa [Function.comp, φ.map_edge x] using hsame)
  · intro x
    simpa [Function.comp, φ.map_face x] using hk.2 (φ.toEquiv x)

theorem coloring_comp_iff
    (k : H.Dart → Color) :
    G.Coloring (k ∘ φ.toEquiv) ↔ H.Coloring k := by
  constructor
  · intro hk
    have hpull := φ.symm.coloring_pull hk
    convert hpull using 1
    funext x
    simp [Function.comp, Iso.symm]
  · exact φ.coloring_pull

theorem graphColoring_pull
    {k : H.Dart → Color}
    (hk : H.GraphColoring k) :
    G.GraphColoring (k ∘ φ.toEquiv) := by
  constructor
  · intro x hsame
    exact hk.1 (φ.toEquiv x) (by
      simpa [Function.comp, φ.map_edge x] using hsame)
  · intro x
    simpa [Function.comp, φ.map_node x] using hk.2 (φ.toEquiv x)

theorem graphColoring_comp_iff
    (k : H.Dart → Color) :
    G.GraphColoring (k ∘ φ.toEquiv) ↔ H.GraphColoring k := by
  constructor
  · intro hk
    have hpull := φ.symm.graphColoring_pull hk
    convert hpull using 1
    funext x
    simp [Function.comp, Iso.symm]
  · exact φ.graphColoring_pull

theorem fourColorable_iff
    (φ : Iso G H) :
    G.FourColorable ↔ H.FourColorable := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k ∘ φ.toEquiv.symm, by
      have hpull := φ.symm.coloring_pull hk
      convert hpull using 1⟩
  · rintro ⟨k, hk⟩
    exact ⟨k ∘ φ.toEquiv, φ.coloring_pull hk⟩

theorem graphFourColorable_iff
    (φ : Iso G H) :
    G.GraphFourColorable ↔ H.GraphFourColorable := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k ∘ φ.toEquiv.symm, by
      have hpull := φ.symm.graphColoring_pull hk
      convert hpull using 1⟩
  · rintro ⟨k, hk⟩
    exact ⟨k ∘ φ.toEquiv, φ.graphColoring_pull hk⟩

end Iso

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
