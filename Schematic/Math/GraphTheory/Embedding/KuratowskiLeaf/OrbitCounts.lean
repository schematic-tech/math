import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.HypermapConstruction

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace LeafExtension

@[simp]
theorem leafHypermap_card
    (G : Hypermap.{u}) (pivot : Option G.Dart) :
    Fintype.card (leafHypermap G pivot).Dart =
      Fintype.card G.Dart + 2 :=
  ExtDart.card

def leafHypermapEdgeOrbitCode
    (G : Hypermap.{u}) (pivot : Option G.Dart) :
    (leafHypermap G pivot).Dart -> Option G.EdgeOrbit :=
  ExtDart.code none none (fun x => some (PermOrbit.of G.edge x))

theorem leafHypermapEdgeOrbitCode_of_link
    (G : Hypermap.{u}) (pivot : Option G.Dart)
    {x y : (leafHypermap G pivot).Dart}
    (hxy : PermLink (leafHypermap G pivot).edge x y) :
    leafHypermapEdgeOrbitCode G pivot x =
      leafHypermapEdgeOrbitCode G pivot y := by
  cases hxy with
  | forward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          simp [leafHypermapEdgeOrbitCode]
          exact (PermOrbit.of_apply G.edge x).symm
  | backward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          rw [leafHypermap_edge_symm_old]
          simp [leafHypermapEdgeOrbitCode]
          exact (PermOrbit.of_symm_apply G.edge x).symm

theorem leafHypermapEdgeOrbitCode_of_reachable
    (G : Hypermap.{u}) (pivot : Option G.Dart)
    {x y : (leafHypermap G pivot).Dart}
    (hxy : PermReachable (leafHypermap G pivot).edge x y) :
    leafHypermapEdgeOrbitCode G pivot x =
      leafHypermapEdgeOrbitCode G pivot y :=
  code_eq_of_reflTransGen (leafHypermapEdgeOrbitCode G pivot)
    (leafHypermapEdgeOrbitCode_of_link G pivot) hxy

noncomputable def leafHypermapEdgeOrbitEquiv
    (G : Hypermap.{u}) (pivot : Option G.Dart) :
    (leafHypermap G pivot).EdgeOrbit ≃ Option G.EdgeOrbit where
  toFun :=
    Quotient.lift
      (leafHypermapEdgeOrbitCode G pivot)
      (by
        intro x y hxy
        exact leafHypermapEdgeOrbitCode_of_reachable G pivot hxy)
  invFun
    | none => PermOrbit.of (leafHypermap G pivot).edge ExtDart.new
    | some q =>
        Quotient.lift
          (fun x => PermOrbit.of (leafHypermap G pivot).edge (ExtDart.old x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (leafHypermap G pivot).edge
              (hxy.lift' ExtDart.old fun x _ hlink => by
                cases hlink with
                | forward =>
                    simpa using
                      (PermReachable.forward (leafHypermap G pivot).edge
                        (ExtDart.old x))
                | backward =>
                    simpa using
                      (PermReachable.backward (leafHypermap G pivot).edge
                        (ExtDart.old x))))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new => rfl
        | newEdge =>
            apply PermOrbit.of_eq_of
            exact PermReachable.forward (leafHypermap G pivot).edge ExtDart.new
        | old x => rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q =>
        induction q using Quotient.inductionOn with
        | h x => rfl

theorem leafHypermap_edgeOrbitCount
    (G : Hypermap.{u}) (pivot : Option G.Dart) :
    (leafHypermap G pivot).edgeOrbitCount = G.edgeOrbitCount + 1 := by
  unfold Hypermap.edgeOrbitCount Hypermap.EdgeOrbit
  rw [Nat.card_congr (leafHypermapEdgeOrbitEquiv G pivot)]
  haveI : Finite G.EdgeOrbit :=
    Quotient.finite (permOrbitSetoid G.edge)
  exact Finite.card_option

theorem leafHypermap_nodeOrbitCount_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).nodeOrbitCount = G.nodeOrbitCount + 1 := by
  unfold Hypermap.nodeOrbitCount Hypermap.NodeOrbit leafHypermap
  change Nat.card (PermOrbit (insertedLeafNode G.node (some p))) =
    Nat.card (PermOrbit G.node) + 1
  rw [Nat.card_congr (insertedLeafNodeSomeOrbitEquiv G.node p)]
  haveI : Finite (PermOrbit G.node) :=
    Quotient.finite (permOrbitSetoid G.node)
  exact Finite.card_option

theorem leafHypermap_nodeOrbitCount_none
    (G : Hypermap.{u}) :
    (leafHypermap G none).nodeOrbitCount = G.nodeOrbitCount + 2 := by
  unfold Hypermap.nodeOrbitCount Hypermap.NodeOrbit leafHypermap
  change Nat.card (PermOrbit (insertedLeafNode G.node none)) =
    Nat.card (PermOrbit G.node) + 2
  rw [Nat.card_congr (insertedLeafNodeNoneOrbitEquiv G.node)]
  haveI : Finite (PermOrbit G.node) :=
    Quotient.finite (permOrbitSetoid G.node)
  simp


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
