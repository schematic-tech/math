import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.NoPivotInvariants
import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.PivotedInvariants

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace LeafExtension

theorem leafHypermap_eulerLeft_none
    (G : Hypermap.{u}) :
    (leafHypermap G none).eulerLeft = G.eulerLeft + 4 := by
  unfold Hypermap.eulerLeft
  rw [leafHypermap_componentCount_none, leafHypermap_card]
  omega

theorem leafHypermap_eulerRight_none
    (G : Hypermap.{u}) :
    (leafHypermap G none).eulerRight = G.eulerRight + 4 := by
  unfold Hypermap.eulerRight
  rw [leafHypermap_edgeOrbitCount, leafHypermap_nodeOrbitCount_none,
    leafHypermap_faceOrbitCount_none]
  omega

theorem leafHypermap_genus_none
    (G : Hypermap.{u}) :
    (leafHypermap G none).genus = G.genus := by
  unfold Hypermap.genus
  rw [leafHypermap_eulerLeft_none, leafHypermap_eulerRight_none,
    Nat.add_sub_add_right]

theorem leafHypermap_eulerLeft_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).eulerLeft = G.eulerLeft + 2 := by
  unfold Hypermap.eulerLeft
  rw [leafHypermap_componentCount_some, leafHypermap_card]
  omega

theorem leafHypermap_eulerRight_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).eulerRight = G.eulerRight + 2 := by
  unfold Hypermap.eulerRight
  rw [leafHypermap_edgeOrbitCount, leafHypermap_nodeOrbitCount_some,
    leafHypermap_faceOrbitCount_some]
  omega

theorem leafHypermap_genus_some
    (G : Hypermap.{u}) (p : G.Dart) :
    (leafHypermap G (some p)).genus = G.genus := by
  unfold Hypermap.genus
  rw [leafHypermap_eulerLeft_some, leafHypermap_eulerRight_some,
    Nat.add_sub_add_right]

theorem leafHypermap_genus
    (G : Hypermap.{u}) (pivot : Option G.Dart) :
    (leafHypermap G pivot).genus = G.genus := by
  cases pivot with
  | none => exact leafHypermap_genus_none G
  | some p => exact leafHypermap_genus_some G p

theorem leafHypermap_eulerPlanar_iff
    (G : Hypermap.{u}) (pivot : Option G.Dart) :
    (leafHypermap G pivot).EulerPlanar ↔ G.EulerPlanar := by
  simp [Hypermap.EulerPlanar, leafHypermap_genus G pivot]


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
