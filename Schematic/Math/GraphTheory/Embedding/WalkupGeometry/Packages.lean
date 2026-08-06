import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.EdgeAction

/-!
Final planar, bridgeless, plain, and precubic Walkup packages.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

theorem walkupE_planarBridgelessPlainPrecubic_of_parts
    (hG : G.Precubic) (z : G.Dart)
    (hplanar : (G.walkupE z).EulerPlanar)
    (hbridgeless : (G.walkupE z).Bridgeless)
    (hplain : (G.walkupE z).Plain) :
    (G.walkupE z).PlanarBridgelessPlainPrecubic where
  base := {
    base := {
      planar := hplanar
      bridgeless := hbridgeless }
    plain := hplain }
  precubic := G.walkupE_precubic hG z

theorem walkupE_walkupE_planarBridgelessPlainPrecubic_of_parts
    (hG : G.Precubic) {z : G.Dart} (u : (G.walkupE z).Dart)
    (hplanar : ((G.walkupE z).walkupE u).EulerPlanar)
    (hbridgeless : ((G.walkupE z).walkupE u).Bridgeless)
    (hplain : ((G.walkupE z).walkupE u).Plain) :
    ((G.walkupE z).walkupE u).PlanarBridgelessPlainPrecubic where
  base := {
    base := {
      planar := hplanar
      bridgeless := hbridgeless }
    plain := hplain }
  precubic := G.walkupE_walkupE_precubic hG u


end Hypermap
end FourColor
end Schematic.Math.GraphTheory

