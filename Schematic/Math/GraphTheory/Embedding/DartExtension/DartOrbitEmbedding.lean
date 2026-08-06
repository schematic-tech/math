import Schematic.Math.GraphTheory.Embedding.DartExtension.N.FaceOrbits
import Schematic.Math.GraphTheory.Embedding.DartExtension.U.FaceOrbits

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap


/-- A dart map that exactly preserves face and edge permutation orbits. -/
structure DartOrbitEmbedding (G H : Hypermap) where
  toFun : G.Dart → H.Dart
  faceReachable_iff : ∀ {x y},
    PermReachable H.face (toFun x) (toFun y) ↔ PermReachable G.face x y
  edgeReachable_iff : ∀ {x y},
    PermReachable H.edge (toFun x) (toFun y) ↔ PermReachable G.edge x y

namespace DartOrbitEmbedding

variable {G H K : Hypermap}

/-- Compose exact dart-orbit embeddings. -/
def trans (f : DartOrbitEmbedding G H) (g : DartOrbitEmbedding H K) :
    DartOrbitEmbedding G K where
  toFun := g.toFun ∘ f.toFun
  faceReachable_iff := g.faceReachable_iff.trans f.faceReachable_iff
  edgeReachable_iff := g.edgeReachable_iff.trans f.edgeReachable_iff

theorem generatedReachable_of_faceReachable
    (f : DartOrbitEmbedding G H) {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    H.Reachable (f.toFun x) (f.toFun y) :=
  H.facePermReachable_reachable (f.faceReachable_iff.2 hxy)

theorem generatedReachable_of_edgeReachable
    (f : DartOrbitEmbedding G H) {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    H.Reachable (f.toFun x) (f.toFun y) :=
  H.edgePermReachable_reachable (f.edgeReachable_iff.2 hxy)

end DartOrbitEmbedding

variable (G : Hypermap) (x0 : G.Dart)

/-- The old darts embed exactly into the face and edge orbits of `ecpU`. -/
def extensionUOrbitEmbedding : DartOrbitEmbedding G (extensionU G x0) where
  toFun := ExtDart.old
  faceReachable_iff := extensionU_old_faceReachable_iff (G := G) x0
  edgeReachable_iff := extensionU_old_edgeReachable_iff (G := G) x0

/-- The old darts embed exactly into the face and edge orbits of `ecpN`. -/
def extensionNOrbitEmbedding : DartOrbitEmbedding G (extensionN G x0) where
  toFun := ExtDart.old
  faceReachable_iff := extensionN_old_faceReachable_iff (G := G) x0
  edgeReachable_iff := extensionN_old_edgeReachable_iff (G := G) x0

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
