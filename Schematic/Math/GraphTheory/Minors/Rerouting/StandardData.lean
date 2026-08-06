import Schematic.Math.GraphTheory.Minors.Rerouting.Extensions

/-! Standard rerouting data for a minimal YZ path. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

structure StandardReroutingData
    (A : Set V)
    (x y z : V)
    (h_setup : Prop) where
  setup : h_setup
  reroutedPath : G.Walk y z
  reroutedPath_isPath : reroutedPath.IsPath
  avoids_forbidden_vertices :
    forall v : V, v ∈ reroutedPath.support -> v ∉ A ∨ v = y ∨ v = z

def StandardReroutingForMinimalYZPath
    (A : Set V)
    (x y z : V)
    (h_setup : Prop) : Prop :=
  Nonempty (StandardReroutingData (G := G) A x y z h_setup)

end Schematic.Math.GraphTheory
