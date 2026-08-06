import Schematic.Math.GraphTheory.PathsTrees

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

/-- Membership transport through a reversed walk mapped to a supergraph.

`Walk.mapLe` is an abbreviation whose support theorem deliberately uses a
restricted transparency setting, so spelling this transport once avoids
fragile simplifier matching at reversed-prefix call sites. -/
theorem Walk.mem_support_of_mem_reverse_mapLe
    {G H : SimpleGraph V} (h : G <= H) {u v z : V}
    (p : G.Walk u v)
    (hz : z ∈ (p.reverse.mapLe h).support) :
    z ∈ p.support := by
  have hzReverse : z ∈ p.reverse.support :=
    Eq.mp
      (congrArg (fun l : List V => z ∈ l)
        (SimpleGraph.Walk.support_mapLe_eq_support h p.reverse)) hz
  have hzListReverse : z ∈ p.support.reverse :=
    Eq.mp
      (congrArg (fun l : List V => z ∈ l)
        (SimpleGraph.Walk.support_reverse p)) hzReverse
  exact List.mem_reverse.mp hzListReverse

end Schematic.Math.GraphTheory
