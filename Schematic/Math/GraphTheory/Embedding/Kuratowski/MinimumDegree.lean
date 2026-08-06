import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

/-- A finite graph of positive cardinality and minimum degree at least three
contains an edge. -/
theorem exists_adj_of_card_pos_min_degree_three
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : 0 < Fintype.card V)
    (hmin : forall v : V, 3 <= G.degree v) :
    Exists fun a : V => Exists fun b : V => G.Adj a b := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp hcard
  let a : V := Classical.choice (inferInstance : Nonempty V)
  have hpos : 0 < G.degree a := by
    have ha := hmin a
    omega
  rcases (G.degree_pos_iff_exists_adj a).mp hpos with ⟨b, hab⟩
  exact ⟨a, b, hab⟩

end FourColor

end Schematic.Math.GraphTheory
