import Schematic.Math.GraphTheory.Contractions.EdgeCollapse
import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Rotation.SmallGraphs

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace GraphContraction

/-- If `v` is a leaf with neighbour `w`, then the edge contraction `G/vw` is
isomorphic to deleting `v`.  This is the quotient identification used in the
low-degree branch of the source induction. -/
noncomputable def collapseEdgeDeleteLeftIso_of_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1) :
    G.induce {z : V | z ≠ v} ≃g
      (GraphContraction.collapseEdge G hvw).graph where
  toEquiv :=
    Equiv.ofBijective
      (GraphContraction.collapseEdgeDeleteLeftHom G hvw)
      ⟨GraphContraction.collapseEdgeDeleteLeftHom_injective G hvw, by
        intro y
        change
          Option
            {z : V //
              z ∉ ((⊤ : G.Subgraph).induce ({v, w} : Set V)).verts} at y
        cases y with
        | none =>
            refine ⟨⟨w, hvw.ne'⟩, ?_⟩
            change (GraphContraction.collapseEdge G hvw).map w =
              (none : (GraphContraction.collapseEdge G hvw).Target)
            simp [GraphContraction.collapseEdge, GraphContraction.ofMap,
              GraphContraction.collapseSubgraph]
        | some z =>
            have hz_not_pair : (z : V) ∉ ({v, w} : Set V) := by
              simpa using z.2
            refine ⟨⟨z, ?_⟩, ?_⟩
            · intro hzv
              exact hz_not_pair (by simp [hzv])
            · change (GraphContraction.collapseEdge G hvw).map (z : V) =
                (some z : (GraphContraction.collapseEdge G hvw).Target)
              simp [GraphContraction.collapseEdge, GraphContraction.ofMap,
                GraphContraction.collapseSubgraph, hz_not_pair]⟩
  map_rel_iff' := by
    intro x y
    constructor
    · intro hxy
      let C := GraphContraction.collapseEdge G hvw
      change (G.induce {z : V | z ≠ v}).Adj x y
      rcases C.edge_lift hxy with ⟨a, b, ha, hb, hab⟩
      have hneq : C.map (x : V) ≠ C.map (y : V) := hxy.1
      have ha_eq_x : a = (x : V) := by
        rcases
            (GraphContraction.collapseEdge_map_eq_iff
              (G := G) hvw (v := a) (w := (x : V))).mp ha with
          hpair | hout
        · have hxw : (x : V) = w := by
            rcases hpair.2 with hxv | hxw
            · exact False.elim (x.2 hxv)
            · exact hxw
          rcases hpair.1 with hav | haw
          · have hb_eq_w : b = w :=
              neighbor_eq_of_degree_le_one_of_adj
                (G := G) hdegree hvw (by simpa [hav] using hab)
            have hy_pair : (y : V) ∈ ({v, w} : Set V) := by
              rcases
                  (GraphContraction.collapseEdge_map_eq_iff
                    (G := G) hvw (v := b) (w := (y : V))).mp hb with
                hpair_b | hout_b
              · exact hpair_b.2
              · have hb_not_pair : b ∉ ({v, w} : Set V) := hout_b.2.1
                exact False.elim (hb_not_pair (by simp [hb_eq_w]))
            have hyw : (y : V) = w := by
              rcases hy_pair with hyv | hyw
              · exact False.elim (y.2 hyv)
              · exact hyw
            exact False.elim (hneq (by simp [C, hxw, hyw]))
          · have haw' : a = w := by simpa using haw
            exact haw'.trans hxw.symm
        · exact hout.1
      have hb_eq_y : b = (y : V) := by
        rcases
            (GraphContraction.collapseEdge_map_eq_iff
              (G := G) hvw (v := b) (w := (y : V))).mp hb with
          hpair | hout
        · have hyw : (y : V) = w := by
            rcases hpair.2 with hyv | hyw
            · exact False.elim (y.2 hyv)
            · exact hyw
          rcases hpair.1 with hbv | hbw
          · have ha_eq_w : a = w :=
              neighbor_eq_of_degree_le_one_of_adj
                (G := G) hdegree hvw (by simpa [hbv] using hab.symm)
            have hx_pair : (x : V) ∈ ({v, w} : Set V) := by
              rcases
                  (GraphContraction.collapseEdge_map_eq_iff
                    (G := G) hvw (v := a) (w := (x : V))).mp ha with
                hpair_a | hout_a
              · exact hpair_a.2
              · have ha_not_pair : a ∉ ({v, w} : Set V) := hout_a.2.1
                exact False.elim (ha_not_pair (by simp [ha_eq_w]))
            have hxw : (x : V) = w := by
              rcases hx_pair with hxv | hxw
              · exact False.elim (x.2 hxv)
              · exact hxw
            exact False.elim (hneq (by simp [C, hxw, hyw]))
          · have hbw' : b = w := by simpa using hbw
            exact hbw'.trans hyw.symm
        · exact hout.1
      change G.Adj (x : V) (y : V)
      simpa [ha_eq_x, hb_eq_y] using hab
    · intro hxy
      change (GraphContraction.collapseEdge G hvw).graph.Adj
        ((GraphContraction.collapseEdgeDeleteLeftHom G hvw) x)
        ((GraphContraction.collapseEdgeDeleteLeftHom G hvw) y)
      exact (GraphContraction.collapseEdgeDeleteLeftHom G hvw).map_rel' hxy

end GraphContraction

end FourColor

end Schematic.Math.GraphTheory
