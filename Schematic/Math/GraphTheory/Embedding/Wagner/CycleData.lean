import Schematic.Math.GraphTheory.PathsTrees

/-! Path uniqueness and the data of an alternating cycle split. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner

/-- A simple-cycle split displaying the cyclic order
`x1, y1, x2, y2`.  The path from `x1` to `x2` is the arc containing `y2`;
the other two paths split the complementary arc at `y1`.

This is the explicit-path replacement for MathComp's
`subcycle [:: x1; y1; x2; y2] s` used in `wagner_no_cross`. -/
structure AlternatingCycleSplit
    {V : Type u} {G : SimpleGraph V}
    {r x1 y1 x2 y2 : V}
    (C : G.Walk r r) where
  pX1X2 : G.Walk x1 x2
  pX1Y1 : G.Walk x1 y1
  pX2Y1 : G.Walk x2 y1
  pX1X2_isPath : pX1X2.IsPath
  pX1Y1_isPath : pX1Y1.IsPath
  pX2Y1_isPath : pX2Y1.IsPath
  pX1X2_support : forall z, z ∈ pX1X2.support -> z ∈ C.support
  pX1Y1_support : forall z, z ∈ pX1Y1.support -> z ∈ C.support
  pX2Y1_support : forall z, z ∈ pX2Y1.support -> z ∈ C.support
  y1_not_pX1X2 : y1 ∉ pX1X2.support
  x2_not_pX1Y1 : x2 ∉ pX1Y1.support
  x1_not_pX2Y1 : x1 ∉ pX2Y1.support
  disjoint_X_X1Y1 :
    Disjoint (Walk.InternalVertices pX1X2) (Walk.InternalVertices pX1Y1)
  disjoint_X_X2Y1 :
    Disjoint (Walk.InternalVertices pX1X2) (Walk.InternalVertices pX2Y1)
  disjoint_X1Y1_X2Y1 :
    Disjoint (Walk.InternalVertices pX1Y1) (Walk.InternalVertices pX2Y1)
  y2_internal : y2 ∈ Walk.InternalVertices pX1X2

/-- Two simple paths with the same endpoints are equal when both use only
edges of a common simple path beginning at their common start. -/
theorem Walk.IsPath.eq_of_edges_subset_of_common_path
    {V : Type u}
    {G : SimpleGraph V} {x y : V}
    {z : V} {t : G.Walk x z} {p q : G.Walk x y}
    (ht : t.IsPath) (hp : p.IsPath) (hq : q.IsPath)
    (hpt : forall e, e ∈ p.edges -> e ∈ t.edges)
    (hqt : forall e, e ∈ q.edges -> e ∈ t.edges) :
    q = p := by
  classical
  induction t with
  | nil =>
      cases p with
      | nil =>
          exact (SimpleGraph.Walk.isPath_iff_eq_nil q).mp hq
      | @cons _ w _ hxw p =>
          have hne : (SimpleGraph.Walk.cons hxw p).edges ≠ [] := by simp
          let e := (SimpleGraph.Walk.cons hxw p).edges.head hne
          have hfalse : e ∈ (SimpleGraph.Walk.nil : G.Walk z z).edges :=
            hpt e (List.head_mem hne)
          simp at hfalse
  | @cons x w z hxw t ih =>
      cases p with
      | nil =>
          exact (SimpleGraph.Walk.isPath_iff_eq_nil q).mp hq
      | @cons _ a _ hxa p =>
          cases q with
          | nil =>
              have hnil :=
                (SimpleGraph.Walk.isPath_iff_eq_nil
                  (SimpleGraph.Walk.cons hxa p)).mp hp
              simp at hnil
          | @cons _ b _ hxb q =>
            have hpa : s(x, a) ∈ (SimpleGraph.Walk.cons hxw t).edges :=
              hpt _ (by simp)
            have hqb : s(x, b) ∈ (SimpleGraph.Walk.cons hxw t).edges :=
              hqt _ (by simp)
            have haw : a = w := by
              simpa using ht.eq_snd_of_mem_edges hpa
            have hbw : b = w := by
              simpa using ht.eq_snd_of_mem_edges hqb
            subst a
            subst b
            have htParts :=
              (SimpleGraph.Walk.cons_isPath_iff hxw t).mp ht
            have hpParts :=
              (SimpleGraph.Walk.cons_isPath_iff hxa p).mp hp
            have hqParts :=
              (SimpleGraph.Walk.cons_isPath_iff hxb q).mp hq
            have hpFirstNot : s(x, w) ∉ p.edges :=
              (SimpleGraph.Walk.isTrail_cons hxa p).mp hp.isTrail |>.2
            have hqFirstNot : s(x, w) ∉ q.edges :=
              (SimpleGraph.Walk.isTrail_cons hxb q).mp hq.isTrail |>.2
            have hpTail : forall e, e ∈ p.edges -> e ∈ t.edges := by
              intro e he
              have heFull : e ∈ (SimpleGraph.Walk.cons hxw t).edges :=
                hpt e (by simp [he])
              rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at heFull
              rcases heFull with heFirst | heTail
              · exact False.elim (hpFirstNot (by simpa [heFirst] using he))
              · exact heTail
            have hqTail : forall e, e ∈ q.edges -> e ∈ t.edges := by
              intro e he
              have heFull : e ∈ (SimpleGraph.Walk.cons hxw t).edges :=
                hqt e (by simp [he])
              rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at heFull
              rcases heFull with heFirst | heTail
              · exact False.elim (hqFirstNot (by simpa [heFirst] using he))
              · exact heTail
            have htailEq : q = p :=
              ih htParts.1 hpParts.1 hqParts.1 hpTail hqTail
            subst q
            rfl

end Wagner

end FourColor

end Schematic.Math.GraphTheory
