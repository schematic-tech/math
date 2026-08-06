import Schematic.Math.GraphTheory.PathsTrees.Operations.MappedPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
theorem Subgraph.exists_left_first_common_split
    [DecidableEq V]
    {T : G.Subgraph}
    {left right one : V}
    {p : G.Walk left right}
    {q : G.Walk left one}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hright_not_q : right ∉ q.support)
    (hleft :
      Exists fun zT : T.verts =>
        (zT : V) ∈ Walk.InternalVertices p ∧
          (zT : V) ∈ q.support ∧
            (zT : V) ≠ left) :
    Exists fun zT : T.verts =>
      Exists fun pBridge : G.Walk (zT : V) right =>
      Exists fun pLeft : G.Walk (zT : V) left =>
      Exists fun pOne : G.Walk (zT : V) one =>
        pBridge.IsPath ∧ pLeft.IsPath ∧ pOne.IsPath ∧
          pBridge.toSubgraph ≤ T ∧ pLeft.toSubgraph ≤ T ∧
            pOne.toSubgraph ≤ T ∧
              (zT : V) ∈ q.support ∧
                (zT : V) ∈ Walk.InternalVertices p ∧
                  (forall {x : V}, x ∈ pBridge.support -> x ∈ p.support) ∧
                    (forall {x : V}, x ∈ pLeft.support -> x ∈ q.support) ∧
                      (forall {x : V}, x ∈ pOne.support -> x ∈ q.support) ∧
                        right ∉ pLeft.support ∧
                          right ∉ pOne.support ∧
                            Disjoint
                              (Walk.InternalVertices pBridge)
                              {x : V | x ∈ pLeft.support ∧ x ≠ (zT : V)} ∧
                            Disjoint
                              (Walk.InternalVertices pBridge)
                              {x : V | x ∈ pOne.support ∧ x ≠ (zT : V)} ∧
                              Disjoint
                                {x : V | x ∈ pLeft.support ∧ x ≠ (zT : V)}
                                {x : V | x ∈ pOne.support ∧ x ≠ (zT : V)} := by
  classical
  rcases hleft with ⟨zT₀, hz_internal₀, hz_q₀, _hz_ne_left₀⟩
  have hz_p_rev₀ : (zT₀ : V) ∈ p.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hz_internal₀.1
  rcases Walk.exists_first_common_support p.reverse q
      ⟨(zT₀ : V), hz_p_rev₀, hz_q₀⟩ with
    ⟨z, hz_p_rev, hz_q, hfirst⟩
  have hz_p : z ∈ p.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hz_p_rev
  have hz_ne_left : z ≠ left := by
    intro hz_eq_left
    have hz₀_prefix :
        (zT₀ : V) ∈ (p.reverse.takeUntil z hz_p_rev).support := by
      rcases Walk.mem_support_takeUntil_or_dropUntil_of_mem_support
          p.reverse hz_p_rev hz_p_rev₀ with hz_take | hz_drop
      · exact hz_take
      · subst z
        have hdrop_path :
            (p.reverse.dropUntil left hz_p_rev).IsPath :=
          hp.reverse.dropUntil hz_p_rev
        have hdrop_nil :
            p.reverse.dropUntil left hz_p_rev = SimpleGraph.Walk.nil :=
          (SimpleGraph.Walk.isPath_iff_eq_nil
            (p.reverse.dropUntil left hz_p_rev)).mp hdrop_path
        have hz₀_eq_left : (zT₀ : V) = left := by
          have hz_nil :
              (zT₀ : V) ∈
                (SimpleGraph.Walk.nil : G.Walk left left).support := by
            simpa [hdrop_nil] using hz_drop
          exact SimpleGraph.Walk.mem_support_nil_iff.mp hz_nil
        exact False.elim (hz_internal₀.2.1 hz₀_eq_left)
    have hz₀_eq_left : (zT₀ : V) = z :=
      hfirst (zT₀ : V) hz_q₀ hz₀_prefix
    exact hz_internal₀.2.1 (hz₀_eq_left.trans hz_eq_left)
  have hz_ne_right : z ≠ right := by
    intro hz_eq_right
    exact hright_not_q (by simpa [hz_eq_right] using hz_q)
  have hzT_mem : z ∈ T.verts := by
    exact hp_le.left (by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact hz_p)
  let zT : T.verts := ⟨z, hzT_mem⟩
  have hz_internal : (zT : V) ∈ Walk.InternalVertices p := by
    exact ⟨by simpa [zT] using hz_p,
      by simpa [zT] using hz_ne_left,
      by simpa [zT] using hz_ne_right⟩
  let pBridge : G.Walk (zT : V) right :=
    (p.reverse.takeUntil z hz_p_rev).reverse
  let pLeft : G.Walk (zT : V) left :=
    (q.takeUntil z hz_q).reverse
  let pOne : G.Walk (zT : V) one :=
    q.dropUntil z hz_q
  have hpBridge : pBridge.IsPath := by
    simpa [pBridge] using (hp.reverse.takeUntil hz_p_rev).reverse
  have hpLeft : pLeft.IsPath := by
    simpa [pLeft] using (hq.takeUntil hz_q).reverse
  have hpOne : pOne.IsPath := by
    simpa [pOne] using hq.dropUntil hz_q
  have hpBridge_le : pBridge.toSubgraph ≤ T := by
    simpa [pBridge, SimpleGraph.Walk.toSubgraph_reverse] using
      (le_trans (Walk.toSubgraph_takeUntil_le p.reverse hz_p_rev)
        (by simpa [SimpleGraph.Walk.toSubgraph_reverse] using hp_le))
  have hpLeft_le : pLeft.toSubgraph ≤ T := by
    simpa [pLeft, SimpleGraph.Walk.toSubgraph_reverse] using
      (le_trans (Walk.toSubgraph_takeUntil_le q hz_q) hq_le)
  have hpOne_le : pOne.toSubgraph ≤ T := by
    simpa [pOne] using
      (le_trans (Walk.toSubgraph_dropUntil_le q hz_q) hq_le)
  have hbridge_support_p :
      forall {x : V}, x ∈ pBridge.support -> x ∈ p.support := by
    intro x hx
    have hx_rev :
        x ∈ (p.reverse.takeUntil z hz_p_rev).reverse.support := by
      simpa [pBridge] using hx
    have hx_prefix :
        x ∈ (p.reverse.takeUntil z hz_p_rev).support := by
      simpa [SimpleGraph.Walk.support_reverse] using hx_rev
    have hx_p_rev : x ∈ p.reverse.support :=
      SimpleGraph.Walk.support_takeUntil_subset p.reverse hz_p_rev hx_prefix
    simpa [SimpleGraph.Walk.support_reverse] using hx_p_rev
  have hleft_support_q :
      forall {x : V}, x ∈ pLeft.support -> x ∈ q.support := by
    intro x hx
    have hx_rev : x ∈ (q.takeUntil z hz_q).reverse.support := by
      simpa [pLeft] using hx
    have hx_prefix : x ∈ (q.takeUntil z hz_q).support := by
      simpa [SimpleGraph.Walk.support_reverse] using hx_rev
    exact SimpleGraph.Walk.support_takeUntil_subset q hz_q hx_prefix
  have hone_support_q :
      forall {x : V}, x ∈ pOne.support -> x ∈ q.support := by
    intro x hx
    exact SimpleGraph.Walk.support_dropUntil_subset q hz_q
      (by simpa [pOne] using hx)
  have hright_not_pLeft : right ∉ pLeft.support := by
    intro hright
    exact hright_not_q (hleft_support_q hright)
  have hright_not_pOne : right ∉ pOne.support := by
    intro hright
    exact hright_not_q (hone_support_q hright)
  have hbridge_left_disjoint :
      Disjoint
        (Walk.InternalVertices pBridge)
        {x : V | x ∈ pLeft.support ∧ x ≠ (zT : V)} := by
    rw [Set.disjoint_left]
    intro x hx_bridge hx_left
    have hx_prefix :
        x ∈ (p.reverse.takeUntil z hz_p_rev).support := by
      have hx_rev :
          x ∈ (p.reverse.takeUntil z hz_p_rev).reverse.support := by
        simpa [pBridge] using hx_bridge.1
      simpa [SimpleGraph.Walk.support_reverse] using hx_rev
    have hx_q : x ∈ q.support :=
      hleft_support_q hx_left.1
    have hx_eq : x = z := hfirst x hx_q hx_prefix
    exact hx_bridge.2.1 (by simpa [zT] using hx_eq)
  have hbridge_one_disjoint :
      Disjoint
        (Walk.InternalVertices pBridge)
        {x : V | x ∈ pOne.support ∧ x ≠ (zT : V)} := by
    rw [Set.disjoint_left]
    intro x hx_bridge hx_one
    have hx_prefix :
        x ∈ (p.reverse.takeUntil z hz_p_rev).support := by
      have hx_rev :
          x ∈ (p.reverse.takeUntil z hz_p_rev).reverse.support := by
        simpa [pBridge] using hx_bridge.1
      simpa [SimpleGraph.Walk.support_reverse] using hx_rev
    have hx_q : x ∈ q.support :=
      hone_support_q hx_one.1
    have hx_eq : x = z := hfirst x hx_q hx_prefix
    exact hx_bridge.2.1 (by simpa [zT] using hx_eq)
  have hleft_one_disjoint :
      Disjoint
        {x : V | x ∈ pLeft.support ∧ x ≠ (zT : V)}
        {x : V | x ∈ pOne.support ∧ x ≠ (zT : V)} := by
    rw [Set.disjoint_left]
    intro x hx_left hx_one
    have hx_take_rev : x ∈ (q.takeUntil z hz_q).reverse.support := by
      simpa [pLeft] using hx_left.1
    have hx_take : x ∈ (q.takeUntil z hz_q).support := by
      simpa [SimpleGraph.Walk.support_reverse] using hx_take_rev
    have hx_drop : x ∈ (q.dropUntil z hz_q).support := by
      simpa [pOne] using hx_one.1
    have hx_eq : x = z :=
      Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        hq hz_q hx_take hx_drop
    exact hx_left.2 (by simpa [zT] using hx_eq)
  exact ⟨zT, pBridge, pLeft, pOne,
    hpBridge, hpLeft, hpOne, hpBridge_le, hpLeft_le, hpOne_le,
    by simpa [zT] using hz_q, hz_internal, hbridge_support_p,
    hleft_support_q, hone_support_q, hright_not_pLeft, hright_not_pOne,
    hbridge_left_disjoint, hbridge_one_disjoint, hleft_one_disjoint⟩


theorem Subgraph.exists_right_first_common_split
    [DecidableEq V]
    {T : G.Subgraph}
    {left right three : V}
    {p : G.Walk left right}
    {q : G.Walk right three}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hleft_not_q : left ∉ q.support)
    (hright :
      Exists fun zT : T.verts =>
        (zT : V) ∈ Walk.InternalVertices p ∧
          (zT : V) ∈ q.support ∧
            (zT : V) ≠ right) :
    Exists fun zT : T.verts =>
      Exists fun pBridge : G.Walk left (zT : V) =>
      Exists fun pRight : G.Walk (zT : V) right =>
      Exists fun pThree : G.Walk (zT : V) three =>
        pBridge.IsPath ∧ pRight.IsPath ∧ pThree.IsPath ∧
          pBridge.toSubgraph ≤ T ∧ pRight.toSubgraph ≤ T ∧
            pThree.toSubgraph ≤ T ∧
              (zT : V) ∈ q.support ∧
                (zT : V) ∈ Walk.InternalVertices p ∧
                  (forall {x : V}, x ∈ pBridge.support -> x ∈ p.support) ∧
                    (forall {x : V}, x ∈ pRight.support -> x ∈ q.support) ∧
                      (forall {x : V}, x ∈ pThree.support -> x ∈ q.support) ∧
                        left ∉ pRight.support ∧
                          left ∉ pThree.support ∧
                            Disjoint
                              (Walk.InternalVertices pBridge)
                              {x : V | x ∈ pRight.support ∧ x ≠ (zT : V)} ∧
                            Disjoint
                              (Walk.InternalVertices pBridge)
                              {x : V | x ∈ pThree.support ∧ x ≠ (zT : V)} ∧
                              Disjoint
                                {x : V | x ∈ pRight.support ∧ x ≠ (zT : V)}
                                {x : V | x ∈ pThree.support ∧ x ≠ (zT : V)} := by
  classical
  have hright_rev :
      Exists fun zT : T.verts =>
        (zT : V) ∈ Walk.InternalVertices p.reverse ∧
          (zT : V) ∈ q.support ∧
            (zT : V) ≠ right := by
    rcases hright with ⟨zT, hz_internal, hz_q, hz_ne_right⟩
    exact ⟨zT,
      (Walk.mem_internalVertices_reverse_iff p).2 hz_internal,
      hz_q, hz_ne_right⟩
  rcases Subgraph.exists_left_first_common_split
      (T := T) (p := p.reverse) (q := q)
      hp.reverse hq
      (by simpa [SimpleGraph.Walk.toSubgraph_reverse] using hp_le)
      hq_le hleft_not_q hright_rev with
    ⟨zT, pBridgeRev, pRight, pThree,
      hpBridgeRev, hpRight, hpThree,
      hpBridgeRev_le, hpRight_le, hpThree_le,
      hz_q, hz_internal_rev, hbridgeRev_support_pRev,
      hright_support_q, hthree_support_q,
      hleft_not_pRight, hleft_not_pThree,
      hbridgeRev_right_disjoint,
      hbridgeRev_three_disjoint,
      hright_three_disjoint⟩
  let pBridge : G.Walk left (zT : V) := pBridgeRev.reverse
  have hpBridge : pBridge.IsPath := by
    simpa [pBridge] using hpBridgeRev.reverse
  have hpBridge_le : pBridge.toSubgraph ≤ T := by
    simpa [pBridge, SimpleGraph.Walk.toSubgraph_reverse] using hpBridgeRev_le
  have hz_internal : (zT : V) ∈ Walk.InternalVertices p :=
    (Walk.mem_internalVertices_reverse_iff p).1 hz_internal_rev
  have hbridge_support_p :
      forall {x : V}, x ∈ pBridge.support -> x ∈ p.support := by
    intro x hx
    have hx_rev : x ∈ pBridgeRev.support := by
      simpa [pBridge, SimpleGraph.Walk.support_reverse] using hx
    have hx_p_rev : x ∈ p.reverse.support :=
      hbridgeRev_support_pRev hx_rev
    simpa [SimpleGraph.Walk.support_reverse] using hx_p_rev
  have hbridge_right_disjoint :
      Disjoint
        (Walk.InternalVertices pBridge)
        {x : V | x ∈ pRight.support ∧ x ≠ (zT : V)} := by
    rw [Set.disjoint_left]
    intro x hx_bridge hx_right
    have hx_bridge_rev : x ∈ Walk.InternalVertices pBridgeRev := by
      simpa [pBridge, Walk.internalVertices_reverse] using hx_bridge
    exact Set.disjoint_left.mp hbridgeRev_right_disjoint
      hx_bridge_rev hx_right
  have hbridge_three_disjoint :
      Disjoint
        (Walk.InternalVertices pBridge)
        {x : V | x ∈ pThree.support ∧ x ≠ (zT : V)} := by
    rw [Set.disjoint_left]
    intro x hx_bridge hx_three
    have hx_bridge_rev : x ∈ Walk.InternalVertices pBridgeRev := by
      simpa [pBridge, Walk.internalVertices_reverse] using hx_bridge
    exact Set.disjoint_left.mp hbridgeRev_three_disjoint
      hx_bridge_rev hx_three
  exact ⟨zT, pBridge, pRight, pThree,
    hpBridge, hpRight, hpThree, hpBridge_le, hpRight_le, hpThree_le,
    hz_q, hz_internal, hbridge_support_p, hright_support_q,
    hthree_support_q, hleft_not_pRight, hleft_not_pThree,
    hbridge_right_disjoint, hbridge_three_disjoint,
    hright_three_disjoint⟩


theorem Subgraph.tree_mem_support_iff_of_isPath
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {u v : T.verts}
    {p q : G.Walk (u : V) (v : V)}
    (hT : T.coe.IsTree)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (z : T.verts) :
    (z : V) ∈ p.support ↔ (z : V) ∈ q.support := by
  classical
  let pT : T.coe.Walk u v :=
    (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let qT : T.coe.Walk u v :=
    (Walk.liftToSubgraph q hq_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hpT : pT.IsPath := by
    simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp
  have hqT : qT.IsPath := by
    simpa [qT] using Walk.liftToSubgraph_isPath hq_le hq
  have hiffT : z ∈ pT.support ↔ z ∈ qT.support :=
    IsTree.mem_support_iff_of_isPath hT hpT hqT
  constructor
  · intro hz
    have hzT : z ∈ pT.support := by
      simpa [pT] using
        ((Walk.mem_support_liftToSubgraph_iff hp_le (z := z)).mpr hz)
    exact
      (Walk.mem_support_liftToSubgraph_iff hq_le (z := z)).mp
        (by simpa [qT] using hiffT.mp hzT)
  · intro hz
    have hzT : z ∈ qT.support := by
      simpa [qT] using
        ((Walk.mem_support_liftToSubgraph_iff hq_le (z := z)).mpr hz)
    exact
      (Walk.mem_support_liftToSubgraph_iff hp_le (z := z)).mp
        (by simpa [pT] using hiffT.mpr hzT)


theorem Subgraph.tree_mem_support_iff_reverse_of_isPath
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {u v : T.verts}
    {p : G.Walk (u : V) (v : V)}
    {q : G.Walk (v : V) (u : V)}
    (hT : T.coe.IsTree)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (z : T.verts) :
    (z : V) ∈ p.support ↔ (z : V) ∈ q.support := by
  have hq_rev_le : q.reverse.toSubgraph ≤ T := by
    simpa [SimpleGraph.Walk.toSubgraph_reverse] using hq_le
  have hiff :=
    Subgraph.tree_mem_support_iff_of_isPath
      (G := G) (T := T) (u := u) (v := v)
      hT hp_le hq_rev_le hp hq.reverse z
  simpa [SimpleGraph.Walk.support_reverse] using hiff


theorem Subgraph.tree_mem_takeUntil_iff_of_isPath
    {T : G.Subgraph}
    [DecidableEq T.verts]
    [DecidableEq V]
    {root pEnd qEnd x : V}
    {p : G.Walk root pEnd}
    {q : G.Walk root qEnd}
    (hT : T.coe.IsTree)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hxp : x ∈ p.support)
    (hxq : x ∈ q.support)
    (z : T.verts) :
    (z : V) ∈ (p.takeUntil x hxp).support ↔
      (z : V) ∈ (q.takeUntil x hxq).support := by
  classical
  have hrootT : root ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hp_le p.start_mem_support
  have hxT : x ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hp_le hxp
  let rootT : T.verts := ⟨root, hrootT⟩
  let xT : T.verts := ⟨x, hxT⟩
  have hp_prefix_le : (p.takeUntil x hxp).toSubgraph ≤ T :=
    le_trans (Walk.toSubgraph_takeUntil_le p hxp) hp_le
  have hq_prefix_le : (q.takeUntil x hxq).toSubgraph ≤ T :=
    le_trans (Walk.toSubgraph_takeUntil_le q hxq) hq_le
  have hp_prefix : (p.takeUntil x hxp).IsPath :=
    hp.takeUntil hxp
  have hq_prefix : (q.takeUntil x hxq).IsPath :=
    hq.takeUntil hxq
  have hiff :=
    Subgraph.tree_mem_support_iff_of_isPath
      (G := G) (T := T) (u := rootT) (v := xT)
      hT hp_prefix_le hq_prefix_le hp_prefix hq_prefix z
  simpa [rootT, xT] using hiff


theorem Subgraph.tree_mem_takeUntil_of_mem_takeUntil_of_isPath
    {T : G.Subgraph}
    [DecidableEq T.verts]
    [DecidableEq V]
    {root pEnd qEnd x y : V}
    {p : G.Walk root pEnd}
    {q : G.Walk root qEnd}
    (hT : T.coe.IsTree)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hxp : x ∈ p.support)
    (hxq : x ∈ q.support)
    (hy : y ∈ (p.takeUntil x hxp).support) :
    y ∈ (q.takeUntil x hxq).support := by
  classical
  have hp_prefix_le : (p.takeUntil x hxp).toSubgraph ≤ T :=
    le_trans (Walk.toSubgraph_takeUntil_le p hxp) hp_le
  have hyT : y ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hp_prefix_le hy
  let yT : T.verts := ⟨y, hyT⟩
  exact
    (Subgraph.tree_mem_takeUntil_iff_of_isPath
      (G := G) (T := T) hT hp_le hq_le hp hq hxp hxq yT).mp
      (by simpa [yT] using hy)


theorem Walk.IsPath.append_of_punctured_supports_disjoint
    {u v w : V}
    {p : G.Walk u v}
    {q : G.Walk v w}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hdisjoint :
      Disjoint
        {z : V | z ∈ p.support ∧ z ≠ v}
        {z : V | z ∈ q.support ∧ z ≠ v}) :
    (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
  refine List.Nodup.append hp.support_nodup hq.support_nodup.tail ?_
  rw [List.disjoint_left]
  intro z hz_p hz_q_tail
  have hz_q : z ∈ q.support := List.mem_of_mem_tail hz_q_tail
  have hz_ne_v : z ≠ v := by
    intro hz_eq
    exact Walk.IsPath.start_notMem_tail_support hq
      (by simpa [hz_eq] using hz_q_tail)
  exact
    Set.disjoint_left.mp hdisjoint
      ⟨hz_p, hz_ne_v⟩ ⟨hz_q, hz_ne_v⟩


theorem IsTree.exists_rooted_paths_common_nonroot_of_endpoint_path_avoids_root
    [DecidableEq V]
    {root a b : V}
    (hT : G.IsTree)
    {p : G.Walk root a}
    {q : G.Walk root b}
    {r : G.Walk a b}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hr : r.IsPath)
    (hroot_not_r : root ∉ r.support) :
    Exists fun z : V =>
      z ∈ p.support ∧ z ≠ root ∧ z ∈ q.support ∧ z ≠ root := by
  classical
  by_contra hnone
  push Not at hnone
  have hdisjoint :
      Disjoint
        {z : V | z ∈ p.reverse.support ∧ z ≠ root}
        {z : V | z ∈ q.support ∧ z ≠ root} := by
    rw [Set.disjoint_left]
    rintro z ⟨hz_p_rev, hz_ne_root⟩ ⟨hz_q, _hz_ne_root'⟩
    have hz_p : z ∈ p.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hz_p_rev
    exact hz_ne_root (hnone z hz_p hz_ne_root hz_q)
  have hpq : (p.reverse.append q).IsPath :=
    Walk.IsPath.append_of_punctured_supports_disjoint
      hp.reverse hq hdisjoint
  have hroot_append : root ∈ (p.reverse.append q).support := by
    exact SimpleGraph.Walk.subset_support_append_left
      p.reverse q p.reverse.end_mem_support
  have hroot_r : root ∈ r.support :=
    (IsTree.mem_support_iff_of_isPath hT hpq hr).mp hroot_append
  exact hroot_not_r hroot_r


theorem Subgraph.tree_exists_rooted_paths_common_nonroot_of_endpoint_path_avoids_root
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {root a b : T.verts}
    (hT : T.coe.IsTree)
    {p : G.Walk (root : V) (a : V)}
    {q : G.Walk (root : V) (b : V)}
    {r : G.Walk (a : V) (b : V)}
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hr_le : r.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hr : r.IsPath)
    (hroot_not_r : (root : V) ∉ r.support) :
    Exists fun zT : T.verts =>
      (zT : V) ∈ p.support ∧ (zT : V) ≠ (root : V) ∧
        (zT : V) ∈ q.support ∧ (zT : V) ≠ (root : V) := by
  classical
  let pT : T.coe.Walk root a :=
    (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let qT : T.coe.Walk root b :=
    (Walk.liftToSubgraph q hq_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let rT : T.coe.Walk a b :=
    (Walk.liftToSubgraph r hr_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hpT : pT.IsPath := by
    simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp
  have hqT : qT.IsPath := by
    simpa [qT] using Walk.liftToSubgraph_isPath hq_le hq
  have hrT : rT.IsPath := by
    simpa [rT] using Walk.liftToSubgraph_isPath hr_le hr
  have hroot_not_rT : root ∉ rT.support := by
    intro hroot
    exact hroot_not_r (by
      simpa [rT] using
        ((Walk.mem_support_liftToSubgraph_iff hr_le (z := root)).mp hroot))
  rcases
    IsTree.exists_rooted_paths_common_nonroot_of_endpoint_path_avoids_root
      (G := T.coe) hT hpT hqT hrT hroot_not_rT with
    ⟨zT, hz_p, hz_ne_root, hz_q, hz_ne_root'⟩
  exact ⟨zT,
    by
      simpa [pT] using
        ((Walk.mem_support_liftToSubgraph_iff hp_le (z := zT)).mp hz_p),
    by
      intro h
      exact hz_ne_root (Subtype.ext h),
    by
      simpa [qT] using
        ((Walk.mem_support_liftToSubgraph_iff hq_le (z := zT)).mp hz_q),
    by
      intro h
      exact hz_ne_root' (Subtype.ext h)⟩



/-! More path/tree segment lemmas needed by the split Near-Hajos path-carrier proof. -/

theorem Walk.IsPath.not_mem_dropUntil_of_mem_takeUntil_ne
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hy : y ∈ p.support)
    (hx_before_y : x ∈ (p.takeUntil y hy).support)
    (hxy : x ≠ y) :
    x ∉ (p.dropUntil y hy).support := by
  intro hx_drop
  exact hxy
    (Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      hp hy hx_before_y hx_drop)


theorem Walk.IsPath.support_dropUntil_takeUntil_subset_dropUntil
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hy : y ∈ p.support)
    (hx_before_y : x ∈ (p.takeUntil y hy).support) :
    ((p.takeUntil y hy).dropUntil x hx_before_y).support ⊆
      (p.dropUntil x
        (SimpleGraph.Walk.support_takeUntil_subset p hy hx_before_y)).support := by
  intro z hz_segment
  have hx : x ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hy hx_before_y
  have hz_prefix : z ∈ (p.takeUntil y hy).support :=
    SimpleGraph.Walk.support_dropUntil_subset
      (p.takeUntil y hy) hx_before_y hz_segment
  have hz_p : z ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hy hz_prefix
  rcases Walk.mem_support_takeUntil_or_dropUntil_of_mem_support
      (p := p) hx hz_p with hz_take | hz_drop
  · have hz_take_prefix :
        z ∈ ((p.takeUntil y hy).takeUntil x hx_before_y).support := by
      simpa [SimpleGraph.Walk.takeUntil_takeUntil] using hz_take
    have hz_eq :
        z = x :=
      Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        (hp.takeUntil hy) hx_before_y hz_take_prefix hz_segment
    simp [hz_eq]
  · simpa [hx] using hz_drop


theorem Walk.IsPath.internalVertices_dropUntil_takeUntil_subset_dropUntil
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hy : y ∈ Walk.InternalVertices p)
    (hx_before_y : x ∈ (p.takeUntil y hy.1).support) :
    Walk.InternalVertices
        ((p.takeUntil y hy.1).dropUntil x hx_before_y) ⊆
      Walk.InternalVertices
        (p.dropUntil x
          (SimpleGraph.Walk.support_takeUntil_subset p hy.1 hx_before_y)) := by
  intro z hz
  have hx : x ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hy.1 hx_before_y
  have hz_support :
      z ∈ (p.dropUntil x hx).support :=
    Walk.IsPath.support_dropUntil_takeUntil_subset_dropUntil
      hp hy.1 hx_before_y hz.1
  refine ⟨hz_support, ?_, ?_⟩
  · exact hz.2.1
  · intro hz_eq_end
    have hz_prefix :
        z ∈ (p.takeUntil y hy.1).support :=
      SimpleGraph.Walk.support_dropUntil_subset
        (p.takeUntil y hy.1) hx_before_y hz.1
    exact Walk.IsPath.end_not_mem_takeUntil_support_of_internal
      hp hy (by simpa [hz_eq_end] using hz_prefix)


theorem Walk.IsPath.internalVertices_dropUntil_takeUntil_subset_takeUntil
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ Walk.InternalVertices p)
    (hy : y ∈ p.support)
    (hx_before_y : x ∈ (p.takeUntil y hy).support) :
    Walk.InternalVertices
        ((p.takeUntil y hy).dropUntil x hx_before_y) ⊆
      Walk.InternalVertices (p.takeUntil y hy) := by
  intro z hz
  have hz_support :
      z ∈ (p.takeUntil y hy).support :=
    SimpleGraph.Walk.support_dropUntil_subset
      (p.takeUntil y hy) hx_before_y hz.1
  refine ⟨hz_support, ?_, ?_⟩
  · intro hz_eq_start
    have hz_drop :
        u ∈
          ((p.takeUntil y hy).dropUntil x hx_before_y).support := by
      simpa [hz_eq_start] using hz.1
    have hu_drop :
        u ∈ (p.dropUntil x hx.1).support :=
      Walk.IsPath.support_dropUntil_takeUntil_subset_dropUntil
        hp hy hx_before_y hz_drop
    exact Walk.IsPath.start_not_mem_dropUntil_support_of_internal
      hp hx hu_drop
  · exact hz.2.2


theorem IsTree.glue_mem_support_of_punctured_supports_disjoint
    {u v w : V}
    (hT : G.IsTree)
    {p : G.Walk u v}
    {q : G.Walk v w}
    {r : G.Walk u w}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hr : r.IsPath)
    (hdisjoint :
      Disjoint
        {z : V | z ∈ p.support ∧ z ≠ v}
        {z : V | z ∈ q.support ∧ z ≠ v}) :
    v ∈ r.support := by
  have hpq : (p.append q).IsPath :=
    Walk.IsPath.append_of_punctured_supports_disjoint hp hq hdisjoint
  have hmem : v ∈ (p.append q).support := by
    exact SimpleGraph.Walk.subset_support_append_left p q p.end_mem_support
  exact (IsTree.mem_support_iff_of_isPath hT hpq hr).mp hmem


theorem Subgraph.tree_glue_mem_support_of_punctured_supports_disjoint
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {u v w : T.verts}
    (hT : T.coe.IsTree)
    {p : G.Walk (u : V) (v : V)}
    {q : G.Walk (v : V) (w : V)}
    {r : G.Walk (u : V) (w : V)}
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hr_le : r.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hr : r.IsPath)
    (hdisjoint :
      Disjoint
        {z : V | z ∈ p.support ∧ z ≠ (v : V)}
        {z : V | z ∈ q.support ∧ z ≠ (v : V)}) :
    (v : V) ∈ r.support := by
  classical
  let pT : T.coe.Walk u v :=
    (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let qT : T.coe.Walk v w :=
    (Walk.liftToSubgraph q hq_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let rT : T.coe.Walk u w :=
    (Walk.liftToSubgraph r hr_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hpT : pT.IsPath := by
    simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp
  have hqT : qT.IsPath := by
    simpa [qT] using Walk.liftToSubgraph_isPath hq_le hq
  have hrT : rT.IsPath := by
    simpa [rT] using Walk.liftToSubgraph_isPath hr_le hr
  have hdisjointT :
      Disjoint
        {z : T.verts | z ∈ pT.support ∧ z ≠ v}
        {z : T.verts | z ∈ qT.support ∧ z ≠ v} := by
    rw [Set.disjoint_left]
    intro z hz_p hz_q
    have hz_pG : (z : V) ∈ p.support := by
      simpa [pT] using
        ((Walk.mem_support_liftToSubgraph_iff hp_le (z := z)).mp hz_p.1)
    have hz_qG : (z : V) ∈ q.support := by
      simpa [qT] using
        ((Walk.mem_support_liftToSubgraph_iff hq_le (z := z)).mp hz_q.1)
    have hz_ne_vG : (z : V) ≠ (v : V) := by
      intro h
      exact hz_p.2 (Subtype.ext h)
    exact Set.disjoint_left.mp hdisjoint
      ⟨hz_pG, hz_ne_vG⟩ ⟨hz_qG, hz_ne_vG⟩
  have hvT : v ∈ rT.support :=
    IsTree.glue_mem_support_of_punctured_supports_disjoint
      (G := T.coe) hT hpT hqT hrT hdisjointT
  simpa [rT] using
    ((Walk.mem_support_liftToSubgraph_iff hr_le (z := v)).mp hvT)


theorem Subgraph.tree_common_prefix_split_mem_start_path
    {T : G.Subgraph}
    [DecidableEq T.verts]
    [DecidableEq V]
    {a b c d z : V}
    {p : G.Walk a b}
    {q : G.Walk c d}
    {r : G.Walk a c}
    (hT : T.coe.IsTree)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hr_le : r.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hr : r.IsPath)
    (hzp : z ∈ p.support)
    (hzq : z ∈ q.support)
    (hdisjoint :
      Disjoint
        {x : V | x ∈ (p.takeUntil z hzp).support ∧ x ≠ z}
        {x : V | x ∈ (q.takeUntil z hzq).support ∧ x ≠ z}) :
    z ∈ r.support := by
  classical
  have haT : a ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hp_le p.start_mem_support
  have hzT : z ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hp_le hzp
  have hcT : c ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hq_le q.start_mem_support
  let aT : T.verts := ⟨a, haT⟩
  let zT : T.verts := ⟨z, hzT⟩
  let cT : T.verts := ⟨c, hcT⟩
  have hp_prefix_le :
      (p.takeUntil z hzp).toSubgraph ≤ T := by
    exact le_trans (Walk.toSubgraph_takeUntil_le p hzp) hp_le
  have hq_prefix_rev_le :
      (q.takeUntil z hzq).reverse.toSubgraph ≤ T := by
    simpa [SimpleGraph.Walk.toSubgraph_reverse] using
      (le_trans (Walk.toSubgraph_takeUntil_le q hzq) hq_le)
  have hp_prefix_path : (p.takeUntil z hzp).IsPath :=
    hp.takeUntil hzp
  have hq_prefix_rev_path : (q.takeUntil z hzq).reverse.IsPath :=
    (hq.takeUntil hzq).reverse
  exact
    Subgraph.tree_glue_mem_support_of_punctured_supports_disjoint
      (G := G) (T := T) (u := aT) (v := zT) (w := cT)
      hT hp_prefix_le hq_prefix_rev_le hr_le
      hp_prefix_path hq_prefix_rev_path hr
      (by
        simpa [aT, zT, cT, SimpleGraph.Walk.support_reverse] using hdisjoint)


/-- Removing a nonempty initial arc after the base edge of a simple cycle and
then closing through that base edge leaves a simple complementary path.  Its
dart list is the cyclic suffix beginning at `k + 1`, followed by the first
cycle dart. -/
theorem Walk.IsCycle.isPath_drop_succ_append_take_one
    [DecidableEq V]
    {r : V} (c : G.Walk r r) (hc : c.IsCycle)
    {k : Nat} (hk_pos : 0 < k) (hk : k + 1 < c.length) :
    ((c.drop (k + 1)).append (c.take 1)).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,
    SimpleGraph.Walk.take_support_eq_support_take_succ]
  have hk_le : k + 1 <= c.length := by omega
  rw [Nat.min_eq_left hk_le]
  let l := c.support.tail
  have hlNodup : l.Nodup := by
    simpa [l] using hc.support_nodup
  have hlNe : l ≠ [] := by
    exact List.ne_nil_of_mem (by
      simpa [l] using c.end_mem_tail_support hc.not_nil)
  have hsupportCons :
      c.support = c.support.head c.support_ne_nil :: l :=
    (List.cons_head_tail c.support_ne_nil).symm
  rw [hsupportCons]
  cases hl : l with
  | nil => exact False.elim (hlNe hl)
  | cons a tail =>
      cases k with
      | zero => omega
      | succ n =>
          simp only [Nat.add_assoc,
            List.drop_succ_cons, List.take_succ_cons, List.take_zero,
            List.tail_cons]
          have hconsNodup : (a :: tail).Nodup := by
            simpa [hl] using hlNodup
          have htailNodup : tail.Nodup := hconsNodup.tail
          have hsplit : (tail.take n ++ tail.drop n).Nodup := by
            rw [List.take_append_drop]
            exact htailNodup
          have hdropNodup : (tail.drop n).Nodup :=
            (List.nodup_append'.mp hsplit).2.1
          have haNotDrop : a ∉ tail.drop n := by
            intro ha
            have haTail : a ∈ tail := by
              rw [← List.take_append_drop n tail]
              exact List.mem_append_right _ ha
            exact (List.nodup_cons.mp hconsNodup).1 haTail
          exact hdropNodup.append (by simp) (by
            rw [List.disjoint_left]
            intro x hx hsingle
            simp only [List.mem_singleton] at hsingle
            exact haNotDrop (hsingle ▸ hx))



end Schematic.Math.GraphTheory
