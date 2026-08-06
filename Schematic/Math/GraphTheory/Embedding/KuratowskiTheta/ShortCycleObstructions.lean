import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.LowDegreeStructure

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Deleted-end square form of the source alternation step.  The four vertices
`a,b,c,d` lie on the cycle in `G - x - y`; deleting the middle pair `b,c`
leaves `a--d` together with `x--y`, and maximum degree two forces `a,d` to
attach to opposite endpoints. -/
theorem deleteEdgeEndsGraph_square_opposite_attachments_of_middle_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {a b c d : {w : V | w ∉ ({x, y} : Set V)}}
    (hxy : G.Adj x y)
    (hda : (deleteEdgeEndsGraph G x y).Adj d a)
    (hab_ne : a ≠ b)
    (hac_ne : a ≠ c)
    (hdb_ne : d ≠ b)
    (hdc_ne : d ≠ c)
    (hattach_a : G.Adj (a : V) x ∨ G.Adj (a : V) y)
    (hattach_d : G.Adj (d : V) x ∨ G.Adj (d : V) y)
    (hdegree_middle :
      forall z : {w : V | w ∉ ({(b : V), (c : V)} : Set V)},
        (deleteEdgeEndsGraph G (b : V) (c : V)).degree z <= 2) :
    (G.Adj x (a : V) ∧ ¬ G.Adj y (a : V) ∧
        G.Adj y (d : V) ∧ ¬ G.Adj x (d : V)) ∨
      (G.Adj y (a : V) ∧ ¬ G.Adj x (a : V) ∧
        G.Adj x (d : V) ∧ ¬ G.Adj y (d : V)) := by
  classical
  have hx_not_bc : x ∉ ({(b : V), (c : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hxb
      exact b.2 (Or.inl (by simpa using hxb.symm))
    · intro hxc
      exact c.2 (Or.inl (by simpa using hxc.symm))
  have hy_not_bc : y ∉ ({(b : V), (c : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hyb
      exact b.2 (Or.inr (by simpa using hyb.symm))
    · intro hyc
      exact c.2 (Or.inr (by simpa using hyc.symm))
  have ha_not_bc : (a : V) ∉ ({(b : V), (c : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hab_ne (Subtype.ext h), fun h => hac_ne (Subtype.ext h)⟩
  have hd_not_bc : (d : V) ∉ ({(b : V), (c : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hdb_ne (Subtype.ext h), fun h => hdc_ne (Subtype.ext h)⟩
  let xH : {w : V | w ∉ ({(b : V), (c : V)} : Set V)} := ⟨x, hx_not_bc⟩
  let yH : {w : V | w ∉ ({(b : V), (c : V)} : Set V)} := ⟨y, hy_not_bc⟩
  let aH : {w : V | w ∉ ({(b : V), (c : V)} : Set V)} := ⟨a, ha_not_bc⟩
  let dH : {w : V | w ∉ ({(b : V), (c : V)} : Set V)} := ⟨d, hd_not_bc⟩
  have ha_attach :
      (deleteEdgeEndsGraph G (b : V) (c : V)).Adj aH xH ∨
        (deleteEdgeEndsGraph G (b : V) (c : V)).Adj aH yH := by
    rcases hattach_a with hax | hay
    · exact Or.inl (by simpa [deleteEdgeEndsGraph, aH, xH] using hax)
    · exact Or.inr (by simpa [deleteEdgeEndsGraph, aH, yH] using hay)
  have hd_attach :
      (deleteEdgeEndsGraph G (b : V) (c : V)).Adj dH xH ∨
        (deleteEdgeEndsGraph G (b : V) (c : V)).Adj dH yH := by
    rcases hattach_d with hdx | hdy
    · exact Or.inl (by simpa [deleteEdgeEndsGraph, dH, xH] using hdx)
    · exact Or.inr (by simpa [deleteEdgeEndsGraph, dH, yH] using hdy)
  have h_alt :
      ((deleteEdgeEndsGraph G (b : V) (c : V)).Adj xH aH ∧
          (deleteEdgeEndsGraph G (b : V) (c : V)).Adj yH dH) ∨
        ((deleteEdgeEndsGraph G (b : V) (c : V)).Adj yH aH ∧
          (deleteEdgeEndsGraph G (b : V) (c : V)).Adj xH dH) :=
    opposite_attachments_of_degree_le_two_edge_pair
      (H := deleteEdgeEndsGraph G (b : V) (c : V))
      (fun z => hdegree_middle z)
      (by simpa [deleteEdgeEndsGraph, xH, yH] using hxy)
      (by simpa [deleteEdgeEndsGraph, aH, dH] using hda.symm)
      (by
        intro h
        have hx_a : x = (a : V) := by simpa [xH, aH] using congrArg Subtype.val h
        exact a.2 (Or.inl hx_a.symm))
      (by
        intro h
        have hx_d : x = (d : V) := by simpa [xH, dH] using congrArg Subtype.val h
        exact d.2 (Or.inl hx_d.symm))
      (by
        intro h
        have hy_a : y = (a : V) := by simpa [yH, aH] using congrArg Subtype.val h
        exact a.2 (Or.inr hy_a.symm))
      (by
        intro h
        have hy_d : y = (d : V) := by simpa [yH, dH] using congrArg Subtype.val h
        exact d.2 (Or.inr hy_d.symm))
      ha_attach hd_attach
  have hxH_ne_dH : xH ≠ dH := by
    intro h
    have hxd : x = (d : V) := by simpa [xH, dH] using congrArg Subtype.val h
    exact d.2 (Or.inl hxd.symm)
  have hyH_ne_dH : yH ≠ dH := by
    intro h
    have hyd : y = (d : V) := by simpa [yH, dH] using congrArg Subtype.val h
    exact d.2 (Or.inr hyd.symm)
  have hxH_ne_aH : xH ≠ aH := by
    intro h
    have hxa : x = (a : V) := by simpa [xH, aH] using congrArg Subtype.val h
    exact a.2 (Or.inl hxa.symm)
  have hyH_ne_aH : yH ≠ aH := by
    intro h
    have hya : y = (a : V) := by simpa [yH, aH] using congrArg Subtype.val h
    exact a.2 (Or.inr hya.symm)
  have hnot_a_both : ¬ (G.Adj (a : V) x ∧ G.Adj (a : V) y) := by
    intro hboth
    have hxy_eq : xH = yH :=
      deleteEdgeEndsGraph_neighbor_unique_outside_singleton_of_degree_le_two
        (G := G) (p := (b : V)) (q := (c : V)) (a := aH)
        (y := dH) (r := xH) (s := yH)
        (hdegree_middle aH)
        (by simpa [deleteEdgeEndsGraph, aH, dH] using hda.symm)
        hxH_ne_dH hyH_ne_dH
        (by simpa [deleteEdgeEndsGraph, aH, xH] using hboth.1)
        (by simpa [deleteEdgeEndsGraph, aH, yH] using hboth.2)
    exact hxy.ne (congrArg Subtype.val hxy_eq)
  have hnot_d_both : ¬ (G.Adj (d : V) x ∧ G.Adj (d : V) y) := by
    intro hboth
    have hxy_eq : xH = yH :=
      deleteEdgeEndsGraph_neighbor_unique_outside_singleton_of_degree_le_two
        (G := G) (p := (b : V)) (q := (c : V)) (a := dH)
        (y := aH) (r := xH) (s := yH)
        (hdegree_middle dH)
        (by simpa [deleteEdgeEndsGraph, dH, aH] using hda)
        hxH_ne_aH hyH_ne_aH
        (by simpa [deleteEdgeEndsGraph, dH, xH] using hboth.1)
        (by simpa [deleteEdgeEndsGraph, dH, yH] using hboth.2)
    exact hxy.ne (congrArg Subtype.val hxy_eq)
  rcases h_alt with hleft | hright
  · have hxa : G.Adj x (a : V) := by
      simpa [deleteEdgeEndsGraph, xH, aH] using hleft.1
    have hyd : G.Adj y (d : V) := by
      simpa [deleteEdgeEndsGraph, yH, dH] using hleft.2
    exact Or.inl
      ⟨hxa,
       by
        intro hya
        exact hnot_a_both ⟨hxa.symm, hya.symm⟩,
       hyd,
       by
        intro hxd
        exact hnot_d_both ⟨hxd.symm, hyd.symm⟩⟩
  · have hya : G.Adj y (a : V) := by
      simpa [deleteEdgeEndsGraph, yH, aH] using hright.1
    have hxd : G.Adj x (d : V) := by
      simpa [deleteEdgeEndsGraph, xH, dH] using hright.2
    exact Or.inr
      ⟨hya,
       by
        intro hxa
        exact hnot_a_both ⟨hxa.symm, hya.symm⟩,
       hxd,
       by
        intro hyd
        exact hnot_d_both ⟨hxd.symm, hyd.symm⟩⟩

/-- Source final-cycle `n >= 5` local exclusion.  Let `b = C[1]` and
`c = C[2]` be the middle edge of a deleted-end cycle `C` in `G - x - y`.
If every vertex of `G - b - c` has degree at most two, then the fifth cycle
vertex `C[4]` cannot be adjacent to either `x` or `y`: its two surviving cycle
neighbours `C[3]` and `C[5]` already use the two available neighbours in
`G - b - c`. -/
theorem deleteEdgeEndsGraph_cycle_getVert_four_not_adj_endpoints_of_middle_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hlen : 5 <= C.length)
    (hdegree :
      forall z : {w : V | w ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)},
        (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).degree z <= 2) :
    ¬ G.Adj (C.getVert 4 : V) x ∧ ¬ G.Adj (C.getVert 4 : V) y := by
  classical
  let bD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 1
  let cD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 2
  let dD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 3
  let eD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 4
  let fD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 5
  let b : V := bD
  let c : V := cD
  let d : V := dD
  let e : V := eD
  let f : V := fD
  have hinj := hC.getVert_injOn
  have h41 : C.getVert 4 ≠ C.getVert 1 := by
    intro h
    have hidx : 4 = 1 := hinj
      (by exact ⟨by omega, by omega⟩)
      (by exact ⟨by omega, by omega⟩) h
    omega
  have h42 : C.getVert 4 ≠ C.getVert 2 := by
    intro h
    have hidx : 4 = 2 := hinj
      (by exact ⟨by omega, by omega⟩)
      (by exact ⟨by omega, by omega⟩) h
    omega
  have h31 : C.getVert 3 ≠ C.getVert 1 := by
    intro h
    have hidx : 3 = 1 := hinj
      (by exact ⟨by omega, by omega⟩)
      (by exact ⟨by omega, by omega⟩) h
    omega
  have h32 : C.getVert 3 ≠ C.getVert 2 := by
    intro h
    have hidx : 3 = 2 := hinj
      (by exact ⟨by omega, by omega⟩)
      (by exact ⟨by omega, by omega⟩) h
    omega
  have h51 : C.getVert 5 ≠ C.getVert 1 := by
    intro h
    have hidx : 5 = 1 := hinj
      (by exact ⟨by omega, by omega⟩)
      (by exact ⟨by omega, by omega⟩) h
    omega
  have h52 : C.getVert 5 ≠ C.getVert 2 := by
    intro h
    have hidx : 5 = 2 := hinj
      (by exact ⟨by omega, by omega⟩)
      (by exact ⟨by omega, by omega⟩) h
    omega
  have h53 : C.getVert 5 ≠ C.getVert 3 := by
    intro h
    have hidx : 5 = 3 := hinj
      (by exact ⟨by omega, by omega⟩)
      (by exact ⟨by omega, by omega⟩) h
    omega
  have hx_not_bc : x ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hxb
      have hb_x : (bD : V) = x := by simpa [b] using hxb.symm
      exact bD.2 (Or.inl hb_x)
    · intro hxc
      have hc_x : (cD : V) = x := by simpa [c] using hxc.symm
      exact cD.2 (Or.inl hc_x)
  have hy_not_bc : y ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hyb
      have hb_y : (bD : V) = y := by simpa [b] using hyb.symm
      exact bD.2 (Or.inr hb_y)
    · intro hyc
      have hc_y : (cD : V) = y := by simpa [c] using hyc.symm
      exact cD.2 (Or.inr hc_y)
  have hd_not_bc : d ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hdb
      exact h31 (Subtype.ext (by simpa [d, b, dD, bD] using hdb))
    · intro hdc
      exact h32 (Subtype.ext (by simpa [d, c, dD, cD] using hdc))
  have he_not_bc : e ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro heb
      exact h41 (Subtype.ext (by simpa [e, b, eD, bD] using heb))
    · intro hec
      exact h42 (Subtype.ext (by simpa [e, c, eD, cD] using hec))
  have hf_not_bc : f ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hfb
      exact h51 (Subtype.ext (by simpa [f, b, fD, bD] using hfb))
    · intro hfc
      exact h52 (Subtype.ext (by simpa [f, c, fD, cD] using hfc))
  let xH : {w : V | w ∉ ({b, c} : Set V)} := ⟨x, hx_not_bc⟩
  let yH : {w : V | w ∉ ({b, c} : Set V)} := ⟨y, hy_not_bc⟩
  let dH : {w : V | w ∉ ({b, c} : Set V)} := ⟨d, hd_not_bc⟩
  let eH : {w : V | w ∉ ({b, c} : Set V)} := ⟨e, he_not_bc⟩
  let fH : {w : V | w ∉ ({b, c} : Set V)} := ⟨f, hf_not_bc⟩
  have hed : G.Adj e d := by
    have hde :
        (deleteEdgeEndsGraph G x y).Adj (C.getVert 3) (C.getVert 4) := by
      simpa using C.adj_getVert_succ (i := 3) (by omega : 3 < C.length)
    have hdeG : G.Adj d e := by
      simpa [deleteEdgeEndsGraph, d, e, dD, eD] using hde
    exact hdeG.symm
  have hef : G.Adj e f := by
    have hefD :
        (deleteEdgeEndsGraph G x y).Adj (C.getVert 4) (C.getVert 5) := by
      simpa using C.adj_getVert_succ (i := 4) (by omega : 4 < C.length)
    simpa [deleteEdgeEndsGraph, e, f, eD, fD] using hefD
  have hfd : fH ≠ dH := by
    intro h
    exact h53 (Subtype.ext (by simpa [fH, dH, f, d, fD, dD] using congrArg Subtype.val h))
  have hxd : xH ≠ dH := by
    intro h
    have hxd_val : x = d := by simpa [xH, dH] using congrArg Subtype.val h
    have hd_x : (dD : V) = x := by simpa [d] using hxd_val.symm
    exact dD.2 (Or.inl hd_x)
  have hyd : yH ≠ dH := by
    intro h
    have hyd_val : y = d := by simpa [yH, dH] using congrArg Subtype.val h
    have hd_y : (dD : V) = y := by simpa [d] using hyd_val.symm
    exact dD.2 (Or.inr hd_y)
  have hfx : fH ≠ xH := by
    intro h
    have hfx_val : f = x := by simpa [fH, xH] using congrArg Subtype.val h
    have hf_x : (fD : V) = x := by simpa [f] using hfx_val
    exact fD.2 (Or.inl hf_x)
  have hfy : fH ≠ yH := by
    intro h
    have hfy_val : f = y := by simpa [fH, yH] using congrArg Subtype.val h
    have hf_y : (fD : V) = y := by simpa [f] using hfy_val
    exact fD.2 (Or.inr hf_y)
  have hdeg_e :
      (deleteEdgeEndsGraph G b c).degree eH <= 2 := hdegree eH
  constructor
  · exact
      deleteEdgeEndsGraph_not_adj_third_of_degree_le_two
        (G := G) (p := b) (q := c) (a := eH) (y := dH) (r := fH) (s := xH)
        hdeg_e
        (by simpa [eH, dH] using hed)
        (by simpa [eH, fH] using hef)
        hfd hxd hfx
  · exact
      deleteEdgeEndsGraph_not_adj_third_of_degree_le_two
        (G := G) (p := b) (q := c) (a := eH) (y := dH) (r := fH) (s := yH)
        hdeg_e
        (by simpa [eH, dH] using hed)
        (by simpa [eH, fH] using hef)
        hfd hyd hfy

/-- If a vertex of `G - x - y` is adjacent in `G` to neither deleted
endpoint, then its original neighbours are exactly neighbours still present in
`G - x - y`, so the original degree is bounded by the deleted-end degree. -/
theorem original_degree_le_deleteEdgeEndsGraph_degree_of_not_adj_endpoints
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hnotx : ¬ G.Adj (z : V) x)
    (hnoty : ¬ G.Adj (z : V) y) :
    G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z := by
  have hbound := degree_le_induce_compl_degree_add_neighbor_inter_ncard
    (G := G) ({x, y} : Set V) z.property
  change G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z +
    (G.neighborSet (z : V) ∩ ({x, y} : Set V)).ncard at hbound
  have hsub :
      G.neighborSet (z : V) ∩ ({x, y} : Set V) ⊆ ∅ := by
    intro w hw
    simp only [Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw.2 with rfl | rfl
    · exact False.elim (hnotx hw.1)
    · exact False.elim (hnoty hw.1)
  have hinter :
      (G.neighborSet (z : V) ∩ ({x, y} : Set V)).ncard <= 0 := by
    simpa using Set.ncard_le_ncard hsub
  omega

/-- Source final-cycle attachment fact.  In the minimum-degree-three
counterexample setting, a degree-at-most-two vertex of `G - x - y` must attach
to at least one of the two deleted endpoints. -/
theorem deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    (hmin : forall w : V, 3 <= G.degree w)
    (z : {w : V | w ∉ ({x, y} : Set V)})
    (hdelete : (deleteEdgeEndsGraph G x y).degree z <= 2) :
    G.Adj (z : V) x ∨ G.Adj (z : V) y := by
  by_contra hnone
  push Not at hnone
  have hle :
      G.degree (z : V) <= (deleteEdgeEndsGraph G x y).degree z :=
    original_degree_le_deleteEdgeEndsGraph_degree_of_not_adj_endpoints
      (G := G) (x := x) (y := y) z hnone.1 hnone.2
  have hge : 3 <= G.degree (z : V) := hmin (z : V)
  omega

/-- The source final-cycle length bound.  Once `G - x - y` is a degree-two
cycle and every deletion `G - p - q` has maximum degree two, the final cycle
cannot have length at least five: `C[4]` is forced by minimum degree to attach
to `x` or `y`, while the middle-deletion degree count forbids both. -/
theorem not_five_le_deleteEdgeEnds_cycle_length_of_middle_degree_le_two_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hdegree_xy :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        z ∈ C.support -> (deleteEdgeEndsGraph G x y).degree z <= 2)
    (hdegree_middle :
      forall z : {w : V | w ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)},
        (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).degree z <= 2) :
    ¬ 5 <= C.length := by
  intro hlen
  have hnot :=
    deleteEdgeEndsGraph_cycle_getVert_four_not_adj_endpoints_of_middle_degree_le_two
      (G := G) C hC hlen hdegree_middle
  have h4_support : C.getVert 4 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨4, ⟨rfl, by omega⟩⟩
  have hattach :
      G.Adj (C.getVert 4 : V) x ∨ G.Adj (C.getVert 4 : V) y :=
    deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
      (G := G) (x := x) (y := y) hmin (C.getVert 4)
      (hdegree_xy (C.getVert 4) h4_support)
  exact hattach.elim hnot.1 hnot.2

/-- Length-four final-cycle alternation for one deleted middle edge.  In the
cycle `C[0], C[1], C[2], C[3]`, deleting `C[1]` and `C[2]` leaves the edge
`C[0]--C[3]`; together with `x--y` and maximum degree two in that deletion,
the two outside vertices `C[0]` and `C[3]` attach to opposite endpoints. -/
theorem deleteEdgeEndsGraph_cycle_length_four_getVert_zero_three_opposite
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hlen : C.length = 4)
    (hdegree_xy :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        z ∈ C.support -> (deleteEdgeEndsGraph G x y).degree z <= 2)
    (hdegree_middle :
      forall z : {w : V | w ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)},
        (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).degree z <= 2) :
    (G.Adj x (C.getVert 0 : V) ∧ G.Adj y (C.getVert 3 : V)) ∨
      (G.Adj y (C.getVert 0 : V) ∧ G.Adj x (C.getVert 3 : V)) := by
  classical
  let aD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 0
  let bD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 1
  let cD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 2
  let dD : {w : V | w ∉ ({x, y} : Set V)} := C.getVert 3
  let a : V := aD
  let b : V := bD
  let c : V := cD
  let d : V := dD
  have h01 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 0) (C.getVert 1) := by
    simpa using C.adj_getVert_succ (by omega : 0 < C.length)
  have h23 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 2) (C.getVert 3) := by
    simpa using C.adj_getVert_succ (i := 2) (by omega : 2 < C.length)
  have h30D :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 3) (C.getVert 0) := by
    have hstep :
        (deleteEdgeEndsGraph G x y).Adj (C.getVert 3) (C.getVert 4) := by
      simpa [hlen] using C.adj_getVert_succ (i := 3) (by omega : 3 < C.length)
    change G.Adj (C.getVert 3 : V) (C.getVert 0 : V)
    have hstepG : G.Adj (C.getVert 3 : V) (C.getVert 4 : V) := by
      simpa [deleteEdgeEndsGraph] using hstep
    have h4r : (C.getVert 4 : V) = (r : V) := by
      have h4r_sub : C.getVert 4 = r := by
        rw [show 4 = C.length by omega, SimpleGraph.Walk.getVert_length]
      exact congrArg Subtype.val h4r_sub
    rw [SimpleGraph.Walk.getVert_zero]
    rw [h4r] at hstepG
    exact hstepG
  have h02_sub : C.getVert 0 ≠ C.getVert 2 := by
    simpa using
      SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one
        (p := C) hC (i := 1) (by omega : 1 <= C.length)
  have h31_sub : C.getVert 3 ≠ C.getVert 1 := by
    intro h
    have hidx : 3 = 1 := hC.getVert_injOn
      (by exact ⟨by omega, by omega⟩)
      (by exact ⟨by omega, by omega⟩) h
    omega
  have ha_not_bc : a ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hab_eq
      exact h01.ne (Subtype.ext (by simpa [a, b, aD, bD] using hab_eq))
    · intro hac_eq
      exact h02_sub (Subtype.ext (by simpa [a, c, aD, cD] using hac_eq))
  have hd_not_bc : d ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hdb_eq
      exact h31_sub (Subtype.ext (by simpa [d, b, dD, bD] using hdb_eq))
    · intro hdc_eq
      exact h23.ne (Subtype.ext (by simpa [d, c, dD, cD] using hdc_eq.symm))
  have hx_not_bc : x ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hxb
      have hb_x : (bD : V) = x := by simpa [b] using hxb.symm
      exact bD.2 (Or.inl hb_x)
    · intro hxc
      have hc_x : (cD : V) = x := by simpa [c] using hxc.symm
      exact cD.2 (Or.inl hc_x)
  have hy_not_bc : y ∉ ({b, c} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hyb
      have hb_y : (bD : V) = y := by simpa [b] using hyb.symm
      exact bD.2 (Or.inr hb_y)
    · intro hyc
      have hc_y : (cD : V) = y := by simpa [c] using hyc.symm
      exact cD.2 (Or.inr hc_y)
  let xH : {w : V | w ∉ ({b, c} : Set V)} := ⟨x, hx_not_bc⟩
  let yH : {w : V | w ∉ ({b, c} : Set V)} := ⟨y, hy_not_bc⟩
  let aH : {w : V | w ∉ ({b, c} : Set V)} := ⟨a, ha_not_bc⟩
  let dH : {w : V | w ∉ ({b, c} : Set V)} := ⟨d, hd_not_bc⟩
  have h0_support : C.getVert 0 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨0, ⟨rfl, by omega⟩⟩
  have h3_support : C.getVert 3 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨3, ⟨rfl, by omega⟩⟩
  have ha_attach :
      (deleteEdgeEndsGraph G b c).Adj aH xH ∨
        (deleteEdgeEndsGraph G b c).Adj aH yH := by
    rcases
        deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
          (G := G) (x := x) (y := y) hmin (C.getVert 0)
          (hdegree_xy (C.getVert 0) h0_support) with hax | hay
    · exact Or.inl (by simpa [deleteEdgeEndsGraph, aH, xH, a, aD] using hax)
    · exact Or.inr (by simpa [deleteEdgeEndsGraph, aH, yH, a, aD] using hay)
  have hd_attach :
      (deleteEdgeEndsGraph G b c).Adj dH xH ∨
        (deleteEdgeEndsGraph G b c).Adj dH yH := by
    rcases
        deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
          (G := G) (x := x) (y := y) hmin (C.getVert 3)
          (hdegree_xy (C.getVert 3) h3_support) with hdx | hdy
    · exact Or.inl (by simpa [deleteEdgeEndsGraph, dH, xH, d, dD] using hdx)
    · exact Or.inr (by simpa [deleteEdgeEndsGraph, dH, yH, d, dD] using hdy)
  have h_alt :
      ((deleteEdgeEndsGraph G b c).Adj xH aH ∧
          (deleteEdgeEndsGraph G b c).Adj yH dH) ∨
        ((deleteEdgeEndsGraph G b c).Adj yH aH ∧
          (deleteEdgeEndsGraph G b c).Adj xH dH) :=
    opposite_attachments_of_degree_le_two_edge_pair
      (H := deleteEdgeEndsGraph G b c)
      (fun z => hdegree_middle z)
      (by simpa [deleteEdgeEndsGraph, xH, yH] using hxy)
      (by simpa [deleteEdgeEndsGraph, aH, dH, a, d, aD, dD] using h30D.symm)
      (by
        intro h
        have hx_a : x = a := by simpa [xH, aH] using congrArg Subtype.val h
        exact aD.2 (Or.inl (by simpa [a] using hx_a.symm)))
      (by
        intro h
        have hx_d : x = d := by simpa [xH, dH] using congrArg Subtype.val h
        exact dD.2 (Or.inl (by simpa [d] using hx_d.symm)))
      (by
        intro h
        have hy_a : y = a := by simpa [yH, aH] using congrArg Subtype.val h
        exact aD.2 (Or.inr (by simpa [a] using hy_a.symm)))
      (by
        intro h
        have hy_d : y = d := by simpa [yH, dH] using congrArg Subtype.val h
        exact dD.2 (Or.inr (by simpa [d] using hy_d.symm)))
      ha_attach hd_attach
  rcases h_alt with hleft | hright
  · exact Or.inl
      ⟨by simpa [deleteEdgeEndsGraph, xH, aH, a, aD] using hleft.1,
       by simpa [deleteEdgeEndsGraph, yH, dH, d, dD] using hleft.2⟩
  · exact Or.inr
      ⟨by simpa [deleteEdgeEndsGraph, yH, aH, a, aD] using hright.1,
       by simpa [deleteEdgeEndsGraph, xH, dH, d, dD] using hright.2⟩

/-- Source final-cycle `n = 4` constructive extraction.  The three square
rotations force the four cycle vertices to attach alternately to the two
deleted endpoints, giving a strict `K_{3,3}` subdivision. -/
theorem containsStrictSubdivision_K33_of_deleteEdgeEnds_cycle_length_four_final
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hlen : C.length = 4)
    (hdegree_xy :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        z ∈ C.support -> (deleteEdgeEndsGraph G x y).degree z <= 2)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z <= 2) :
    ContainsStrictSubdivision K33Graph G := by
  classical
  have h01 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 0) (C.getVert 1) := by
    simpa using C.adj_getVert_succ (by omega : 0 < C.length)
  have h12 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 1) (C.getVert 2) := by
    simpa using C.adj_getVert_succ (i := 1) (by omega : 1 < C.length)
  have h23 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 2) (C.getVert 3) := by
    simpa using C.adj_getVert_succ (i := 2) (by omega : 2 < C.length)
  have h30 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 3) (C.getVert 0) := by
    have hstep :
        (deleteEdgeEndsGraph G x y).Adj (C.getVert 3) (C.getVert 4) := by
      simpa [hlen] using C.adj_getVert_succ (i := 3) (by omega : 3 < C.length)
    change G.Adj (C.getVert 3 : V) (C.getVert 0 : V)
    have hstepG : G.Adj (C.getVert 3 : V) (C.getVert 4 : V) := by
      simpa [deleteEdgeEndsGraph] using hstep
    have h4r : (C.getVert 4 : V) = (r : V) := by
      have h4r_sub : C.getVert 4 = r := by
        rw [show 4 = C.length by omega, SimpleGraph.Walk.getVert_length]
      exact congrArg Subtype.val h4r_sub
    rw [SimpleGraph.Walk.getVert_zero]
    rw [h4r] at hstepG
    exact hstepG
  have h02 : C.getVert 0 ≠ C.getVert 2 := by
    simpa using
      SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one
        (p := C) hC (i := 1) (by omega : 1 <= C.length)
  have h13 : C.getVert 1 ≠ C.getVert 3 := by
    simpa using
      SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one
        (p := C) hC (i := 2) (by omega : 2 <= C.length)
  have h0_support : C.getVert 0 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨0, ⟨rfl, by omega⟩⟩
  have h1_support : C.getVert 1 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨1, ⟨rfl, by omega⟩⟩
  have h2_support : C.getVert 2 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨2, ⟨rfl, by omega⟩⟩
  have h3_support : C.getVert 3 ∈ C.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨3, ⟨rfl, by omega⟩⟩
  have h0_attach :
      G.Adj (C.getVert 0 : V) x ∨ G.Adj (C.getVert 0 : V) y :=
    deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
      (G := G) (x := x) (y := y) hmin (C.getVert 0)
      (hdegree_xy (C.getVert 0) h0_support)
  have h1_attach :
      G.Adj (C.getVert 1 : V) x ∨ G.Adj (C.getVert 1 : V) y :=
    deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
      (G := G) (x := x) (y := y) hmin (C.getVert 1)
      (hdegree_xy (C.getVert 1) h1_support)
  have h2_attach :
      G.Adj (C.getVert 2 : V) x ∨ G.Adj (C.getVert 2 : V) y :=
    deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
      (G := G) (x := x) (y := y) hmin (C.getVert 2)
      (hdegree_xy (C.getVert 2) h2_support)
  have h3_attach :
      G.Adj (C.getVert 3 : V) x ∨ G.Adj (C.getVert 3 : V) y :=
    deleteEdgeEndsGraph_degree_le_two_adj_left_or_right_of_min_degree_three
      (G := G) (x := x) (y := y) hmin (C.getVert 3)
      (hdegree_xy (C.getVert 3) h3_support)
  have h12G : G.Adj (C.getVert 1 : V) (C.getVert 2 : V) := by
    simpa [deleteEdgeEndsGraph] using h12
  have h23G : G.Adj (C.getVert 2 : V) (C.getVert 3 : V) := by
    simpa [deleteEdgeEndsGraph] using h23
  have h30G : G.Adj (C.getVert 3 : V) (C.getVert 0 : V) := by
    simpa [deleteEdgeEndsGraph] using h30
  have hA :=
    deleteEdgeEndsGraph_square_opposite_attachments_of_middle_degree_le_two
      (G := G) (x := x) (y := y)
      (a := C.getVert 0) (b := C.getVert 1) (c := C.getVert 2) (d := C.getVert 3)
      hxy h30 h01.ne h02 (by intro h; exact h13 h.symm)
      (by intro h; exact h23.ne h.symm)
      h0_attach h3_attach (fun z => hdegree_delete h12G z)
  have hB :=
    deleteEdgeEndsGraph_square_opposite_attachments_of_middle_degree_le_two
      (G := G) (x := x) (y := y)
      (a := C.getVert 1) (b := C.getVert 2) (c := C.getVert 3) (d := C.getVert 0)
      hxy h01 h12.ne h13 h02 (by intro h; exact h30.ne h.symm)
      h1_attach h0_attach (fun z => hdegree_delete h23G z)
  have hCalt :=
    deleteEdgeEndsGraph_square_opposite_attachments_of_middle_degree_le_two
      (G := G) (x := x) (y := y)
      (a := C.getVert 2) (b := C.getVert 3) (c := C.getVert 0) (d := C.getVert 1)
      hxy h12 h23.ne (by intro h; exact h02 h.symm) h13
      (by intro h; exact h01.ne h.symm)
      h2_attach h1_attach (fun z => hdegree_delete h30G z)
  rcases hA with hAleft | hAright
  · rcases hB with hBleft | hBright
    · exact False.elim (hAleft.2.1 hBleft.2.2.1)
    · rcases hCalt with hCleft | hCright
      · exact
          containsStrictSubdivision_K33_of_deleteEdgeEnds_cycle_length_four_alternating_getVert
            (G := G) C hC hxy hlen
            hAleft.1 hCleft.1 hBright.1 hAleft.2.2.1
      · exact False.elim (hBright.2.1 hCright.2.2.1)
  · rcases hB with hBleft | hBright
    · rcases hCalt with hCleft | hCright
      · exact False.elim (hBleft.2.1 hCleft.2.2.1)
      · exact
          containsStrictSubdivision_K33_of_deleteEdgeEnds_four_cycle_alternating_pair
            (G := G) hxy
            h01.symm h30.symm h23.symm h12.symm
            hBleft.1 hAright.2.2.1 hAright.1 hCright.1
            (by
              intro h
              exact h02 (Subtype.ext h))
            (by
              intro h
              exact h13 (Subtype.ext h))
    · exact False.elim (hAright.2.1 hBright.2.2.1)

/-- Source final-cycle `n = 4` contradiction.  The three square rotations force
the four cycle vertices to attach alternately to the two deleted endpoints,
and the existing direct `K_{3,3}` extraction closes the planar contradiction. -/
theorem not_isPlanar_of_deleteEdgeEnds_cycle_length_four_final
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hlen : C.length = 4)
    (hdegree_xy :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        z ∈ C.support -> (deleteEdgeEndsGraph G x y).degree z <= 2)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z <= 2) :
    False := by
  exact h_planar.no_K33_subdivision
    (containsStrictSubdivision_K33_of_deleteEdgeEnds_cycle_length_four_final
      (G := G) hmin C hC hxy hlen hdegree_xy hdegree_delete)

/-- Triangle final-cycle support control for the vertex `C[0]`: if the
deleted-end cycle spans `G - x - y` and has length three, then after deleting
`C[1]` and `C[2]`, every neighbour of the surviving copy of `C[0]` is one of
`x,y`. -/
theorem deleteEdgeEndsGraph_triangle_getVert_zero_neighbor_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hlen : C.length = 3)
    (hspanning : C.toSubgraph.verts = Set.univ)
    {aH w : {t : V | t ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)}}
    (haH : (aH : V) = (C.getVert 0 : V))
    (hw : (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).Adj aH w) :
    (w : V) = x ∨ (w : V) = y := by
  classical
  by_cases hwx : (w : V) = x
  · exact Or.inl hwx
  by_cases hwy : (w : V) = y
  · exact Or.inr hwy
  have hw_not_xy : (w : V) ∉ ({x, y} : Set V) := by
    simp [hwx, hwy]
  let wD : {t : V | t ∉ ({x, y} : Set V)} := ⟨w, hw_not_xy⟩
  have hw_support : wD ∈ C.support := by
    have hw_vert : wD ∈ C.toSubgraph.verts := by
      rw [hspanning]
      exact Set.mem_univ wD
    exact C.mem_verts_toSubgraph.mp hw_vert
  rcases Walk.support_subset_getVert012_of_length_eq_three
      (G := deleteEdgeEndsGraph G x y) C hlen hw_support with h0 | h1 | h2
  · have hw_eq_a : w = aH := by
      apply Subtype.ext
      have hw_val : (w : V) = (C.getVert 0 : V) := congrArg Subtype.val h0
      exact hw_val.trans haH.symm
    exact False.elim (hw.ne hw_eq_a.symm)
  · have hw_eq_b : (w : V) = (C.getVert 1 : V) := congrArg Subtype.val h1
    exact False.elim (w.2 (by simp [hw_eq_b]))
  · have hw_eq_c : (w : V) = (C.getVert 2 : V) := congrArg Subtype.val h2
    exact False.elim (w.2 (by simp [hw_eq_c]))

/-- Triangle final-cycle endpoint for `C[0]`: if `G - C[1] - C[2]` has
degree exactly two at the surviving copy of `C[0]`, then `C[0]` is adjacent to
both original deleted endpoints. -/
theorem deleteEdgeEndsGraph_triangle_getVert_zero_joined_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hlen : C.length = 3)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hdegree_middle :
      forall z : {w : V | w ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)},
        (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).degree z = 2) :
    G.Adj x (C.getVert 0 : V) ∧ G.Adj y (C.getVert 0 : V) := by
  classical
  have h01 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 0) (C.getVert 1) := by
    simpa using C.adj_getVert_succ (by omega : 0 < C.length)
  have h02 : C.getVert 0 ≠ C.getVert 2 := by
    simpa using
      SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one
        (p := C) hC (i := 1) (by omega : 1 <= C.length)
  have ha_not_bc : (C.getVert 0 : V) ∉
      ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact h01.ne (Subtype.ext h)
    · intro h
      exact h02 (Subtype.ext h)
  have hx_not_bc : x ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact (C.getVert 1).2 (Or.inl h.symm)
    · intro h
      exact (C.getVert 2).2 (Or.inl h.symm)
  have hy_not_bc : y ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact (C.getVert 1).2 (Or.inr h.symm)
    · intro h
      exact (C.getVert 2).2 (Or.inr h.symm)
  let aH : {t : V | t ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)} :=
    ⟨C.getVert 0, ha_not_bc⟩
  let xH : {t : V | t ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)} :=
    ⟨x, hx_not_bc⟩
  let yH : {t : V | t ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)} :=
    ⟨y, hy_not_bc⟩
  have hsub :
      (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).neighborSet aH ⊆
        ({xH, yH} :
          Set {t : V | t ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)}) := by
    intro w hw
    rcases
        deleteEdgeEndsGraph_triangle_getVert_zero_neighbor_endpoint
          (G := G) C hlen hspanning (aH := aH) (w := w)
          (by simp [aH]) hw with hwx | hwy
    · exact Or.inl (Subtype.ext hwx)
    · exact Or.inr (Subtype.ext hwy)
  have hsub_swap :
      (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).neighborSet aH ⊆
        ({yH, xH} :
          Set {t : V | t ∉ ({(C.getVert 1 : V), (C.getVert 2 : V)} : Set V)}) := by
    intro w hw
    rcases hsub hw with hwx | hwy
    · exact Or.inr hwx
    · exact Or.inl hwy
  have hayH :
      (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).Adj aH yH :=
    adj_other_of_degree_eq_two_neighborSet_subset_pair
      (H := deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V))
      (a := aH) (x := xH) (y := yH) (hdegree_middle aH) hsub
  have haxH :
      (deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V)).Adj aH xH :=
    adj_other_of_degree_eq_two_neighborSet_subset_pair
      (H := deleteEdgeEndsGraph G (C.getVert 1 : V) (C.getVert 2 : V))
      (a := aH) (x := yH) (y := xH) (hdegree_middle aH) hsub_swap
  exact
    ⟨by simpa [deleteEdgeEndsGraph, aH, xH] using haxH.symm,
     by simpa [deleteEdgeEndsGraph, aH, yH] using hayH.symm⟩

/-- Triangle final-cycle support control for the vertex `C[1]`: if the
deleted-end cycle spans `G - x - y` and has length three, then after deleting
`C[2]` and `C[0]`, every neighbour of the surviving copy of `C[1]` is one of
`x,y`. -/
theorem deleteEdgeEndsGraph_triangle_getVert_one_neighbor_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hlen : C.length = 3)
    (hspanning : C.toSubgraph.verts = Set.univ)
    {aH w : {t : V | t ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V)}}
    (haH : (aH : V) = (C.getVert 1 : V))
    (hw : (deleteEdgeEndsGraph G (C.getVert 2 : V) (C.getVert 0 : V)).Adj aH w) :
    (w : V) = x ∨ (w : V) = y := by
  classical
  by_cases hwx : (w : V) = x
  · exact Or.inl hwx
  by_cases hwy : (w : V) = y
  · exact Or.inr hwy
  have hw_not_xy : (w : V) ∉ ({x, y} : Set V) := by
    simp [hwx, hwy]
  let wD : {t : V | t ∉ ({x, y} : Set V)} := ⟨w, hw_not_xy⟩
  have hw_support : wD ∈ C.support := by
    have hw_vert : wD ∈ C.toSubgraph.verts := by
      rw [hspanning]
      exact Set.mem_univ wD
    exact C.mem_verts_toSubgraph.mp hw_vert
  rcases Walk.support_subset_getVert012_of_length_eq_three
      (G := deleteEdgeEndsGraph G x y) C hlen hw_support with h0 | h1 | h2
  · have hw_eq_c : (w : V) = (C.getVert 0 : V) := congrArg Subtype.val h0
    exact False.elim (w.2 (by simp [hw_eq_c]))
  · have hw_eq_a : w = aH := by
      apply Subtype.ext
      have hw_val : (w : V) = (C.getVert 1 : V) := congrArg Subtype.val h1
      exact hw_val.trans haH.symm
    exact False.elim (hw.ne hw_eq_a.symm)
  · have hw_eq_b : (w : V) = (C.getVert 2 : V) := congrArg Subtype.val h2
    exact False.elim (w.2 (by simp [hw_eq_b]))

/-- Triangle final-cycle endpoint for `C[1]`: if `G - C[2] - C[0]` has
degree exactly two at the surviving copy of `C[1]`, then `C[1]` is adjacent to
both original deleted endpoints. -/
theorem deleteEdgeEndsGraph_triangle_getVert_one_joined_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hlen : C.length = 3)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hdegree_middle :
      forall z : {w : V | w ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V)},
        (deleteEdgeEndsGraph G (C.getVert 2 : V) (C.getVert 0 : V)).degree z = 2) :
    G.Adj x (C.getVert 1 : V) ∧ G.Adj y (C.getVert 1 : V) := by
  classical
  have h01 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 0) (C.getVert 1) := by
    simpa using C.adj_getVert_succ (by omega : 0 < C.length)
  have h12 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 1) (C.getVert 2) := by
    simpa using C.adj_getVert_succ (i := 1) (by omega : 1 < C.length)
  have ha_not_bc : (C.getVert 1 : V) ∉
      ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact h12.ne (Subtype.ext h)
    · intro h
      exact h01.ne (Subtype.ext h.symm)
  have hx_not_bc : x ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact (C.getVert 2).2 (Or.inl h.symm)
    · intro h
      exact (C.getVert 0).2 (Or.inl h.symm)
  have hy_not_bc : y ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact (C.getVert 2).2 (Or.inr h.symm)
    · intro h
      exact (C.getVert 0).2 (Or.inr h.symm)
  let aH : {t : V | t ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V)} :=
    ⟨C.getVert 1, ha_not_bc⟩
  let xH : {t : V | t ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V)} :=
    ⟨x, hx_not_bc⟩
  let yH : {t : V | t ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V)} :=
    ⟨y, hy_not_bc⟩
  have hsub :
      (deleteEdgeEndsGraph G (C.getVert 2 : V) (C.getVert 0 : V)).neighborSet aH ⊆
        ({xH, yH} :
          Set {t : V | t ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V)}) := by
    intro w hw
    rcases
        deleteEdgeEndsGraph_triangle_getVert_one_neighbor_endpoint
          (G := G) C hlen hspanning (aH := aH) (w := w)
          (by simp [aH]) hw with hwx | hwy
    · exact Or.inl (Subtype.ext hwx)
    · exact Or.inr (Subtype.ext hwy)
  have hsub_swap :
      (deleteEdgeEndsGraph G (C.getVert 2 : V) (C.getVert 0 : V)).neighborSet aH ⊆
        ({yH, xH} :
          Set {t : V | t ∉ ({(C.getVert 2 : V), (C.getVert 0 : V)} : Set V)}) := by
    intro w hw
    rcases hsub hw with hwx | hwy
    · exact Or.inr hwx
    · exact Or.inl hwy
  have hayH :
      (deleteEdgeEndsGraph G (C.getVert 2 : V) (C.getVert 0 : V)).Adj aH yH :=
    adj_other_of_degree_eq_two_neighborSet_subset_pair
      (H := deleteEdgeEndsGraph G (C.getVert 2 : V) (C.getVert 0 : V))
      (a := aH) (x := xH) (y := yH) (hdegree_middle aH) hsub
  have haxH :
      (deleteEdgeEndsGraph G (C.getVert 2 : V) (C.getVert 0 : V)).Adj aH xH :=
    adj_other_of_degree_eq_two_neighborSet_subset_pair
      (H := deleteEdgeEndsGraph G (C.getVert 2 : V) (C.getVert 0 : V))
      (a := aH) (x := yH) (y := xH) (hdegree_middle aH) hsub_swap
  exact
    ⟨by simpa [deleteEdgeEndsGraph, aH, xH] using haxH.symm,
     by simpa [deleteEdgeEndsGraph, aH, yH] using hayH.symm⟩

/-- Triangle final-cycle support control for the vertex `C[2]`: if the
deleted-end cycle spans `G - x - y` and has length three, then after deleting
`C[0]` and `C[1]`, every neighbour of the surviving copy of `C[2]` is one of
`x,y`. -/
theorem deleteEdgeEndsGraph_triangle_getVert_two_neighbor_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hlen : C.length = 3)
    (hspanning : C.toSubgraph.verts = Set.univ)
    {aH w : {t : V | t ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V)}}
    (haH : (aH : V) = (C.getVert 2 : V))
    (hw : (deleteEdgeEndsGraph G (C.getVert 0 : V) (C.getVert 1 : V)).Adj aH w) :
    (w : V) = x ∨ (w : V) = y := by
  classical
  by_cases hwx : (w : V) = x
  · exact Or.inl hwx
  by_cases hwy : (w : V) = y
  · exact Or.inr hwy
  have hw_not_xy : (w : V) ∉ ({x, y} : Set V) := by
    simp [hwx, hwy]
  let wD : {t : V | t ∉ ({x, y} : Set V)} := ⟨w, hw_not_xy⟩
  have hw_support : wD ∈ C.support := by
    have hw_vert : wD ∈ C.toSubgraph.verts := by
      rw [hspanning]
      exact Set.mem_univ wD
    exact C.mem_verts_toSubgraph.mp hw_vert
  rcases Walk.support_subset_getVert012_of_length_eq_three
      (G := deleteEdgeEndsGraph G x y) C hlen hw_support with h0 | h1 | h2
  · have hw_eq_b : (w : V) = (C.getVert 0 : V) := congrArg Subtype.val h0
    exact False.elim (w.2 (by simp [hw_eq_b]))
  · have hw_eq_c : (w : V) = (C.getVert 1 : V) := congrArg Subtype.val h1
    exact False.elim (w.2 (by simp [hw_eq_c]))
  · have hw_eq_a : w = aH := by
      apply Subtype.ext
      have hw_val : (w : V) = (C.getVert 2 : V) := congrArg Subtype.val h2
      exact hw_val.trans haH.symm
    exact False.elim (hw.ne hw_eq_a.symm)

/-- Triangle final-cycle endpoint for `C[2]`: if `G - C[0] - C[1]` has
degree exactly two at the surviving copy of `C[2]`, then `C[2]` is adjacent to
both original deleted endpoints. -/
theorem deleteEdgeEndsGraph_triangle_getVert_two_joined_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hlen : C.length = 3)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hdegree_middle :
      forall z : {w : V | w ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V)},
        (deleteEdgeEndsGraph G (C.getVert 0 : V) (C.getVert 1 : V)).degree z = 2) :
    G.Adj x (C.getVert 2 : V) ∧ G.Adj y (C.getVert 2 : V) := by
  classical
  have h12 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 1) (C.getVert 2) := by
    simpa using C.adj_getVert_succ (i := 1) (by omega : 1 < C.length)
  have h02 : C.getVert 0 ≠ C.getVert 2 := by
    simpa using
      SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one
        (p := C) hC (i := 1) (by omega : 1 <= C.length)
  have ha_not_bc : (C.getVert 2 : V) ∉
      ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact h02 (Subtype.ext h.symm)
    · intro h
      exact h12.ne (Subtype.ext h.symm)
  have hx_not_bc : x ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact (C.getVert 0).2 (Or.inl h.symm)
    · intro h
      exact (C.getVert 1).2 (Or.inl h.symm)
  have hy_not_bc : y ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact (C.getVert 0).2 (Or.inr h.symm)
    · intro h
      exact (C.getVert 1).2 (Or.inr h.symm)
  let aH : {t : V | t ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V)} :=
    ⟨C.getVert 2, ha_not_bc⟩
  let xH : {t : V | t ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V)} :=
    ⟨x, hx_not_bc⟩
  let yH : {t : V | t ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V)} :=
    ⟨y, hy_not_bc⟩
  have hsub :
      (deleteEdgeEndsGraph G (C.getVert 0 : V) (C.getVert 1 : V)).neighborSet aH ⊆
        ({xH, yH} :
          Set {t : V | t ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V)}) := by
    intro w hw
    rcases
        deleteEdgeEndsGraph_triangle_getVert_two_neighbor_endpoint
          (G := G) C hlen hspanning (aH := aH) (w := w)
          (by simp [aH]) hw with hwx | hwy
    · exact Or.inl (Subtype.ext hwx)
    · exact Or.inr (Subtype.ext hwy)
  have hsub_swap :
      (deleteEdgeEndsGraph G (C.getVert 0 : V) (C.getVert 1 : V)).neighborSet aH ⊆
        ({yH, xH} :
          Set {t : V | t ∉ ({(C.getVert 0 : V), (C.getVert 1 : V)} : Set V)}) := by
    intro w hw
    rcases hsub hw with hwx | hwy
    · exact Or.inr hwx
    · exact Or.inl hwy
  have hayH :
      (deleteEdgeEndsGraph G (C.getVert 0 : V) (C.getVert 1 : V)).Adj aH yH :=
    adj_other_of_degree_eq_two_neighborSet_subset_pair
      (H := deleteEdgeEndsGraph G (C.getVert 0 : V) (C.getVert 1 : V))
      (a := aH) (x := xH) (y := yH) (hdegree_middle aH) hsub
  have haxH :
      (deleteEdgeEndsGraph G (C.getVert 0 : V) (C.getVert 1 : V)).Adj aH xH :=
    adj_other_of_degree_eq_two_neighborSet_subset_pair
      (H := deleteEdgeEndsGraph G (C.getVert 0 : V) (C.getVert 1 : V))
      (a := aH) (x := yH) (y := xH) (hdegree_middle aH) hsub_swap
  exact
    ⟨by simpa [deleteEdgeEndsGraph, aH, xH] using haxH.symm,
     by simpa [deleteEdgeEndsGraph, aH, yH] using hayH.symm⟩

/-- Source final-cycle `n = 3` constructive extraction.  If the deleted-end
cycle spans `G - x - y`, has length three, and each deletion by a cycle edge
leaves degree exactly two, all three triangle vertices are joined to both
`x` and `y`, giving a direct strict `K_5` subdivision. -/
theorem containsStrictSubdivision_K5_of_deleteEdgeEnds_cycle_length_three_final
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hlen : C.length = 3)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G := by
  classical
  have h01 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 0) (C.getVert 1) := by
    simpa using C.adj_getVert_succ (by omega : 0 < C.length)
  have h12 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 1) (C.getVert 2) := by
    simpa using C.adj_getVert_succ (i := 1) (by omega : 1 < C.length)
  have h20 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 2) (C.getVert 0) := by
    have hstep :
        (deleteEdgeEndsGraph G x y).Adj (C.getVert 2) (C.getVert 3) := by
      simpa [hlen] using C.adj_getVert_succ (i := 2) (by omega : 2 < C.length)
    change G.Adj (C.getVert 2 : V) (C.getVert 0 : V)
    have hstepG : G.Adj (C.getVert 2 : V) (C.getVert 3 : V) := by
      simpa [deleteEdgeEndsGraph] using hstep
    have h3r : (C.getVert 3 : V) = (r : V) := by
      have h3r_sub : C.getVert 3 = r := by
        rw [show 3 = C.length by omega, SimpleGraph.Walk.getVert_length]
      exact congrArg Subtype.val h3r_sub
    rw [SimpleGraph.Walk.getVert_zero]
    rw [h3r] at hstepG
    exact hstepG
  have h01G : G.Adj (C.getVert 0 : V) (C.getVert 1 : V) := by
    simpa [deleteEdgeEndsGraph] using h01
  have h12G : G.Adj (C.getVert 1 : V) (C.getVert 2 : V) := by
    simpa [deleteEdgeEndsGraph] using h12
  have h20G : G.Adj (C.getVert 2 : V) (C.getVert 0 : V) := by
    simpa [deleteEdgeEndsGraph] using h20
  have h0 :
      G.Adj x (C.getVert 0 : V) ∧ G.Adj y (C.getVert 0 : V) :=
    deleteEdgeEndsGraph_triangle_getVert_zero_joined_pair
      (G := G) C hC hlen hspanning (fun z => hdegree_delete h12G z)
  have h1 :
      G.Adj x (C.getVert 1 : V) ∧ G.Adj y (C.getVert 1 : V) :=
    deleteEdgeEndsGraph_triangle_getVert_one_joined_pair
      (G := G) C hlen hspanning (fun z => hdegree_delete h20G z)
  have h2 :
      G.Adj x (C.getVert 2 : V) ∧ G.Adj y (C.getVert 2 : V) :=
    deleteEdgeEndsGraph_triangle_getVert_two_joined_pair
      (G := G) C hC hlen hspanning (fun z => hdegree_delete h01G z)
  exact
    containsStrictSubdivision_K5_of_triangle_joined_pair
      (G := G) hxy h01G h12G h20G
      h0.1 h1.1 h2.1 h0.2 h1.2 h2.2

/-- Source final-cycle `n = 3` contradiction.  If the deleted-end cycle spans
`G - x - y`, has length three, and each deletion by a cycle edge leaves degree
exactly two, the constructive triangle extraction contradicts planarity. -/
theorem not_isPlanar_of_deleteEdgeEnds_cycle_length_three_final
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hlen : C.length = 3)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    False :=
  h_planar.no_K5_subdivision
    (containsStrictSubdivision_K5_of_deleteEdgeEnds_cycle_length_three_final
      (G := G) C hC hxy hlen hspanning hdegree_delete)

/-- Source final-cycle constructive extraction after the cycle/block
reductions.  This packages the three length branches of the
Makarychev/Skopenkov argument: length three gives `K_5`, length four gives the
alternating `K_{3,3}`, and length at least five is impossible. -/
theorem containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_spanning_cycle_final
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  have hlen_ge_three : 3 <= C.length := hC.three_le_length
  by_cases hlen3 : C.length = 3
  · exact Or.inl
      (containsStrictSubdivision_K5_of_deleteEdgeEnds_cycle_length_three_final
        (G := G) C hC hxy hlen3 hspanning hdegree_delete)
  by_cases hlen4 : C.length = 4
  · exact Or.inr
      (containsStrictSubdivision_K33_of_deleteEdgeEnds_cycle_length_four_final
        (G := G) hmin C hC hxy hlen4
        (fun z _hz => by
          have hzdeg := hdegree_delete hxy z
          omega)
        (fun {p q} hpq z => by
          have hzdeg := hdegree_delete hpq z
          omega))
  have hlen5 : 5 <= C.length := by omega
  have h12 :
      (deleteEdgeEndsGraph G x y).Adj (C.getVert 1) (C.getVert 2) := by
    simpa using C.adj_getVert_succ (i := 1) (by omega : 1 < C.length)
  have h12G : G.Adj (C.getVert 1 : V) (C.getVert 2 : V) := by
    simpa [deleteEdgeEndsGraph] using h12
  exact False.elim
    ((not_five_le_deleteEdgeEnds_cycle_length_of_middle_degree_le_two_min_degree_three
      (G := G) hmin C hC
      (fun z _hz => by
        have hzdeg := hdegree_delete hxy z
        omega)
      (fun z => by
        have hzdeg := hdegree_delete h12G z
        omega)) hlen5)

/-- Source final-cycle contradiction after the cycle/block reductions.  The
constructive final-cycle extraction contradicts the current Kuratowski
exclusion predicate. -/
theorem not_isPlanar_of_deleteEdgeEnds_spanning_cycle_final
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    (hmin : forall w : V, 3 <= G.degree w)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hspanning : C.toSubgraph.verts = Set.univ)
    (hdegree_delete :
      forall {p q : V}, G.Adj p q ->
        forall z : {w : V | w ∉ ({p, q} : Set V)},
          (deleteEdgeEndsGraph G p q).degree z = 2) :
    False := by
  rcases
      containsStrictSubdivision_K5_or_K33_of_deleteEdgeEnds_spanning_cycle_final
        (G := G) hmin C hC hxy hspanning hdegree_delete with
    hK5 | hK33
  · exact h_planar.no_K5_subdivision hK5
  · exact h_planar.no_K33_subdivision hK33


end FourColor

end Schematic.Math.GraphTheory
