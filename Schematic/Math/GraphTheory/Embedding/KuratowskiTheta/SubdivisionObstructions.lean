import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion
import Schematic.Math.GraphTheory.Planarity.Basic

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Final-cycle extraction with one subdivided triangle side.  If `a-b-c`
are consecutive on the deleted-end cycle, the third side of the triangle can
be the complementary `a`-`c` arc.  Together with two adjacent vertices `x,y`
joined to all three of `a,b,c`, this is a strict `K_5` subdivision with only
the source edge `2--4` subdivided. -/
theorem containsStrictSubdivision_K5_of_one_arc_joined_pair
    {V : Type u}
    {G : SimpleGraph V}
    {x y a b c : V}
    (pAC : G.Walk a c)
    (hxy : G.Adj x y)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hxa : G.Adj x a)
    (hxb : G.Adj x b)
    (hxc : G.Adj x c)
    (hya : G.Adj y a)
    (hyb : G.Adj y b)
    (hyc : G.Adj y c)
    (hac : a ≠ c)
    (hpAC : pAC.IsPath)
    (hno_x : forall {z : V}, z ∈ Walk.InternalVertices pAC -> z ≠ x)
    (hno_y : forall {z : V}, z ∈ Walk.InternalVertices pAC -> z ≠ y)
    (hno_b : forall {z : V}, z ∈ Walk.InternalVertices pAC -> z ≠ b) :
    ContainsStrictSubdivision K5Graph G := by
  classical
  let f : Fin 5 -> V := fun i =>
    match i with
    | 0 => x
    | 1 => y
    | 2 => a
    | 3 => b
    | 4 => c
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f] at hij ⊢
    all_goals
      first
      | rfl
      | exact False.elim (hxy.ne hij)
      | exact False.elim (hxy.ne hij.symm)
      | exact False.elim (hxa.ne hij)
      | exact False.elim (hxa.ne hij.symm)
      | exact False.elim (hxb.ne hij)
      | exact False.elim (hxb.ne hij.symm)
      | exact False.elim (hxc.ne hij)
      | exact False.elim (hxc.ne hij.symm)
      | exact False.elim (hya.ne hij)
      | exact False.elim (hya.ne hij.symm)
      | exact False.elim (hyb.ne hij)
      | exact False.elim (hyb.ne hij.symm)
      | exact False.elim (hyc.ne hij)
      | exact False.elim (hyc.ne hij.symm)
      | exact False.elim (hab.ne hij)
      | exact False.elim (hab.ne hij.symm)
      | exact False.elim (hac hij)
      | exact False.elim (hac hij.symm)
      | exact False.elim (hbc.ne hij)
      | exact False.elim (hbc.ne hij.symm)
  let e : Fin 5 ↪ V := {
    toFun := f
    inj' := hf_inj }
  let p : G.Walk (e 2) (e 4) := by
    simpa [e, f] using pAC
  have hp : p.IsPath := by
    simpa [p] using hpAC
  refine ⟨StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath
    (H := K5Graph) (G := G) e (a := (2 : Fin 5)) (b := (4 : Fin 5))
    p hp ?_ ?_⟩
  · intro i j hij hnot
    fin_cases i <;> fin_cases j <;>
      simp [K5Graph, CompleteGraphOn, e, f] at hij hnot ⊢
    all_goals
      first
      | contradiction
      | exact hxy
      | exact hxy.symm
      | exact hxa
      | exact hxa.symm
      | exact hxb
      | exact hxb.symm
      | exact hxc
      | exact hxc.symm
      | exact hya
      | exact hya.symm
      | exact hyb
      | exact hyb.symm
      | exact hyc
      | exact hyc.symm
      | exact hab
      | exact hab.symm
      | exact hbc
      | exact hbc.symm
  · intro z hz w hzw
    have hzAC : z ∈ Walk.InternalVertices pAC := by
      simpa [p] using hz
    fin_cases w <;> simp [e, f] at hzw
    · exact hno_x hzAC hzw
    · exact hno_y hzAC hzw
    · exact hzAC.2.1 hzw
    · exact hno_b hzAC hzw
    · exact hzAC.2.2 hzw

/-- Cycle form of `containsStrictSubdivision_K5_of_one_arc_joined_pair`.
The hypotheses `a--b` and `b--c` are the consecutive two-edge segment of the
cycle; the complementary `a`-`c` arc supplied by the cycle split is the single
subdivided source edge of the resulting `K_5`. -/
theorem containsStrictSubdivision_K5_of_cycle_consecutive_joined_pair
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x y a b c : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hc : c ∈ C.support)
    (hxy : G.Adj x y)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hxa : G.Adj x a)
    (hxb : G.Adj x b)
    (hxc : G.Adj x c)
    (hya : G.Adj y a)
    (hyb : G.Adj y b)
    (hyc : G.Adj y c)
    (hac : a ≠ c)
    (hx_cycle : x ∉ C.support)
    (hy_cycle : y ∉ C.support) :
    ContainsStrictSubdivision K5Graph G := by
  classical
  rcases
    Walk.IsCycle.exists_avoiding_path_and_split_through
      (G := G) C hC ha hc hb hac hab.ne.symm hbc.ne with
    ⟨pAC, _pAB, _pCB, hpAC, _hpAB, _hpCB,
      hpAC_support, _hpAB_support, _hpCB_support,
      hb_not_pAC, _hc_not_pAB, _ha_not_pCB,
      _hAC_AB, _hAC_CB, _hAB_CB⟩
  refine
    containsStrictSubdivision_K5_of_one_arc_joined_pair
      (G := G) pAC hxy hab hbc hxa hxb hxc hya hyb hyc
      hac hpAC ?_ ?_ ?_
  · intro z hz hzx
    exact hx_cycle (by simpa [hzx] using hpAC_support z hz.1)
  · intro z hz hzy
    exact hy_cycle (by simpa [hzy] using hpAC_support z hz.1)
  · intro z hz hzb
    exact hb_not_pAC (by simpa [hzb] using hz.1)

/-- Deleted-end form of the consecutive-cycle `K_5` extraction.  This is the
form used in the Makarychev/Skopenkov final-cycle branch: the cycle lives in
`G - x - y`, while the two deleted endpoints are restored as the two universal
vertices of the `K_5` subdivision. -/
theorem containsStrictSubdivision_K5_of_deleteEdgeEnds_cycle_consecutive_joined_pair
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {x y : V}
    {r a b c : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hc : c ∈ C.support)
    (hxy : G.Adj x y)
    (hab : (deleteEdgeEndsGraph G x y).Adj a b)
    (hbc : (deleteEdgeEndsGraph G x y).Adj b c)
    (hxa : G.Adj x (a : V))
    (hxb : G.Adj x (b : V))
    (hxc : G.Adj x (c : V))
    (hya : G.Adj y (a : V))
    (hyb : G.Adj y (b : V))
    (hyc : G.Adj y (c : V))
    (hac : (a : V) ≠ (c : V)) :
    ContainsStrictSubdivision K5Graph G := by
  classical
  let A : Set V := ({x, y} : Set V)ᶜ
  let φ := (SimpleGraph.Embedding.induce (G := G) A).toHom
  let CG : G.Walk (r : V) (r : V) := C.map φ
  have hCG : CG.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.map
      (p := C) (f := φ) (by
        intro u v huv
        exact Subtype.ext huv) hC
  have haG : (a : V) ∈ CG.support := by
    change (a : V) ∈ (C.map φ).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨a, ha, by simp [φ, A]⟩
  have hbG : (b : V) ∈ CG.support := by
    change (b : V) ∈ (C.map φ).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨b, hb, by simp [φ, A]⟩
  have hcG : (c : V) ∈ CG.support := by
    change (c : V) ∈ (C.map φ).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨c, hc, by simp [φ, A]⟩
  have hx_cycle : x ∉ CG.support := by
    intro hxmem
    change x ∈ (C.map φ).support at hxmem
    rw [SimpleGraph.Walk.support_map] at hxmem
    rcases List.mem_map.mp hxmem with ⟨z, _hz, hz_eq⟩
    have hzx : (z : V) = x := by
      simpa [φ, A] using hz_eq
    exact z.2 (by simp [hzx])
  have hy_cycle : y ∉ CG.support := by
    intro hymem
    change y ∈ (C.map φ).support at hymem
    rw [SimpleGraph.Walk.support_map] at hymem
    rcases List.mem_map.mp hymem with ⟨z, _hz, hz_eq⟩
    have hzy : (z : V) = y := by
      simpa [φ, A] using hz_eq
    exact z.2 (by simp [hzy])
  have habG : G.Adj (a : V) (b : V) := by
    simpa [deleteEdgeEndsGraph] using hab
  have hbcG : G.Adj (b : V) (c : V) := by
    simpa [deleteEdgeEndsGraph] using hbc
  exact
    containsStrictSubdivision_K5_of_cycle_consecutive_joined_pair
      (G := G) CG hCG haG hbG hcG hxy habG hbcG hxa hxb hxc hya hyb hyc
      hac hx_cycle hy_cycle

/-- Final-cycle extraction, triangle case.  If the deleted-end cycle has
three vertices and all three are adjacent to both deleted endpoints `x,y`,
then the five displayed vertices form a direct `K_5` strict subdivision. -/
theorem containsStrictSubdivision_K5_of_triangle_joined_pair
    {V : Type u}
    {G : SimpleGraph V}
    {x y a b c : V}
    (hxy : G.Adj x y)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hca : G.Adj c a)
    (hxa : G.Adj x a)
    (hxb : G.Adj x b)
    (hxc : G.Adj x c)
    (hya : G.Adj y a)
    (hyb : G.Adj y b)
    (hyc : G.Adj y c) :
    ContainsStrictSubdivision K5Graph G := by
  classical
  let f : Fin 5 -> V := fun i =>
    match i with
    | 0 => x
    | 1 => y
    | 2 => a
    | 3 => b
    | 4 => c
  have hf_adj : forall i j : Fin 5, i ≠ j -> G.Adj (f i) (f j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f] at hij ⊢
    all_goals
      first
      | exact False.elim (hij rfl)
      | exact hxy
      | exact hxy.symm
      | exact hab
      | exact hab.symm
      | exact hbc
      | exact hbc.symm
      | exact hca
      | exact hca.symm
      | exact hxa
      | exact hxa.symm
      | exact hxb
      | exact hxb.symm
      | exact hxc
      | exact hxc.symm
      | exact hya
      | exact hya.symm
      | exact hyb
      | exact hyb.symm
      | exact hyc
      | exact hyc.symm
  let e : Fin 5 ↪ V := {
    toFun := f
    inj' := by
      intro i j hij
      by_contra hne
      have hadj : G.Adj (f i) (f j) := hf_adj i j hne
      rw [hij] at hadj
      exact hadj.ne rfl }
  exact containsStrictSubdivision_completeGraph_of_cliqueEmbedding
    (G := G) e (by
      intro i j hij
      exact hf_adj i j hij)

/-- Final-cycle extraction, four-cycle alternating case.  The four cycle
vertices alternate between the two deleted endpoints, producing a direct
strict `K_{3,3}` subdivision with bipartition `{x,b,d}` and `{y,a,c}`. -/
theorem containsStrictSubdivision_K33_of_four_cycle_alternating_pair
    {V : Type u}
    {G : SimpleGraph V}
    {x y a b c d : V}
    (hxy : G.Adj x y)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hcd : G.Adj c d)
    (hda : G.Adj d a)
    (hxa : G.Adj x a)
    (hxc : G.Adj x c)
    (hyb : G.Adj y b)
    (hyd : G.Adj y d)
    (hxb : x ≠ b)
    (hxd : x ≠ d)
    (hbd : b ≠ d)
    (hya : y ≠ a)
    (hyc : y ≠ c)
    (hac : a ≠ c) :
    ContainsStrictSubdivision K33Graph G := by
  classical
  let f : K33Vertex -> V
    | Sum.inl 0 => x
    | Sum.inl 1 => b
    | Sum.inl 2 => d
    | Sum.inr 0 => y
    | Sum.inr 1 => a
    | Sum.inr 2 => c
  have hf_inj : Function.Injective f := by
    intro u v huv
    rcases u with i | i <;> rcases v with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [f] at huv ⊢
    all_goals
      first
      | rfl
      | exact False.elim (hxy.ne huv)
      | exact False.elim (hxy.ne huv.symm)
      | exact False.elim (hxa.ne huv)
      | exact False.elim (hxa.ne huv.symm)
      | exact False.elim (hxc.ne huv)
      | exact False.elim (hxc.ne huv.symm)
      | exact False.elim (hyb.ne huv)
      | exact False.elim (hyb.ne huv.symm)
      | exact False.elim (hyd.ne huv)
      | exact False.elim (hyd.ne huv.symm)
      | exact False.elim (hab.ne huv)
      | exact False.elim (hab.ne huv.symm)
      | exact False.elim (hbc.ne huv)
      | exact False.elim (hbc.ne huv.symm)
      | exact False.elim (hcd.ne huv)
      | exact False.elim (hcd.ne huv.symm)
      | exact False.elim (hda.ne huv)
      | exact False.elim (hda.ne huv.symm)
      | exact False.elim (hxb huv)
      | exact False.elim (hxb huv.symm)
      | exact False.elim (hxd huv)
      | exact False.elim (hxd huv.symm)
      | exact False.elim (hbd huv)
      | exact False.elim (hbd huv.symm)
      | exact False.elim (hya huv)
      | exact False.elim (hya huv.symm)
      | exact False.elim (hyc huv)
      | exact False.elim (hyc huv.symm)
      | exact False.elim (hac huv)
      | exact False.elim (hac huv.symm)
  let e : K33Vertex ↪ V := {
    toFun := f
    inj' := hf_inj }
  refine containsStrictSubdivision_of_graphEmbedding e ?_
  intro u v huv
  rcases u with i | i <;> rcases v with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [K33Graph] at huv ⊢
  all_goals
    first
    | exact False.elim huv
    | exact hxy
    | exact hxy.symm
    | exact hxa
    | exact hxa.symm
    | exact hxc
    | exact hxc.symm
    | exact hyb
    | exact hyb.symm
    | exact hyd
    | exact hyd.symm
    | exact hab
    | exact hab.symm
    | exact hbc
    | exact hbc.symm
    | exact hcd
    | exact hcd.symm
    | exact hda
    | exact hda.symm

/-- Deleted-end form of the four-cycle alternating extraction.  The cycle
edges live in `G - x - y`; restoring the deleted endpoints gives the direct
`K_{3,3}` model from the source proof's `n = 4` alternating case. -/
theorem containsStrictSubdivision_K33_of_deleteEdgeEnds_four_cycle_alternating_pair
    {V : Type u}
    {G : SimpleGraph V}
    {x y : V}
    {a b c d : {w : V | w ∉ ({x, y} : Set V)}}
    (hxy : G.Adj x y)
    (hab : (deleteEdgeEndsGraph G x y).Adj a b)
    (hbc : (deleteEdgeEndsGraph G x y).Adj b c)
    (hcd : (deleteEdgeEndsGraph G x y).Adj c d)
    (hda : (deleteEdgeEndsGraph G x y).Adj d a)
    (hxa : G.Adj x (a : V))
    (hxc : G.Adj x (c : V))
    (hyb : G.Adj y (b : V))
    (hyd : G.Adj y (d : V))
    (hbd : (b : V) ≠ (d : V))
    (hac : (a : V) ≠ (c : V)) :
    ContainsStrictSubdivision K33Graph G := by
  have habG : G.Adj (a : V) (b : V) := by
    simpa [deleteEdgeEndsGraph] using hab
  have hbcG : G.Adj (b : V) (c : V) := by
    simpa [deleteEdgeEndsGraph] using hbc
  have hcdG : G.Adj (c : V) (d : V) := by
    simpa [deleteEdgeEndsGraph] using hcd
  have hdaG : G.Adj (d : V) (a : V) := by
    simpa [deleteEdgeEndsGraph] using hda
  have hxb : x ≠ (b : V) := by
    intro h
    exact b.2 (by simp [h.symm])
  have hxd : x ≠ (d : V) := by
    intro h
    exact d.2 (by simp [h.symm])
  have hya : y ≠ (a : V) := by
    intro h
    exact a.2 (by simp [h.symm])
  have hyc : y ≠ (c : V) := by
    intro h
    exact c.2 (by simp [h.symm])
  exact
    containsStrictSubdivision_K33_of_four_cycle_alternating_pair
      (G := G) hxy habG hbcG hcdG hdaG hxa hxc hyb hyd
      hxb hxd hbd hya hyc hac

theorem not_isPlanar_of_triangle_joined_pair
    {V : Type u}
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {x y a b c : V}
    (hxy : G.Adj x y)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hca : G.Adj c a)
    (hxa : G.Adj x a)
    (hxb : G.Adj x b)
    (hxc : G.Adj x c)
    (hya : G.Adj y a)
    (hyb : G.Adj y b)
    (hyc : G.Adj y c) :
    False :=
  h_planar.no_K5_subdivision
    (containsStrictSubdivision_K5_of_triangle_joined_pair
      (G := G) hxy hab hbc hca hxa hxb hxc hya hyb hyc)

theorem not_isPlanar_of_cycle_consecutive_joined_pair
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {r x y a b c : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hc : c ∈ C.support)
    (hxy : G.Adj x y)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hxa : G.Adj x a)
    (hxb : G.Adj x b)
    (hxc : G.Adj x c)
    (hya : G.Adj y a)
    (hyb : G.Adj y b)
    (hyc : G.Adj y c)
    (hac : a ≠ c)
    (hx_cycle : x ∉ C.support)
    (hy_cycle : y ∉ C.support) :
    False :=
  h_planar.no_K5_subdivision
    (containsStrictSubdivision_K5_of_cycle_consecutive_joined_pair
      (G := G) C hC ha hb hc hxy hab hbc hxa hxb hxc hya hyb hyc
      hac hx_cycle hy_cycle)

theorem not_isPlanar_of_deleteEdgeEnds_cycle_consecutive_joined_pair
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {x y : V}
    {r a b c : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hc : c ∈ C.support)
    (hxy : G.Adj x y)
    (hab : (deleteEdgeEndsGraph G x y).Adj a b)
    (hbc : (deleteEdgeEndsGraph G x y).Adj b c)
    (hxa : G.Adj x (a : V))
    (hxb : G.Adj x (b : V))
    (hxc : G.Adj x (c : V))
    (hya : G.Adj y (a : V))
    (hyb : G.Adj y (b : V))
    (hyc : G.Adj y (c : V))
    (hac : (a : V) ≠ (c : V)) :
    False :=
  h_planar.no_K5_subdivision
    (containsStrictSubdivision_K5_of_deleteEdgeEnds_cycle_consecutive_joined_pair
      (G := G) C hC ha hb hc hxy hab hbc hxa hxb hxc hya hyb hyc hac)

/-- Source final-cycle branch: if the relevant consecutive triple on the
cycle in `G - x - y` consists entirely of vertices joined to both deleted
endpoints, then planarity of `G` is impossible by the one-arc `K_5`
extraction. -/
theorem not_isPlanar_of_deleteEdgeEnds_cycle_consecutive_all_joined_pair
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {x y : V}
    {r a b c : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hc : c ∈ C.support)
    (hxy : G.Adj x y)
    (hab : (deleteEdgeEndsGraph G x y).Adj a b)
    (hbc : (deleteEdgeEndsGraph G x y).Adj b c)
    (hac : (a : V) ≠ (c : V))
    (hall :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        z ∈ C.support -> G.Adj x (z : V) ∧ G.Adj y (z : V)) :
    False := by
  exact
    not_isPlanar_of_deleteEdgeEnds_cycle_consecutive_joined_pair
      (G := G) h_planar C hC ha hb hc hxy hab hbc
      (hall a ha).1 (hall b hb).1 (hall c hc).1
      (hall a ha).2 (hall b hb).2 (hall c hc).2 hac

/-- Source final-cycle all-joined branch without naming the consecutive
triple.  A simple cycle in `G - x - y` supplies a consecutive two-edge
segment; if every cycle vertex is joined to both deleted endpoints, the
preceding one-arc `K_5` extraction contradicts planarity. -/
theorem not_isPlanar_of_deleteEdgeEnds_cycle_all_joined_pair
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hall :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        z ∈ C.support -> G.Adj x (z : V) ∧ G.Adj y (z : V)) :
    False := by
  rcases Walk.IsCycle.exists_consecutive_triple
    (G := deleteEdgeEndsGraph G x y) C hC with
    ⟨a, b, c, ha, hb, hc, hab, hbc, hac_sub⟩
  have hac : (a : V) ≠ (c : V) := by
    intro hval
    exact hac_sub (Subtype.ext hval)
  exact
    not_isPlanar_of_deleteEdgeEnds_cycle_consecutive_all_joined_pair
      (G := G) h_planar C hC ha hb hc hxy hab hbc hac hall

/-- Branch-selection consequence of the all-joined final-cycle extraction: in
a planar graph, a deleted-end cycle cannot have every vertex adjacent to both
deleted endpoints. -/
theorem exists_cycle_vertex_not_adj_both_of_isPlanar_deleteEdgeEnds_cycle
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y) :
    Exists fun z : {w : V | w ∉ ({x, y} : Set V)} =>
      z ∈ C.support ∧ ¬ (G.Adj x (z : V) ∧ G.Adj y (z : V)) := by
  classical
  by_contra hnone
  have hall :
      forall z : {w : V | w ∉ ({x, y} : Set V)},
        z ∈ C.support -> G.Adj x (z : V) ∧ G.Adj y (z : V) := by
    intro z hz
    by_contra hnot
    exact hnone ⟨z, hz, hnot⟩
  exact
    not_isPlanar_of_deleteEdgeEnds_cycle_all_joined_pair
      (G := G) h_planar C hC hxy hall

theorem not_isPlanar_of_four_cycle_alternating_pair
    {V : Type u}
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {x y a b c d : V}
    (hxy : G.Adj x y)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hcd : G.Adj c d)
    (hda : G.Adj d a)
    (hxa : G.Adj x a)
    (hxc : G.Adj x c)
    (hyb : G.Adj y b)
    (hyd : G.Adj y d)
    (hxb : x ≠ b)
    (hxd : x ≠ d)
    (hbd : b ≠ d)
    (hya : y ≠ a)
    (hyc : y ≠ c)
    (hac : a ≠ c) :
    False :=
  h_planar.no_K33_subdivision
    (containsStrictSubdivision_K33_of_four_cycle_alternating_pair
      (G := G) hxy hab hbc hcd hda hxa hxc hyb hyd
      hxb hxd hbd hya hyc hac)

theorem not_isPlanar_of_deleteEdgeEnds_four_cycle_alternating_pair
    {V : Type u}
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {x y : V}
    {a b c d : {w : V | w ∉ ({x, y} : Set V)}}
    (hxy : G.Adj x y)
    (hab : (deleteEdgeEndsGraph G x y).Adj a b)
    (hbc : (deleteEdgeEndsGraph G x y).Adj b c)
    (hcd : (deleteEdgeEndsGraph G x y).Adj c d)
    (hda : (deleteEdgeEndsGraph G x y).Adj d a)
    (hxa : G.Adj x (a : V))
    (hxc : G.Adj x (c : V))
    (hyb : G.Adj y (b : V))
    (hyd : G.Adj y (d : V))
    (hbd : (b : V) ≠ (d : V))
    (hac : (a : V) ≠ (c : V)) :
    False :=
  h_planar.no_K33_subdivision
    (containsStrictSubdivision_K33_of_deleteEdgeEnds_four_cycle_alternating_pair
      (G := G) hxy hab hbc hcd hda hxa hxc hyb hyd hbd hac)

/-- Source final-cycle `n = 4` branch in indexed constructive form.  A
length-four cycle in `G - x - y`, with opposite vertices attached alternately
to the deleted endpoints, gives a direct strict `K_{3,3}` subdivision. -/
theorem containsStrictSubdivision_K33_of_deleteEdgeEnds_cycle_length_four_alternating_getVert
    {V : Type u}
    {G : SimpleGraph V}
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hlen : C.length = 4)
    (hx0 : G.Adj x (C.getVert 0 : V))
    (hx2 : G.Adj x (C.getVert 2 : V))
    (hy1 : G.Adj y (C.getVert 1 : V))
    (hy3 : G.Adj y (C.getVert 3 : V)) :
    ContainsStrictSubdivision K33Graph G := by
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
  have h13_sub : C.getVert 1 ≠ C.getVert 3 := by
    simpa using
      SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one
        (p := C) hC (i := 2) (by omega : 2 <= C.length)
  have h02_sub : C.getVert 0 ≠ C.getVert 2 := by
    simpa using
      SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one
        (p := C) hC (i := 1) (by omega : 1 <= C.length)
  have h13 : (C.getVert 1 : V) ≠ (C.getVert 3 : V) := by
    intro h
    exact h13_sub (Subtype.ext h)
  have h02 : (C.getVert 0 : V) ≠ (C.getVert 2 : V) := by
    intro h
    exact h02_sub (Subtype.ext h)
  exact
    containsStrictSubdivision_K33_of_deleteEdgeEnds_four_cycle_alternating_pair
      (G := G) hxy h01 h12 h23 h30 hx0 hx2 hy1 hy3 h13 h02

/-- Source final-cycle `n = 4` branch in indexed form.  A length-four cycle in
`G - x - y`, with opposite vertices attached alternately to the deleted
endpoints, immediately gives the `K_{3,3}` contradiction. -/
theorem not_isPlanar_of_deleteEdgeEnds_cycle_length_four_alternating_getVert
    {V : Type u}
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {x y : V}
    {r : {w : V | w ∉ ({x, y} : Set V)}}
    (C : (deleteEdgeEndsGraph G x y).Walk r r)
    (hC : C.IsCycle)
    (hxy : G.Adj x y)
    (hlen : C.length = 4)
    (hx0 : G.Adj x (C.getVert 0 : V))
    (hx2 : G.Adj x (C.getVert 2 : V))
    (hy1 : G.Adj y (C.getVert 1 : V))
    (hy3 : G.Adj y (C.getVert 3 : V)) :
    False := by
  exact h_planar.no_K33_subdivision
    (containsStrictSubdivision_K33_of_deleteEdgeEnds_cycle_length_four_alternating_getVert
      (G := G) C hC hxy hlen hx0 hx2 hy1 hy3)

/-- If an edge `xy` and two common neighbours `u,v` all survive deleting the
ends of another edge `pq`, then the deleted-end graph contains the
source-facing direct-edge theta.  This is the formal local object used in the
Makarychev Lemma 2 line: after two hanging vertices are adjacent to both
deleted endpoints, any edge disjoint from the four displayed vertices would
leave this theta in the corresponding `G - p - q`. -/
theorem containsEdgeTheta_deleteEdgeEndsGraph_of_edge_and_two_common_neighbors
    {V : Type u} {G : SimpleGraph V}
    {x y u v p q : V}
    (hx : x ∉ ({p, q} : Set V))
    (hy : y ∉ ({p, q} : Set V))
    (hu : u ∉ ({p, q} : Set V))
    (hv : v ∉ ({p, q} : Set V))
    (hxy : G.Adj x y)
    (hxu : G.Adj x u)
    (hyu : G.Adj y u)
    (hxv : G.Adj x v)
    (hyv : G.Adj y v)
    (huv : u ≠ v) :
    ContainsEdgeTheta (deleteEdgeEndsGraph G p q) := by
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨u, hu⟩, ⟨v, hv⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [deleteEdgeEndsGraph] using hxy
  · simpa [deleteEdgeEndsGraph] using hxu
  · simpa [deleteEdgeEndsGraph] using hyu
  · simpa [deleteEdgeEndsGraph] using hxv
  · simpa [deleteEdgeEndsGraph] using hyv
  · intro huv_sub
    exact huv (congrArg Subtype.val huv_sub)

theorem containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_and_two_common_neighbors
    {V : Type u} {G : SimpleGraph V}
    {x y u v p q : V}
    (hx : x ∉ ({p, q} : Set V))
    (hy : y ∉ ({p, q} : Set V))
    (hu : u ∉ ({p, q} : Set V))
    (hv : v ∉ ({p, q} : Set V))
    (hxy : G.Adj x y)
    (hxu : G.Adj x u)
    (hyu : G.Adj y u)
    (hxv : G.Adj x v)
    (hyv : G.Adj y v)
    (huv : u ≠ v) :
    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q) :=
  ContainsHomeomorphicTheta.of_edge
    (containsEdgeTheta_deleteEdgeEndsGraph_of_edge_and_two_common_neighbors
      (G := G) hx hy hu hv hxy hxu hyu hxv hyv huv)

/-- Deleted-end strict theta constructor for three common neighbours.  If two
vertices `a,b` have three distinct common neighbours `u,v,w`, all surviving the
deletion of `p,q`, then `G - p - q` contains a genuine `K_{2,3}` subdivision
with all six source edges unsplit.  This is the alternating-attachment pattern
in the source hanging-cycle argument. -/
theorem containsHomeomorphicTheta_deleteEdgeEndsGraph_of_three_common_neighbors
    {V : Type u} {G : SimpleGraph V}
    {a b u v w p q : V}
    (ha : a ∉ ({p, q} : Set V))
    (hb : b ∉ ({p, q} : Set V))
    (hu : u ∉ ({p, q} : Set V))
    (hv : v ∉ ({p, q} : Set V))
    (hw : w ∉ ({p, q} : Set V))
    (hau : G.Adj a u) (hbu : G.Adj b u)
    (hav : G.Adj a v) (hbv : G.Adj b v)
    (haw : G.Adj a w) (hbw : G.Adj b w)
    (hab : a ≠ b) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q) := by
  classical
  let A := {z : V | z ∉ ({p, q} : Set V)}
  let branch : K23Vertex -> A
    | Sum.inl 0 => ⟨a, ha⟩
    | Sum.inl 1 => ⟨b, hb⟩
    | Sum.inr 0 => ⟨u, hu⟩
    | Sum.inr 1 => ⟨v, hv⟩
    | Sum.inr 2 => ⟨w, hw⟩
  let emb : K23Vertex ↪ A := {
    toFun := branch
    inj' := by
      intro r s hrs
      rcases r with i | i <;> rcases s with j | j <;>
        fin_cases i <;> fin_cases j <;>
        simp [branch] at hrs ⊢
      all_goals
        first
        | exact False.elim (hab hrs)
        | exact False.elim (hab hrs.symm)
        | exact False.elim (hau.ne hrs)
        | exact False.elim (hau.ne hrs.symm)
        | exact False.elim (hav.ne hrs)
        | exact False.elim (hav.ne hrs.symm)
        | exact False.elim (haw.ne hrs)
        | exact False.elim (haw.ne hrs.symm)
        | exact False.elim (hbu.ne hrs)
        | exact False.elim (hbu.ne hrs.symm)
        | exact False.elim (hbv.ne hrs)
        | exact False.elim (hbv.ne hrs.symm)
        | exact False.elim (hbw.ne hrs)
        | exact False.elim (hbw.ne hrs.symm)
        | exact False.elim (huv hrs)
        | exact False.elim (huv hrs.symm)
        | exact False.elim (huw hrs)
        | exact False.elim (huw hrs.symm)
        | exact False.elim (hvw hrs)
        | exact False.elim (hvw hrs.symm) }
  have hadj :
      forall {r s : K23Vertex}, K23Graph.Adj r s ->
        (deleteEdgeEndsGraph G p q).Adj (emb r) (emb s) := by
    intro r s hrs
    rcases r with i | i <;> rcases s with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [K23Graph, emb, branch] at hrs ⊢
    all_goals
      first
      | simpa [deleteEdgeEndsGraph] using hau
      | simpa [deleteEdgeEndsGraph] using hbu
      | simpa [deleteEdgeEndsGraph] using hav
      | simpa [deleteEdgeEndsGraph] using hbv
      | simpa [deleteEdgeEndsGraph] using haw
      | simpa [deleteEdgeEndsGraph] using hbw
      | simpa [deleteEdgeEndsGraph] using hau.symm
      | simpa [deleteEdgeEndsGraph] using hbu.symm
      | simpa [deleteEdgeEndsGraph] using hav.symm
      | simpa [deleteEdgeEndsGraph] using hbv.symm
      | simpa [deleteEdgeEndsGraph] using haw.symm
      | simpa [deleteEdgeEndsGraph] using hbw.symm
  exact ContainsHomeomorphicTheta.of_strict
    ⟨StrictSubdivisionModel.ofGraphEmbedding emb hadj⟩

/-- Deleted-end theta constructor for a direct edge with one common neighbour
and a two-edge split tail.  The displayed paths are `a--b`, `a--t--b`, and
`a--z--w--b`, with the last path represented as `b--w--z` in the orientation
expected by `ContainsEdgeThetaSubdivision.of_common_neighbor_and_split_path`. -/
theorem containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_common_neighbor_two_edge_tail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {a b t z w p q : V}
    (ha : a ∉ ({p, q} : Set V))
    (hb : b ∉ ({p, q} : Set V))
    (ht : t ∉ ({p, q} : Set V))
    (hz : z ∉ ({p, q} : Set V))
    (hw : w ∉ ({p, q} : Set V))
    (hab : G.Adj a b)
    (hat : G.Adj a t)
    (hbt : G.Adj b t)
    (haz : G.Adj a z)
    (hbw : G.Adj b w)
    (hwz : G.Adj w z)
    (hab_ne : a ≠ b)
    (hat_ne : a ≠ t)
    (haz_ne : a ≠ z)
    (hbt_ne : b ≠ t)
    (hbz_ne : b ≠ z)
    (htz_ne : t ≠ z)
    (hwa_ne : w ≠ a)
    (hwb_ne : w ≠ b)
    (hwt_ne : w ≠ t)
    (hwz_ne : w ≠ z) :
    ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q) := by
  classical
  let A : Set V := ({p, q} : Set V)ᶜ
  let aA : A := ⟨a, ha⟩
  let bA : A := ⟨b, hb⟩
  let tA : A := ⟨t, ht⟩
  let zA : A := ⟨z, hz⟩
  let wA : A := ⟨w, hw⟩
  have habA : (deleteEdgeEndsGraph G p q).Adj aA bA := by
    simpa [deleteEdgeEndsGraph, A, aA, bA] using hab
  have hatA : (deleteEdgeEndsGraph G p q).Adj aA tA := by
    simpa [deleteEdgeEndsGraph, A, aA, tA] using hat
  have hbtA : (deleteEdgeEndsGraph G p q).Adj bA tA := by
    simpa [deleteEdgeEndsGraph, A, bA, tA] using hbt
  have hazA : (deleteEdgeEndsGraph G p q).Adj aA zA := by
    simpa [deleteEdgeEndsGraph, A, aA, zA] using haz
  have hbwA : (deleteEdgeEndsGraph G p q).Adj bA wA := by
    simpa [deleteEdgeEndsGraph, A, bA, wA] using hbw
  have hwzA : (deleteEdgeEndsGraph G p q).Adj wA zA := by
    simpa [deleteEdgeEndsGraph, A, wA, zA] using hwz
  have habA_ne : aA ≠ bA := by intro h; exact hab_ne (congrArg Subtype.val h)
  have hatA_ne : aA ≠ tA := by intro h; exact hat_ne (congrArg Subtype.val h)
  have hazA_ne : aA ≠ zA := by intro h; exact haz_ne (congrArg Subtype.val h)
  have hbtA_ne : bA ≠ tA := by intro h; exact hbt_ne (congrArg Subtype.val h)
  have hbzA_ne : bA ≠ zA := by intro h; exact hbz_ne (congrArg Subtype.val h)
  have htzA_ne : tA ≠ zA := by intro h; exact htz_ne (congrArg Subtype.val h)
  have hwaA_ne : wA ≠ aA := by intro h; exact hwa_ne (congrArg Subtype.val h)
  have hwbA_ne : wA ≠ bA := by intro h; exact hwb_ne (congrArg Subtype.val h)
  have hwtA_ne : wA ≠ tA := by intro h; exact hwt_ne (congrArg Subtype.val h)
  have hwzA_ne : wA ≠ zA := by intro h; exact hwz_ne (congrArg Subtype.val h)
  let pAB : (deleteEdgeEndsGraph G p q).Walk aA bA := habA.toWalk
  let pAZ : (deleteEdgeEndsGraph G p q).Walk aA zA := hazA.toWalk
  let pBZ : (deleteEdgeEndsGraph G p q).Walk bA zA :=
    hbwA.toWalk.append hwzA.toWalk
  have hpBZ : pBZ.IsPath := by
    refine Walk.edge_append_isPath hbwA (SimpleGraph.Walk.IsPath.of_adj hwzA) ?_
    intro hbmem
    have hbmem_list : bA ∈ [wA, zA] := by
      exact hbmem
    have hbmem' : bA = wA ∨ bA = zA ∨ bA ∈ ([] : List A) := by
      simpa only [List.mem_cons, List.mem_singleton] using hbmem_list
    rcases hbmem' with hbw' | hbz_or_nil
    · exact hwbA_ne hbw'.symm
    · rcases hbz_or_nil with hbz' | hnil
      · exact hbzA_ne hbz'
      · cases hnil
  have hnoAB :
      forall {r : A}, r ∈ Walk.InternalVertices pAB ->
        forall c : EdgeThetaVertex, r ≠ edgeThetaBranch aA bA tA zA c := by
    intro r hr c
    exact (Walk.not_mem_internalVertices_toWalk habA hr).elim
  have hnoAZ :
      forall {r : A}, r ∈ Walk.InternalVertices pAZ ->
        forall c : EdgeThetaVertex, r ≠ edgeThetaBranch aA bA tA zA c := by
    intro r hr c
    exact (Walk.not_mem_internalVertices_toWalk hazA hr).elim
  have hnoBZ :
      forall {r : A}, r ∈ Walk.InternalVertices pBZ ->
        forall c : EdgeThetaVertex, r ≠ edgeThetaBranch aA bA tA zA c := by
    intro r hr c
    have hrw : r = wA := by
      simpa [pBZ] using
        (Walk.mem_internalVertices_two_edge_toWalk_iff hbwA hwzA).mp hr
    intro hbranch
    have hw_branch : wA = edgeThetaBranch aA bA tA zA c := by
      simpa [hrw] using hbranch
    fin_cases c <;> simp [edgeThetaBranch] at hw_branch
    · exact hwaA_ne hw_branch
    · exact hwbA_ne hw_branch
    · exact hwtA_ne hw_branch
    · exact hwzA_ne hw_branch
  have hAB_AZ :
      Disjoint (Walk.InternalVertices pAB) (Walk.InternalVertices pAZ) := by
    rw [Set.disjoint_left]
    intro r hr _
    exact (Walk.not_mem_internalVertices_toWalk habA hr).elim
  have hAB_BZ :
      Disjoint (Walk.InternalVertices pAB) (Walk.InternalVertices pBZ) := by
    rw [Set.disjoint_left]
    intro r hr _
    exact (Walk.not_mem_internalVertices_toWalk habA hr).elim
  have hAZ_BZ :
      Disjoint (Walk.InternalVertices pAZ) (Walk.InternalVertices pBZ) := by
    rw [Set.disjoint_left]
    intro r hr _
    exact (Walk.not_mem_internalVertices_toWalk hazA hr).elim
  exact
    ContainsHomeomorphicTheta.of_edgeSubdivision
      (ContainsEdgeThetaSubdivision.of_common_neighbor_and_split_path
        (G := deleteEdgeEndsGraph G p q)
        pAB pAZ pBZ hatA hbtA
        habA_ne hatA_ne hazA_ne hbtA_ne hbzA_ne htzA_ne
        (SimpleGraph.Walk.IsPath.of_adj habA)
        (SimpleGraph.Walk.IsPath.of_adj hazA) hpBZ
        hnoAB hnoAZ hnoBZ hAB_AZ hAB_BZ hAZ_BZ)

/-- If every two-end deletion is homeomorphic-theta-free, no edge can be
disjoint from a displayed direct-edge theta. -/
theorem no_edge_disjoint_from_edge_theta_of_forall_deleteEdgeEnds_no_homeomorphicTheta
    {V : Type u} {G : SimpleGraph V}
    (hno :
      forall {p q : V} (_hpq : G.Adj p q),
        Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    {x y u v p q : V}
    (hpq : G.Adj p q)
    (hx : x ∉ ({p, q} : Set V))
    (hy : y ∉ ({p, q} : Set V))
    (hu : u ∉ ({p, q} : Set V))
    (hv : v ∉ ({p, q} : Set V))
    (hxy : G.Adj x y)
    (hxu : G.Adj x u)
    (hyu : G.Adj y u)
    (hxv : G.Adj x v)
    (hyv : G.Adj y v)
    (huv : u ≠ v) :
    False :=
  hno hpq
    (containsHomeomorphicTheta_deleteEdgeEndsGraph_of_edge_and_two_common_neighbors
      (G := G) hx hy hu hv hxy hxu hyu hxv hyv huv)


end FourColor

end Schematic.Math.GraphTheory
