import Schematic.Math.GraphTheory.Subdivisions.Theta

/-! Suppressed-edge theta models built from explicit paths. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

/-- Branch-vertex assignment for the four-vertex suppressed-edge theta. The
two `inl` vertices are the degree-three ends, and the two `inr` vertices are
the suppressed branch vertices on the other two theta branches. -/
def edgeThetaBranch {V : Type v} (x y u w : V) :
    EdgeThetaVertex -> V
  | Sum.inl 0 => x
  | Sum.inl 1 => y
  | Sum.inr 0 => u
  | Sum.inr 1 => w

/-- The four displayed vertices give an injective branch map for
`EdgeThetaGraph` when they are pairwise distinct. -/
theorem edgeThetaBranch_injective
    {V : Type v} {x y u w : V}
    (hxy : x ≠ y) (hxu : x ≠ u) (hxw : x ≠ w)
    (hyu : y ≠ u) (hyw : y ≠ w) (huw : u ≠ w) :
    Function.Injective (edgeThetaBranch x y u w) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [edgeThetaBranch] at hab ⊢
  all_goals
    first
    | exact False.elim (hxy hab)
    | exact False.elim (hxy hab.symm)
    | exact False.elim (hxu hab)
    | exact False.elim (hxu hab.symm)
    | exact False.elim (hxw hab)
    | exact False.elim (hxw hab.symm)
    | exact False.elim (hyu hab)
    | exact False.elim (hyu hab.symm)
    | exact False.elim (hyw hab)
    | exact False.elim (hyw hab.symm)
    | exact False.elim (huw hab)
    | exact False.elim (huw hab.symm)

/-- Labels for the five undirected edges of `EdgeThetaGraph`. -/
inductive EdgeThetaPathLabel where
  | xy | xu | yu | xw | yw
  deriving DecidableEq

/-- The five source-edge paths of an `EdgeThetaGraph` model, oriented according
to the source edge requested by Lean.  This is the reusable constructor
interface for the source argument: one branch between the degree-three ends and
two further branches split at `u` and `w`. -/
noncomputable def edgeThetaFivePath
    {V : Type v} {G : SimpleGraph V}
    {x y u w : V}
    (pXY : G.Walk x y)
    (pXU : G.Walk x u)
    (pYU : G.Walk y u)
    (pXW : G.Walk x w)
    (pYW : G.Walk y w) :
    forall {a b : EdgeThetaVertex}, EdgeThetaGraph.Adj a b ->
      G.Walk (edgeThetaBranch x y u w a)
        (edgeThetaBranch x y u w b)
  | Sum.inl 0, Sum.inl 0, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inl 0, Sum.inl 1, _hab => pXY
  | Sum.inl 1, Sum.inl 0, _hab => pXY.reverse
  | Sum.inl 1, Sum.inl 1, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inl 0, Sum.inr 0, _hab => pXU
  | Sum.inl 0, Sum.inr 1, _hab => pXW
  | Sum.inl 1, Sum.inr 0, _hab => pYU
  | Sum.inl 1, Sum.inr 1, _hab => pYW
  | Sum.inr 0, Sum.inl 0, _hab => pXU.reverse
  | Sum.inr 0, Sum.inl 1, _hab => pYU.reverse
  | Sum.inr 1, Sum.inl 0, _hab => pXW.reverse
  | Sum.inr 1, Sum.inl 1, _hab => pYW.reverse
  | Sum.inr 0, Sum.inr 0, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inr 0, Sum.inr 1, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inr 1, Sum.inr 0, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inr 1, Sum.inr 1, hab => False.elim (by simp [EdgeThetaGraph] at hab)

/-- The undirected label of a source edge in `EdgeThetaGraph`. -/
def edgeThetaPathLabel :
    forall {a b : EdgeThetaVertex}, EdgeThetaGraph.Adj a b ->
      EdgeThetaPathLabel
  | Sum.inl 0, Sum.inl 0, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inl 0, Sum.inl 1, _hab => EdgeThetaPathLabel.xy
  | Sum.inl 1, Sum.inl 0, _hab => EdgeThetaPathLabel.xy
  | Sum.inl 1, Sum.inl 1, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inl 0, Sum.inr 0, _hab => EdgeThetaPathLabel.xu
  | Sum.inl 0, Sum.inr 1, _hab => EdgeThetaPathLabel.xw
  | Sum.inl 1, Sum.inr 0, _hab => EdgeThetaPathLabel.yu
  | Sum.inl 1, Sum.inr 1, _hab => EdgeThetaPathLabel.yw
  | Sum.inr 0, Sum.inl 0, _hab => EdgeThetaPathLabel.xu
  | Sum.inr 0, Sum.inl 1, _hab => EdgeThetaPathLabel.yu
  | Sum.inr 1, Sum.inl 0, _hab => EdgeThetaPathLabel.xw
  | Sum.inr 1, Sum.inl 1, _hab => EdgeThetaPathLabel.yw
  | Sum.inr 0, Sum.inr 0, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inr 0, Sum.inr 1, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inr 1, Sum.inr 0, hab => False.elim (by simp [EdgeThetaGraph] at hab)
  | Sum.inr 1, Sum.inr 1, hab => False.elim (by simp [EdgeThetaGraph] at hab)

/-- The internal-vertex set corresponding to one of the five displayed paths. -/
def edgeThetaPathInternalSet
    {V : Type v} {G : SimpleGraph V}
    {x y u w : V}
    (pXY : G.Walk x y)
    (pXU : G.Walk x u)
    (pYU : G.Walk y u)
    (pXW : G.Walk x w)
    (pYW : G.Walk y w) :
    EdgeThetaPathLabel -> Set V
  | EdgeThetaPathLabel.xy => Walk.InternalVertices pXY
  | EdgeThetaPathLabel.xu => Walk.InternalVertices pXU
  | EdgeThetaPathLabel.yu => Walk.InternalVertices pYU
  | EdgeThetaPathLabel.xw => Walk.InternalVertices pXW
  | EdgeThetaPathLabel.yw => Walk.InternalVertices pYW

/-- The source-edge label records exactly which of the five host paths
`edgeThetaFivePath` uses; reversed source edges have the same internal set. -/
theorem edgeThetaFivePath_internalVertices_eq
    {V : Type v} {G : SimpleGraph V}
    {x y u w : V}
    {pXY : G.Walk x y}
    {pXU : G.Walk x u}
    {pYU : G.Walk y u}
    {pXW : G.Walk x w}
    {pYW : G.Walk y w}
    {a b : EdgeThetaVertex} (hab : EdgeThetaGraph.Adj a b) :
    Walk.InternalVertices
      (edgeThetaFivePath pXY pXU pYU pXW pYW hab) =
        edgeThetaPathInternalSet pXY pXU pYU pXW pYW
          (edgeThetaPathLabel hab) := by
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [EdgeThetaGraph, edgeThetaFivePath, edgeThetaPathLabel,
      edgeThetaPathInternalSet] at hab ⊢
  all_goals
    first
    | rfl
    | exact Walk.internalVertices_reverse _

/-- Equal labels in `EdgeThetaGraph` are the same undirected source edge. -/
theorem edgeThetaPathLabel_eq_imp_same_or_reverse
    {a b a' b' : EdgeThetaVertex}
    {hab : EdgeThetaGraph.Adj a b}
    {ha'b' : EdgeThetaGraph.Adj a' b'}
    (hlabel : edgeThetaPathLabel hab = edgeThetaPathLabel ha'b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  rcases a with a | a <;> rcases b with b | b <;>
    rcases a' with a' | a' <;> rcases b' with b' | b' <;>
    fin_cases a <;> fin_cases b <;>
    fin_cases a' <;> fin_cases b' <;>
    simp [EdgeThetaGraph, edgeThetaPathLabel] at hab ha'b' hlabel ⊢

/-- Finite-case path proof for `edgeThetaFivePath`. -/
theorem edgeThetaFivePath_isPath
    {V : Type v} {G : SimpleGraph V}
    {x y u w : V}
    {pXY : G.Walk x y}
    {pXU : G.Walk x u}
    {pYU : G.Walk y u}
    {pXW : G.Walk x w}
    {pYW : G.Walk y w}
    (hXY : pXY.IsPath) (hXU : pXU.IsPath) (hYU : pYU.IsPath)
    (hXW : pXW.IsPath) (hYW : pYW.IsPath) :
    forall {a b : EdgeThetaVertex} (hab : EdgeThetaGraph.Adj a b),
      (edgeThetaFivePath pXY pXU pYU pXW pYW hab).IsPath := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [EdgeThetaGraph, edgeThetaFivePath] at hab ⊢
  · exact hXY
  · exact hXY.reverse
  · exact hXU
  · exact hXW
  · exact hYU
  · exact hYW
  · exact hXU.reverse
  · exact hYU.reverse
  · exact hXW.reverse
  · exact hYW.reverse

/-- Finite-case reduction of the no-internal-branch condition for
`edgeThetaFivePath` to the five displayed host paths. -/
theorem edgeThetaFivePath_no_internal_branch
    {V : Type v} {G : SimpleGraph V}
    {x y u w : V}
    {pXY : G.Walk x y}
    {pXU : G.Walk x u}
    {pYU : G.Walk y u}
    {pXW : G.Walk x w}
    {pYW : G.Walk y w}
    (hXY :
      forall {z : V}, z ∈ Walk.InternalVertices pXY ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hXU :
      forall {z : V}, z ∈ Walk.InternalVertices pXU ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hYU :
      forall {z : V}, z ∈ Walk.InternalVertices pYU ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hXW :
      forall {z : V}, z ∈ Walk.InternalVertices pXW ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hYW :
      forall {z : V}, z ∈ Walk.InternalVertices pYW ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c) :
    forall {a b : EdgeThetaVertex} (hab : EdgeThetaGraph.Adj a b) {z : V},
      z ∈ Walk.InternalVertices
        (edgeThetaFivePath pXY pXU pYU pXW pYW hab) ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c := by
  intro a b hab z hz c
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [EdgeThetaGraph, edgeThetaFivePath] at hab hz ⊢
  · exact hXY hz c
  · exact hXY ((Walk.mem_internalVertices_reverse_iff pXY).1 hz) c
  · exact hXU hz c
  · exact hXW hz c
  · exact hYU hz c
  · exact hYW hz c
  · exact hXU ((Walk.mem_internalVertices_reverse_iff pXU).1 hz) c
  · exact hYU ((Walk.mem_internalVertices_reverse_iff pYU).1 hz) c
  · exact hXW ((Walk.mem_internalVertices_reverse_iff pXW).1 hz) c
  · exact hYW ((Walk.mem_internalVertices_reverse_iff pYW).1 hz) c

/-- Finite-case reduction of internal disjointness for `edgeThetaFivePath` to
pairwise disjointness of the five displayed host paths. -/
theorem edgeThetaFivePath_internally_disjoint
    {V : Type v} {G : SimpleGraph V}
    {x y u w : V}
    {pXY : G.Walk x y}
    {pXU : G.Walk x u}
    {pYU : G.Walk y u}
    {pXW : G.Walk x w}
    {pYW : G.Walk y w}
    (hdisj :
      forall {L M : EdgeThetaPathLabel}, L ≠ M ->
        Disjoint
          (edgeThetaPathInternalSet pXY pXU pYU pXW pYW L)
          (edgeThetaPathInternalSet pXY pXU pYU pXW pYW M)) :
    forall {a b a' b' : EdgeThetaVertex}
      (hab : EdgeThetaGraph.Adj a b) (ha'b' : EdgeThetaGraph.Adj a' b'),
        Not ((a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) ->
          Disjoint
            (Walk.InternalVertices
              (edgeThetaFivePath pXY pXU pYU pXW pYW hab))
            (Walk.InternalVertices
              (edgeThetaFivePath pXY pXU pYU pXW pYW ha'b')) := by
  intro a b a' b' hab ha'b' hne
  rw [edgeThetaFivePath_internalVertices_eq (pXY := pXY) (pXU := pXU)
      (pYU := pYU) (pXW := pXW) (pYW := pYW) hab,
    edgeThetaFivePath_internalVertices_eq (pXY := pXY) (pXU := pXU)
      (pYU := pYU) (pXW := pXW) (pYW := pYW) ha'b']
  exact hdisj (by
    intro hlabel
    exact hne (edgeThetaPathLabel_eq_imp_same_or_reverse hlabel))

/-- Build a strict suppressed-edge theta subdivision from five path branches.
The hypotheses are exactly the strict-subdivision side conditions: branch
vertices are injective, every displayed path is simple, no displayed path has
an internal branch vertex, and distinct source edges have disjoint internal
vertices. -/
theorem ContainsEdgeThetaSubdivision.of_five_paths
    {V : Type v} {G : SimpleGraph V}
    {x y u w : V}
    (pXY : G.Walk x y)
    (pXU : G.Walk x u)
    (pYU : G.Walk y u)
    (pXW : G.Walk x w)
    (pYW : G.Walk y w)
    (hinj : Function.Injective (edgeThetaBranch x y u w))
    (hpath :
      forall {a b : EdgeThetaVertex} (hab : EdgeThetaGraph.Adj a b),
        (edgeThetaFivePath pXY pXU pYU pXW pYW hab).IsPath)
    (hno_branch :
      forall {a b : EdgeThetaVertex} (hab : EdgeThetaGraph.Adj a b) {z : V},
        z ∈ Walk.InternalVertices
          (edgeThetaFivePath pXY pXU pYU pXW pYW hab) ->
          forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hdisjoint :
      forall {a b a' b' : EdgeThetaVertex}
        (hab : EdgeThetaGraph.Adj a b) (ha'b' : EdgeThetaGraph.Adj a' b'),
          Not ((a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) ->
            Disjoint
              (Walk.InternalVertices
                (edgeThetaFivePath pXY pXU pYU pXW pYW hab))
              (Walk.InternalVertices
                (edgeThetaFivePath pXY pXU pYU pXW pYW ha'b'))) :
    ContainsEdgeThetaSubdivision G := by
  classical
  exact ⟨{
    toSubdivisionModel := {
      branchVertex := edgeThetaBranch x y u w
      branchVertex_injective := hinj
      edgePath := edgeThetaFivePath pXY pXU pYU pXW pYW
      edgePath_isPath := hpath
      no_internal_branch_vertices := True
      internally_disjoint_edge_paths := True }
    no_internal_branch_vertices' := hno_branch
    internally_disjoint_edge_paths' := hdisjoint }⟩

/-- A concrete five-path constructor for a suppressed-edge theta subdivision.
This packages the finite source-graph bookkeeping, leaving only the actual host
path facts as hypotheses. -/
theorem ContainsEdgeThetaSubdivision.of_five_paths_explicit
    {V : Type v} {G : SimpleGraph V}
    {x y u w : V}
    (pXY : G.Walk x y)
    (pXU : G.Walk x u)
    (pYU : G.Walk y u)
    (pXW : G.Walk x w)
    (pYW : G.Walk y w)
    (hxy : x ≠ y) (hxu : x ≠ u) (hxw : x ≠ w)
    (hyu : y ≠ u) (hyw : y ≠ w) (huw : u ≠ w)
    (hXY : pXY.IsPath) (hXU : pXU.IsPath) (hYU : pYU.IsPath)
    (hXW : pXW.IsPath) (hYW : pYW.IsPath)
    (hnoXY :
      forall {z : V}, z ∈ Walk.InternalVertices pXY ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hnoXU :
      forall {z : V}, z ∈ Walk.InternalVertices pXU ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hnoYU :
      forall {z : V}, z ∈ Walk.InternalVertices pYU ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hnoXW :
      forall {z : V}, z ∈ Walk.InternalVertices pXW ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hnoYW :
      forall {z : V}, z ∈ Walk.InternalVertices pYW ->
        forall c : EdgeThetaVertex, z ≠ edgeThetaBranch x y u w c)
    (hdisj :
      forall {L M : EdgeThetaPathLabel}, L ≠ M ->
        Disjoint
          (edgeThetaPathInternalSet pXY pXU pYU pXW pYW L)
          (edgeThetaPathInternalSet pXY pXU pYU pXW pYW M)) :
    ContainsEdgeThetaSubdivision G :=
  ContainsEdgeThetaSubdivision.of_five_paths
    pXY pXU pYU pXW pYW
    (edgeThetaBranch_injective hxy hxu hxw hyu hyw huw)
    (edgeThetaFivePath_isPath hXY hXU hYU hXW hYW)
    (edgeThetaFivePath_no_internal_branch hnoXY hnoXU hnoYU hnoXW hnoYW)
    (edgeThetaFivePath_internally_disjoint hdisj)

/-- Two internally disjoint `a`-`b` branches, one split at `z`, together with
a common neighbour `t` of `a` and `b`, form a suppressed-edge theta
subdivision.  This is the local constructor used by the Makarychev Lemma 3
end-block line after a cycle is split into two arcs. -/
theorem ContainsEdgeThetaSubdivision.of_common_neighbor_and_split_path
    {V : Type v} {G : SimpleGraph V}
    {a b t z : V}
    (pAB : G.Walk a b)
    (pAZ : G.Walk a z)
    (pBZ : G.Walk b z)
    (hat : G.Adj a t)
    (hbt : G.Adj b t)
    (hab : a ≠ b) (hat_ne : a ≠ t) (haz : a ≠ z)
    (hbt_ne : b ≠ t) (hbz : b ≠ z) (htz : t ≠ z)
    (hAB : pAB.IsPath) (hAZ : pAZ.IsPath) (hBZ : pBZ.IsPath)
    (hnoAB :
      forall {r : V}, r ∈ Walk.InternalVertices pAB ->
        forall c : EdgeThetaVertex, r ≠ edgeThetaBranch a b t z c)
    (hnoAZ :
      forall {r : V}, r ∈ Walk.InternalVertices pAZ ->
        forall c : EdgeThetaVertex, r ≠ edgeThetaBranch a b t z c)
    (hnoBZ :
      forall {r : V}, r ∈ Walk.InternalVertices pBZ ->
        forall c : EdgeThetaVertex, r ≠ edgeThetaBranch a b t z c)
    (hAB_AZ :
      Disjoint (Walk.InternalVertices pAB) (Walk.InternalVertices pAZ))
    (hAB_BZ :
      Disjoint (Walk.InternalVertices pAB) (Walk.InternalVertices pBZ))
    (hAZ_BZ :
      Disjoint (Walk.InternalVertices pAZ) (Walk.InternalVertices pBZ)) :
    ContainsEdgeThetaSubdivision G := by
  classical
  refine
    ContainsEdgeThetaSubdivision.of_five_paths_explicit
      pAB hat.toWalk hbt.toWalk pAZ pBZ
      hab hat_ne haz hbt_ne hbz htz
      hAB (SimpleGraph.Walk.IsPath.of_adj hat) (SimpleGraph.Walk.IsPath.of_adj hbt)
      hAZ hBZ
      hnoAB ?_ ?_ hnoAZ hnoBZ ?_
  · intro r hr c
    exact (Walk.not_mem_internalVertices_toWalk hat hr).elim
  · intro r hr c
    exact (Walk.not_mem_internalVertices_toWalk hbt hr).elim
  · intro L M hLM
    rcases L <;> rcases M <;>
      simp [edgeThetaPathInternalSet] at hLM ⊢
    all_goals
      rw [Set.disjoint_left]
      intro r hrL hrR
      first
      | exact (Walk.not_mem_internalVertices_toWalk hat hrL).elim
      | exact (Walk.not_mem_internalVertices_toWalk hat hrR).elim
      | exact (Walk.not_mem_internalVertices_toWalk hbt hrL).elim
      | exact (Walk.not_mem_internalVertices_toWalk hbt hrR).elim
      | exact Set.disjoint_left.mp hAB_AZ hrL hrR
      | exact Set.disjoint_left.mp hAB_AZ.symm hrL hrR
      | exact Set.disjoint_left.mp hAB_BZ hrL hrR
      | exact Set.disjoint_left.mp hAB_BZ.symm hrL hrR
      | exact Set.disjoint_left.mp hAZ_BZ hrL hrR
      | exact Set.disjoint_left.mp hAZ_BZ.symm hrL hrR

/-- If a simple cycle contains three distinct vertices `a,b,z`, and an
external vertex `t` is adjacent to both `a` and `b`, then the cycle together
with the two attachment edges contains a suppressed-edge theta subdivision.
This is the direct formal form of the Makarychev Lemma 3 end-cycle step. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_common_neighbor
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b z t : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hat : G.Adj a t)
    (hbt : G.Adj b t)
    (ht_cycle : t ∉ c.support) :
    ContainsEdgeThetaSubdivision G := by
  classical
  rcases
    Walk.IsCycle.exists_avoiding_path_and_split_through
      (G := G) c hc ha hb hz hab haz.symm hbz.symm with
    ⟨pAB, pAZ, pBZ, hAB, hAZ, hBZ,
      hpAB_support, hpAZ_support, hpBZ_support,
      hz_not_pAB, hb_not_pAZ, ha_not_pBZ,
      hAB_AZ, hAB_BZ, hAZ_BZ⟩
  have hat_ne : a ≠ t := by
    intro hat_eq
    exact ht_cycle (by simpa [hat_eq] using ha)
  have hbt_ne : b ≠ t := by
    intro hbt_eq
    exact ht_cycle (by simpa [hbt_eq] using hb)
  have htz : t ≠ z := by
    intro htz_eq
    exact ht_cycle (by simpa [htz_eq] using hz)
  refine
    ContainsEdgeThetaSubdivision.of_common_neighbor_and_split_path
      pAB pAZ pBZ hat hbt hab hat_ne haz hbt_ne hbz htz
      hAB hAZ hBZ ?_ ?_ ?_ hAB_AZ hAB_BZ hAZ_BZ
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · exact hq.2.2
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqt
        exact ht_cycle (by simpa [hqt] using hpAB_support q hq.1)
      · intro hqz
        exact hz_not_pAB (by simpa [hqz] using hq.1)
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · intro hqb
        exact hb_not_pAZ (by simpa [hqb] using hq.1)
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqt
        exact ht_cycle (by simpa [hqt] using hpAZ_support q hq.1)
      · exact hq.2.2
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · intro hqa
        exact ha_not_pBZ (by simpa [hqa] using hq.1)
      · exact hq.2.1
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqt
        exact ht_cycle (by simpa [hqt] using hpBZ_support q hq.1)
      · exact hq.2.2

end Schematic.Math.GraphTheory
