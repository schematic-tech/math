import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.BoundaryPolygon
import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

/-- A graph together with a finite cyclic boundary order. -/
structure GeneralSociety (V : Type u) where
  graph : SimpleGraph V
  boundary : CyclicBoundary V

namespace GeneralSociety

/-- Adjoin the boundary polygon to a society graph.  A face-marked rotation
system on this exact graph is the finite combinatorial form of a drawing in a
disk with the society boundary on the rim. -/
def boundaryAugmentedGraphOfLength (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n) : SimpleGraph V :=
  S.graph ⊔ S.boundary.cycleGraphOfLength n h

/-- The boundary traversal included into the boundary-augmented graph. -/
def boundaryCycleWalkOfLength (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) :
    (S.boundaryAugmentedGraphOfLength (n + 3) h).Walk
      (S.boundary.embeddingOfLength (n + 3) h 0)
      (S.boundary.embeddingOfLength (n + 3) h 0) :=
  (S.boundary.cycleWalkOfLength n h).mapLe le_sup_right

theorem boundaryCycleWalkOfLength_isCycle (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) :
    (S.boundaryCycleWalkOfLength n h).IsCycle :=
  (S.boundary.cycleWalkOfLength_isCycle n h).mapLe le_sup_right

@[simp]
theorem boundaryCycleWalkOfLength_support (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) :
    (S.boundaryCycleWalkOfLength n h).support =
      (S.boundary.cycleWalkOfLength n h).support := by
  change
    ((S.boundary.cycleWalkOfLength n h).mapLe le_sup_right).support =
      (S.boundary.cycleWalkOfLength n h).support
  exact SimpleGraph.Walk.support_mapLe_eq_support le_sup_right
    (S.boundary.cycleWalkOfLength n h)

@[simp]
theorem boundaryCycleWalkOfLength_length (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) :
    (S.boundaryCycleWalkOfLength n h).length =
      (S.boundary.cycleWalkOfLength n h).length := by
  change
    ((S.boundary.cycleWalkOfLength n h).mapLe le_sup_right).length =
      (S.boundary.cycleWalkOfLength n h).length
  exact SimpleGraph.Walk.length_map
    (SimpleGraph.Hom.ofLE le_sup_right) (S.boundary.cycleWalkOfLength n h)

/-- The boundary walk inside the augmented graph spans exactly the adjoined
canonical polygon. -/
theorem boundaryCycleWalkOfLength_toSubgraph_spanningCoe
    [Fintype V] [DecidableEq V]
    (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) :
    (S.boundaryCycleWalkOfLength n h).toSubgraph.spanningCoe =
      S.boundary.cycleGraphOfLength (n + 3) h := by
  ext x y
  calc
    (S.boundaryCycleWalkOfLength n h).toSubgraph.spanningCoe.Adj x y ↔
        s(x, y) ∈ (S.boundaryCycleWalkOfLength n h).edges :=
      by
        rw [SimpleGraph.Subgraph.spanningCoe_adj,
          SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    _ ↔ s(x, y) ∈ (S.boundary.cycleWalkOfLength n h).edges := by
      change s(x, y) ∈
          ((S.boundary.cycleWalkOfLength n h).mapLe le_sup_right).edges ↔ _
      rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    _ ↔ (S.boundary.cycleWalkOfLength n h).toSubgraph.spanningCoe.Adj x y :=
      by
        rw [SimpleGraph.Subgraph.spanningCoe_adj,
          SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    _ ↔ (S.boundary.cycleGraphOfLength (n + 3) h).Adj x y := by
      rw [S.boundary.cycleWalkOfLength_toSubgraph_spanningCoe n h]

/-- Taking the same interval of the boundary traversal before or after its
inclusion into the boundary-augmented graph gives the same ordered support. -/
theorem boundaryCycleWalkOfLength_drop_take_support
    (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) (i k : Nat) :
    ((((S.boundaryCycleWalkOfLength n h).drop i).take k).support) =
      ((((S.boundary.cycleWalkOfLength n h).drop i).take k).support) := by
  rw [SimpleGraph.Walk.take_support_eq_support_take_succ,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,
    SimpleGraph.Walk.take_support_eq_support_take_succ,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,
    S.boundaryCycleWalkOfLength_support,
    S.boundaryCycleWalkOfLength_length]

/-- A checked disk embedding for a society whose boundary has at least three
vertices.  The augmented graph is exact, the canonical boundary cycle is one
complete face, and the rotation system has Euler genus zero. -/
structure DiskRuralCertificate [Fintype V] [DecidableEq V]
    (S : GeneralSociety V) where
  n : Nat
  boundary_length : S.boundary.length = n + 3
  rotation :
    FourColor.RotationSystem
      (S.boundaryAugmentedGraphOfLength (n + 3) boundary_length)
  dual_eulerPlanar :
    letI : DecidableRel
        (S.boundaryAugmentedGraphOfLength (n + 3) boundary_length).Adj :=
      Classical.decRel _
    rotation.toHypermap.dual.EulerPlanar
  boundary_facial :
    letI : DecidableRel
        (S.boundaryAugmentedGraphOfLength (n + 3) boundary_length).Adj :=
      Classical.decRel _
    FourColor.RotationSystemGluing.IsFacialCycle rotation
      (S.boundaryCycleWalkOfLength n boundary_length)
      (S.boundaryCycleWalkOfLength_isCycle n boundary_length)

-- Re-open the graph namespace after the rotation-system field declarations;
-- subsequent source code intentionally uses the established short names
-- `Walk` and `ConnectedComponent`.
open SimpleGraph

@[ext]
theorem ext {S T : GeneralSociety V}
    (hgraph : S.graph = T.graph) (hboundary : S.boundary = T.boundary) :
    S = T := by
  cases S
  cases T
  simp at hgraph hboundary ⊢
  exact ⟨hgraph, hboundary⟩

def boundarySet (S : GeneralSociety V) : Set V :=
  S.boundary.vertexSet

/-- The vertices that belong to the society, ignoring ambient isolated
vertices left over from using a fixed Lean vertex type.  This matters for the
GM IX split graphs: `G_i` deletes the opposite side, while our concrete
`SimpleGraph V` representation leaves deleted vertices as isolated ambient
points unless the separation predicate filters them out. -/
def activeSet (S : GeneralSociety V) : Set V :=
  S.graph.support ∪ S.boundarySet

theorem boundarySet_finite (S : GeneralSociety V) :
    S.boundarySet.Finite :=
  S.boundary.finite_vertexSet

theorem boundarySet_ncard (S : GeneralSociety V) :
    S.boundarySet.ncard = S.boundary.length :=
  S.boundary.ncard_vertexSet_eq_length'

/-- Every boundary vertex occurs on the canonical boundary walk in the
boundary-augmented graph.  This is the society-level form used when a rural
face is split at the two ends of a GM IX cut path. -/
theorem boundary_mem_boundaryCycleWalkOfLength_support
    (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) {v : V}
    (hv : v ∈ S.boundarySet) :
    v ∈ (S.boundaryCycleWalkOfLength n h).support := by
  have hv' : v ∈ S.boundary.vertexSet := by
    simpa [boundarySet] using hv
  have hsupport := S.boundary.mem_cycleWalkOfLength_support n h hv'
  change v ∈ ((S.boundary.cycleWalkOfLength n h).mapLe _).support
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  exact hsupport

theorem boundary_mem_boundaryAugmentedGraphOfLength_support
    (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) {v : V}
    (hv : v ∈ S.boundarySet) :
    v ∈ (S.boundaryAugmentedGraphOfLength (n + 3) h).support := by
  exact SimpleGraph.mem_support_of_mem_walk_support
    (S.boundaryCycleWalkOfLength n h)
    (S.boundaryCycleWalkOfLength_isCycle n h).not_nil
    (S.boundary_mem_boundaryCycleWalkOfLength_support n h hv)

theorem boundaryAugmentedGraphOfLength_support_subset
    [Fintype V] [DecidableEq V]
    (S : GeneralSociety V) (n : Nat)
    (h : S.boundary.length = n + 3) :
    (S.boundaryAugmentedGraphOfLength (n + 3) h).support ⊆
      S.graph.support ∪ S.boundarySet := by
  intro v hv
  rcases (SimpleGraph.mem_support
    (S.boundaryAugmentedGraphOfLength (n + 3) h)).mp hv with
    ⟨w, hvw⟩
  rcases (SimpleGraph.sup_adj S.graph
      (S.boundary.cycleGraphOfLength (n + 3) h) v w).mp hvw with
    hvGraph | hvCycle
  · exact Or.inl hvGraph.left_mem_support
  · exact Or.inr (by
      have hvSupport :
          v ∈ (S.boundary.cycleGraphOfLength (n + 3) h).support :=
        hvCycle.left_mem_support
      rw [S.boundary.cycleGraphOfLength_support_eq_vertexSet n h] at hvSupport
      simpa [GeneralSociety.boundarySet] using hvSupport)


end GeneralSociety

end Schematic.Math.GraphTheory
