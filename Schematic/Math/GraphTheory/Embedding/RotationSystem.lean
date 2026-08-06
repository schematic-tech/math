import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Schematic.Math.GraphTheory.Embedding.Counts
import Schematic.Math.GraphTheory.Embedding.Hypermap
import Schematic.Math.GraphTheory.Embedding.Geometry

/-!
Rotation systems for finite simple graphs.

This file starts the graph-side embedding object needed by the
SimpleGraph-to-hypermap bridge.  A dart is an oriented edge of a simple graph.
A rotation system supplies the cyclic order of the darts leaving each vertex.
From an edge-swap and a node rotation we get a hypermap by the usual formula
`face = node⁻¹ ∘ edge`.

The planarity/Kuratowski theorem still has to prove that the rotation system
exists with the right planar geometry.  The construction here is independent of
that theorem and contains no placeholder assumptions.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

/-- Oriented edges of a simple graph, represented by ordered adjacent vertex
pairs. -/
abbrev OrientedEdge {V : Type u} (G : SimpleGraph V) :=
  { e : V × V // G.Adj e.1 e.2 }

namespace OrientedEdge

variable {V : Type u} {G : SimpleGraph V}

def tail (e : OrientedEdge G) : V :=
  e.1.1

def head (e : OrientedEdge G) : V :=
  e.1.2

@[simp]
theorem adj (e : OrientedEdge G) :
    G.Adj e.tail e.head :=
  e.2

/-- Reverse the orientation of a dart. -/
def symm (e : OrientedEdge G) : OrientedEdge G :=
  ⟨(e.head, e.tail), G.symm e.adj⟩

@[simp]
theorem tail_symm (e : OrientedEdge G) :
    e.symm.tail = e.head :=
  rfl

@[simp]
theorem head_symm (e : OrientedEdge G) :
    e.symm.head = e.tail :=
  rfl

@[simp]
theorem symm_symm (e : OrientedEdge G) :
    e.symm.symm = e := by
  cases e with
  | mk e he =>
      cases e
      rfl

/-- The hypermap edge permutation on oriented graph edges. -/
def edgePerm {V : Type u} (G : SimpleGraph V) :
    Equiv.Perm (OrientedEdge G) where
  toFun := symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm

@[simp]
theorem edgePerm_apply (e : OrientedEdge G) :
    edgePerm G e = e.symm :=
  rfl

@[simp]
theorem edgePerm_edgePerm (e : OrientedEdge G) :
    edgePerm G (edgePerm G e) = e := by
  simp [edgePerm]

theorem edgePerm_ne_self (e : OrientedEdge G) :
    edgePerm G e ≠ e := by
  intro h
  have htail : e.head = e.tail := by
    have hpair : (e.head, e.tail) = (e.tail, e.head) :=
      congrArg Subtype.val h
    exact Prod.ext_iff.mp hpair |>.1
  have hloop : G.Adj e.tail e.tail := by
    exact htail ▸ e.adj
  exact G.loopless.irrefl e.tail hloop

end OrientedEdge

noncomputable def orientedEdgeDartEquiv
    {V : Type u} {G : SimpleGraph V} :
    OrientedEdge G ≃ G.Dart where
  toFun e := ⟨(e.tail, e.head), e.adj⟩
  invFun d := ⟨(d.fst, d.snd), d.adj⟩
  left_inv := by
    intro e
    cases e with
    | mk e he =>
        cases e
        rfl
  right_inv := by
    intro d
    ext <;> rfl

theorem orientedEdge_card_eq_twice_card_edges
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    Fintype.card (OrientedEdge G) = 2 * G.edgeFinset.card := by
  classical
  rw [Fintype.card_congr (orientedEdgeDartEquiv (G := G))]
  exact G.dart_card_eq_twice_card_edges

/-- A rotation system on a graph: a permutation of oriented edges preserving
their tail vertex.  The optional transitivity field says that all darts leaving
the same vertex lie in one node orbit, which is the combinatorial embedding
condition used when transferring node colours back to vertex colours. -/
structure RotationSystem {V : Type u} (G : SimpleGraph V) where
  node : Equiv.Perm (OrientedEdge G)
  node_tail : ∀ e : OrientedEdge G, (node e).tail = e.tail
  node_orbit_of_same_tail :
    ∀ e f : OrientedEdge G, e.tail = f.tail → PermReachable node e f

namespace RotationSystem

variable {V : Type u} {G : SimpleGraph V}

/-- Hypermap induced by a graph rotation system. -/
noncomputable def toHypermap
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    Hypermap.{u} where
  Dart := OrientedEdge G
  edge := OrientedEdge.edgePerm G
  node := R.node
  face := (OrientedEdge.edgePerm G).trans R.node.symm
  node_face_edge := by
    intro e
    simp [OrientedEdge.edgePerm]

@[simp]
theorem toHypermap_edge
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) (e : (R.toHypermap).Dart) :
    (R.toHypermap).edge e = e.symm :=
  rfl

@[simp]
theorem toHypermap_node
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) (e : (R.toHypermap).Dart) :
    (R.toHypermap).node e = R.node e :=
  rfl

theorem toHypermap_plain
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).Plain := by
  intro e
  constructor
  · change OrientedEdge.edgePerm G (OrientedEdge.edgePerm G e) = e
    exact OrientedEdge.edgePerm_edgePerm e
  · exact OrientedEdge.edgePerm_ne_self e

theorem toHypermap_dual_plain
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).dual.Plain :=
  (R.toHypermap_plain).dual

theorem node_symm_tail
    (R : RotationSystem G)
    (e : OrientedEdge G) :
    (R.node.symm e).tail = e.tail := by
  have h := R.node_tail (R.node.symm e)
  simpa using h.symm

/-- Reverse every local cyclic order of a graph rotation system.  This is the
combinatorial operation that reflects an embedded component before it is
spliced through a cut vertex or along a boundary cycle. -/
def reverse
    (R : RotationSystem G) :
    RotationSystem G where
  node := R.node.symm
  node_tail := R.node_symm_tail
  node_orbit_of_same_tail := by
    intro e f hef
    exact (permReachable_symmPerm_iff R.node).2
      (R.node_orbit_of_same_tail e f hef)

@[simp]
theorem reverse_node
    (R : RotationSystem G)
    (e : OrientedEdge G) :
    R.reverse.node e = R.node.symm e :=
  rfl

@[simp]
theorem reverse_reverse
    (R : RotationSystem G) :
    R.reverse.reverse = R := by
  cases R
  rfl

theorem node_reachable_tail
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : PermReachable R.node e f) :
    f.tail = e.tail :=
  (hef.apply_eq OrientedEdge.tail fun {_ _} h => by
    cases h
    · exact (R.node_tail _).symm
    · exact (R.node_symm_tail _).symm).symm

theorem node_symm_reachable_tail
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : PermReachable R.node.symm e f) :
    f.tail = e.tail :=
  (hef.apply_eq OrientedEdge.tail fun {_ _} h => by
    cases h
    · exact (R.node_symm_tail _).symm
    · exact (R.node_tail _).symm).symm

theorem toHypermap_dual_bridgeless
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).dual.Bridgeless := by
  intro e hbad
  change PermReachable R.node.symm e e.symm at hbad
  have htail : e.symm.tail = e.tail :=
    R.node_symm_reachable_tail hbad
  have hhead_tail : e.head = e.tail := by
    simpa using htail
  have hloop : G.Adj e.tail e.tail := by
    simpa [hhead_tail] using e.adj
  exact G.loopless.irrefl e.tail hloop

@[simp]
theorem toHypermap_face_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) (e : OrientedEdge G) :
    ((R.toHypermap).face e).tail = e.head := by
  change (R.node.symm e.symm).tail = e.head
  simpa using R.node_symm_tail e.symm

/-- If the two orientations of an edge lie in different face orbits of a
rotation system, that edge lies on a graph cycle.  Traversing the selected
face orbit from `e` and omitting its first dart gives an alternate walk from
`e.tail` to `e.head` avoiding the edge. -/
theorem exists_isCycle_edge_mem_of_not_faceReachable_symm
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) (e : OrientedEdge G)
    (hnot :
      ¬ PermReachable (R.toHypermap).face e e.symm) :
    ∃ u : V, ∃ c : G.Walk u u,
      c.IsCycle ∧
        s(e.tail, e.head) ∈ c.edges ∧
          ∀ f ∈ c.edges,
            ∃ d : OrientedEdge G,
              PermReachable (R.toHypermap).face e d ∧
                f = s(d.tail, d.head) := by
  classical
  rcases
      Hypermap.exists_ordered_faceOrbitCycle
        (G := R.toHypermap) e with
    ⟨p, hpFace, hpClose, hpNodup, hpMem⟩
  have hpNe : p ≠ [] := by
    intro hp
    subst p
    have hface : (R.toHypermap).face e = e := by
      simpa [List.getLastD] using hpClose
    have htail := R.toHypermap_face_tail e
    rw [hface] at htail
    exact e.adj.ne htail
  cases p with
  | nil =>
    exact (hpNe rfl).elim
  | cons d p =>
    have hed :
        (R.toHypermap).face e = d := by
      exact
        ((Hypermap.FacePath.cons
          (G := R.toHypermap) e d p).mp hpFace).1
    have hdp :
        (R.toHypermap).FacePath d p := by
      exact
        ((Hypermap.FacePath.cons
          (G := R.toHypermap) e d p).mp hpFace).2
    have hchainFace :
        List.IsChain
          (fun a b : OrientedEdge G =>
            (R.toHypermap).face a = b)
          (d :: p) :=
      (Hypermap.FacePath.iff_isChain R.toHypermap).mp hdp
    let dartEquiv : OrientedEdge G ≃ G.Dart :=
      orientedEdgeDartEquiv (G := G)
    let ds : List G.Dart := (d :: p).map dartEquiv
    have hchainOriented :
        List.IsChain
          (fun a b : OrientedEdge G =>
            G.DartAdj (dartEquiv a) (dartEquiv b))
          (d :: p) := by
      exact hchainFace.imp (fun {a b} hab => by
        change a.head = b.tail
        rw [← hab]
        exact (R.toHypermap_face_tail a).symm)
    have hchain :
        List.IsChain G.DartAdj ds := by
      exact (List.isChain_map dartEquiv).mpr hchainOriented
    have hdsNe : ds ≠ [] := by
      simp [ds]
    let q0 :=
      SimpleGraph.Walk.ofDarts ds hdsNe hchain
    have hdTail : d.tail = e.head := by
      rw [← hed]
      exact R.toHypermap_face_tail e
    have hlastFace :
        (R.toHypermap).face ((d :: p).getLastD d) = e := by
      simpa [List.getLastD] using hpClose
    have hlastHead :
        ((d :: p).getLastD d).head = e.tail := by
      have htail :=
        R.toHypermap_face_tail ((d :: p).getLastD d)
      rw [hlastFace] at htail
      exact htail.symm
    have hq0Start :
        (ds.head hdsNe).fst = e.head := by
      simpa [ds, dartEquiv, orientedEdgeDartEquiv] using hdTail
    have hq0End :
        (ds.getLast hdsNe).snd = e.tail := by
      simpa [ds, dartEquiv, orientedEdgeDartEquiv] using hlastHead
    let q : G.Walk e.head e.tail :=
      q0.copy hq0Start hq0End
    have heNotMem : e ∉ d :: p := by
      exact (List.nodup_cons.mp hpNodup).1
    have heSymmNotMem : e.symm ∉ d :: p := by
      intro heSymm
      have heSymmFace :
          PermReachable (R.toHypermap).face e e.symm :=
        (hpMem e.symm).mp (by
          exact List.mem_cons_of_mem e heSymm)
      exact hnot heSymmFace
    have heDartNotMem : dartEquiv e ∉ ds := by
      simpa [ds] using heNotMem
    have heSymmDartNotMem :
        (dartEquiv e).symm ∉ ds := by
      have hcommute :
          dartEquiv e.symm = (dartEquiv e).symm := by
        rfl
      rw [← hcommute]
      simpa [ds] using heSymmNotMem
    have heEdgeNotMem : s(e.tail, e.head) ∉ q.edges := by
      have hqEdges :
          q.edges = ds.map SimpleGraph.Dart.edge := by
        simp [q, q0]
      rw [hqEdges]
      intro heEdge
      rcases List.mem_map.mp heEdge with ⟨f, hf, hfe⟩
      have hfe' :
          f.edge = (dartEquiv e).edge := by
        simpa [dartEquiv, orientedEdgeDartEquiv,
          SimpleGraph.Dart.edge] using hfe
      rcases
          (SimpleGraph.dart_edge_eq_iff f (dartEquiv e)).mp hfe' with
        hfe | hfe
      · exact heDartNotMem (hfe ▸ hf)
      · exact heSymmDartNotMem (hfe ▸ hf)
    let pAlt : G.Walk e.tail e.head := q.reverse
    have hePathNotMem :
        s(e.head, e.tail) ∉ (pAlt.toPath : G.Walk e.tail e.head).edges := by
      intro hePath
      have heAlt : s(e.head, e.tail) ∈ pAlt.edges :=
        SimpleGraph.Walk.edges_toPath_subset pAlt hePath
      apply heEdgeNotMem
      simpa [pAlt, Sym2.eq_swap] using heAlt
    let c : G.Walk e.head e.head :=
      SimpleGraph.Walk.cons e.adj.symm pAlt.toPath
    have hc : c.IsCycle := by
      exact SimpleGraph.Path.cons_isCycle pAlt.toPath e.adj.symm hePathNotMem
    have hec : s(e.tail, e.head) ∈ c.edges := by
      simp [c, Sym2.eq_swap]
    have hqEdgesOriented :
        q.edges =
          (d :: p).map
            (fun z : OrientedEdge G => s(z.tail, z.head)) := by
      calc
        q.edges = ds.map SimpleGraph.Dart.edge := by
          simp [q, q0]
        _ = (d :: p).map
              (fun z : OrientedEdge G => s(z.tail, z.head)) := by
          simp [ds, dartEquiv, orientedEdgeDartEquiv,
            SimpleGraph.Dart.edge]
    refine ⟨e.head, c, hc, hec, ?_⟩
    intro f hf
    have hfCases :
        f = s(e.head, e.tail) ∨
          f ∈ (pAlt.toPath : G.Walk e.tail e.head).edges := by
      simpa [c] using hf
    rcases hfCases with hfirst | hpath
    · exact
        ⟨e, PermReachable.refl (R.toHypermap).face e,
          hfirst.trans Sym2.eq_swap⟩
    · have hpAlt : f ∈ pAlt.edges :=
        SimpleGraph.Walk.edges_toPath_subset pAlt hpath
      have hq : f ∈ q.edges := by
        simpa [pAlt] using hpAlt
      rw [hqEdgesOriented] at hq
      rcases List.mem_map.mp hq with ⟨z, hz, rfl⟩
      exact
        ⟨z,
          (hpMem z).mp (List.mem_cons_of_mem e hz),
          rfl⟩

theorem toHypermap_reachable_tail_reachable
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : (R.toHypermap).Reachable e f) :
    G.Reachable e.tail f.tail := by
  rw [SimpleGraph.reachable_eq_reflTransGen]
  exact hef.lift' OrientedEdge.tail fun b _ h => by
    rcases h with h | h | h
    · subst h
      exact Relation.ReflTransGen.single b.adj
    · subst h
      have htail : ((R.toHypermap).node b).tail = b.tail := R.node_tail b
      rw [htail]
    · subst h
      have htail : ((R.toHypermap).face b).tail = b.head := by
        change (R.node.symm b.symm).tail = b.head
        simpa using R.node_symm_tail b.symm
      rw [htail]
      exact Relation.ReflTransGen.single b.adj

theorem toHypermap_reachable_of_same_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : e.tail = f.tail) :
    (R.toHypermap).Reachable e f := by
  exact Hypermap.nodePermReachable_reachable
    (G := R.toHypermap)
    (by
      change PermReachable R.node e f
      exact R.node_orbit_of_same_tail e f hef)

theorem toHypermap_cConnect_of_same_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : e.tail = f.tail) :
    (R.toHypermap).CConnect e f := by
  have hreach : PermReachable R.node e f :=
    R.node_orbit_of_same_tail e f hef
  have hreachSymm : PermReachable R.node.symm e f :=
    (permReachable_symmPerm_iff R.node).2 hreach
  exact (R.toHypermap).cConnect_of_nodeSymmReachable (by
    simpa [RotationSystem.toHypermap] using hreachSymm)

theorem toHypermap_exists_short_cPath_of_same_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : e.tail = f.tail) :
    ∃ p : List (OrientedEdge G),
      (R.toHypermap).CPath e p ∧
        (e :: p).getLastD e = f ∧
          (e :: p).Nodup :=
  Hypermap.CConnect.exists_short_cPath
    (G := R.toHypermap) (R.toHypermap_cConnect_of_same_tail hef)

/-- A reverse-node path in a graph rotation system stays over one graph
vertex.  This is the controlled counterpart of the generic `CPath` API used
when porting GraphTheory's `hcycle.v`. -/
theorem nodeSymmPath_tail_eq
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e : OrientedEdge G} {p : List (OrientedEdge G)}
    (hp : (R.toHypermap).NodeSymmPath e p)
    {d : OrientedEdge G}
    (hd : d ∈ e :: p) :
    d.tail = e.tail := by
  induction p generalizing e with
  | nil =>
      simp at hd
      subst d
      rfl
  | cons f p ih =>
      have hp' :
          R.node.symm e = f ∧
            (R.toHypermap).NodeSymmPath f p := by
        simpa [Hypermap.NodeSymmPath] using hp
      have hfTail : f.tail = e.tail := by
        rw [← hp'.1]
        exact R.node_symm_tail e
      rw [List.mem_cons] at hd
      rcases hd with rfl | hd
      · rfl
      · exact (ih hp'.2 hd).trans hfTail

/-- A contour step between darts based at the same graph vertex must be the
reverse-node alternative; a face step crosses the underlying graph edge. -/
theorem toHypermap_node_apply_eq_of_cLink_same_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : e.tail = f.tail)
    (hlink : (R.toHypermap).CLink e f) :
    (R.toHypermap).node f = e := by
  rcases hlink with hnode | hface
  · rw [hnode]
    simp
  · exfalso
    apply e.adj.ne
    calc
      e.tail = f.tail := hef
      _ = ((R.toHypermap).face e).tail :=
        congrArg OrientedEdge.tail hface
      _ = e.head := RotationSystem.toHypermap_face_tail R e

/-- Same-tail darts can be joined using reverse-node steps only. -/
theorem toHypermap_exists_nodeSymmPath_of_same_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : e.tail = f.tail) :
    ∃ p : List (OrientedEdge G),
      (R.toHypermap).NodeSymmPath e p ∧
        (e :: p).getLastD e = f := by
  have hreach : PermReachable R.node e f :=
    R.node_orbit_of_same_tail e f hef
  have hreachSymm : PermReachable R.node.symm e f :=
    (permReachable_symmPerm_iff R.node).2 hreach
  exact Hypermap.exists_nodeSymmPath_of_nodeSymmReachable
    (G := R.toHypermap) (by
      simpa [RotationSystem.toHypermap] using hreachSymm)

/-- A duplicate-free contour between same-tail darts whose every dart remains
over that common vertex.  It is obtained by shortening a reverse-node path;
shortening only removes darts, so the tail invariant is preserved. -/
theorem toHypermap_exists_short_cPath_of_same_tail_controlled
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : e.tail = f.tail) :
    ∃ p : List (OrientedEdge G),
      (R.toHypermap).CPath e p ∧
        (e :: p).getLastD e = f ∧
          (e :: p).Nodup ∧
            ∀ d : OrientedEdge G, d ∈ e :: p →
              d.tail = e.tail := by
  rcases R.toHypermap_exists_nodeSymmPath_of_same_tail hef with
    ⟨p, hp, hlast⟩
  rcases Hypermap.CPath.shorten
      (G := R.toHypermap)
      (Hypermap.NodeSymmPath.to_CPath (G := R.toHypermap) hp) with
    ⟨q, hq, hlastq, hnodup, hsub⟩
  exact
    ⟨q, hq, hlastq.trans hlast, hnodup,
      fun d hd => R.nodeSymmPath_tail_eq hp (hsub d hd)⟩

/-- One graph edge can be traversed by a controlled contour path: rotate at
the initial vertex to the chosen oriented edge, take one face step across it,
then rotate at the terminal vertex to the requested dart.  Every listed dart
therefore lies over one of the two endpoints. -/
theorem toHypermap_exists_cPath_across_adj_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : G.Adj e.tail f.tail) :
    ∃ p : List (OrientedEdge G),
      (R.toHypermap).CPath e p ∧
        (e :: p).getLastD e = f ∧
          ∀ d : OrientedEdge G, d ∈ e :: p →
            d.tail = e.tail ∨ d.tail = f.tail := by
  let a : OrientedEdge G := ⟨(e.tail, f.tail), hef⟩
  rcases R.toHypermap_exists_nodeSymmPath_of_same_tail
      (e := e) (f := a) rfl with
    ⟨p, hp, hlastp⟩
  let fa : OrientedEdge G := (R.toHypermap).face a
  have hfaceTail : fa.tail = f.tail := by
    rw [RotationSystem.toHypermap_face_tail]
    rfl
  rcases R.toHypermap_exists_nodeSymmPath_of_same_tail
      (e := fa) (f := f) hfaceTail with
    ⟨q, hq, hlastq⟩
  refine ⟨p ++ fa :: q, ?_, ?_, ?_⟩
  · exact Hypermap.CPath.append_cons
      (G := R.toHypermap)
      (Hypermap.NodeSymmPath.to_CPath (G := R.toHypermap) hp)
      hlastp (by
        simpa [fa] using
          (Hypermap.CLink.face (G := R.toHypermap) a))
      (Hypermap.NodeSymmPath.to_CPath (G := R.toHypermap) hq)
  · calc
      (e :: (p ++ fa :: q)).getLastD e =
          (a :: fa :: q).getLastD a :=
        Hypermap.list_getLastD_cons_append_of_getLast
          e a p (fa :: q) hlastp
      _ =
          (fa :: q).getLastD fa :=
        by simp [List.getLastD]
      _ = f := hlastq
  · intro d hd
    rw [List.mem_cons, List.mem_append] at hd
    rcases hd with rfl | hdp | hdq
    · exact Or.inl rfl
    · exact Or.inl
        (R.nodeSymmPath_tail_eq hp (by simp [hdp]))
    · exact Or.inr
        ((R.nodeSymmPath_tail_eq hq hdq).trans hfaceTail)

/-- Lift a graph walk to a contour path with controlled support.  Every dart
in the contour is based at a vertex of the original walk; this is the
rotation-system form of the restricted `clink` paths used in Coq
`hcycle.v`. -/
theorem toHypermap_exists_cPath_of_walk
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {x y : V}
    (w : G.Walk x y)
    {e f : OrientedEdge G}
    (he : e.tail = x)
    (hf : f.tail = y) :
    ∃ p : List (OrientedEdge G),
      (R.toHypermap).CPath e p ∧
        (e :: p).getLastD e = f ∧
          ∀ d : OrientedEdge G, d ∈ e :: p → d.tail ∈ w.support := by
  induction w generalizing e f with
  | nil =>
      rcases R.toHypermap_exists_nodeSymmPath_of_same_tail
          (e := e) (f := f) (he.trans hf.symm) with
        ⟨p, hp, hlast⟩
      refine ⟨p, Hypermap.NodeSymmPath.to_CPath (G := R.toHypermap) hp,
        hlast, ?_⟩
      intro d hd
      have hdtail : d.tail = e.tail :=
        R.nodeSymmPath_tail_eq hp hd
      simpa [he] using hdtail
  | @cons u v z huv w ih =>
      let a : OrientedEdge G := ⟨(u, v), huv⟩
      have hea : G.Adj e.tail a.symm.tail := by
        simpa [a, he] using huv
      rcases R.toHypermap_exists_cPath_across_adj_tail
          (e := e) (f := a.symm) hea with
        ⟨p, hp, hlastp, hpSupport⟩
      rcases ih (e := a.symm) (f := f) rfl hf with
        ⟨q, hq, hlastq, hqSupport⟩
      refine ⟨p ++ q, ?_, ?_, ?_⟩
      · exact Hypermap.CPath.append (G := R.toHypermap) hp hlastp hq
      · calc
          (e :: (p ++ q)).getLastD e =
              (a.symm :: q).getLastD a.symm :=
            Hypermap.list_getLastD_cons_append_of_getLast
              e a.symm p q hlastp
          _ = f := hlastq
      · intro d hd
        rw [List.mem_cons, List.mem_append] at hd
        rcases hd with rfl | hdp | hdq
        · simp [he]
        · rcases hpSupport d (by simp [hdp]) with hdu | hdv
          · simp [hdu, he]
          · have hdv' : d.tail = v := by
              simpa [a] using hdv
            simp [hdv']
        · have hdmem : d.tail ∈ w.support :=
            hqSupport d (by simp [hdq])
          exact SimpleGraph.Walk.support_subset_support_cons w huv hdmem

/-- Shortened controlled contour lift.  The shortening operation only removes
darts, so the graph-walk support bound survives while the resulting contour
becomes duplicate-free. -/
theorem toHypermap_exists_short_cPath_of_walk
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {x y : V}
    (w : G.Walk x y)
    {e f : OrientedEdge G}
    (he : e.tail = x)
    (hf : f.tail = y) :
    ∃ p : List (OrientedEdge G),
      (R.toHypermap).CPath e p ∧
        (e :: p).getLastD e = f ∧
          (e :: p).Nodup ∧
            ∀ d : OrientedEdge G, d ∈ e :: p →
              d.tail ∈ w.support := by
  rcases R.toHypermap_exists_cPath_of_walk w he hf with
    ⟨p, hp, hlast, hsupport⟩
  rcases Hypermap.CPath.shorten (G := R.toHypermap) hp with
    ⟨q, hq, hlastq, hnodup, hsub⟩
  refine ⟨q, hq, ?_, hnodup, ?_⟩
  · exact hlastq.trans hlast
  · intro d hd
    exact hsupport d (hsub d hd)

theorem toHypermap_exists_short_cPath_of_walk_avoiding_vertex
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {x y z : V}
    (w : G.Walk x y)
    (hz : z ∉ w.support)
    {e f : OrientedEdge G}
    (he : e.tail = x)
    (hf : f.tail = y) :
    ∃ p : List (OrientedEdge G),
      (R.toHypermap).CPath e p ∧
        (e :: p).getLastD e = f ∧
          (e :: p).Nodup ∧
            ∀ d : OrientedEdge G, d ∈ e :: p → d.tail ≠ z := by
  rcases R.toHypermap_exists_short_cPath_of_walk w he hf with
    ⟨p, hp, hlast, hnodup, hsupport⟩
  exact ⟨p, hp, hlast, hnodup, fun d hd hdz =>
    hz (by simpa [hdz] using hsupport d hd)⟩

theorem toHypermap_reachable_of_adj_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : G.Adj e.tail f.tail) :
    (R.toHypermap).Reachable e f := by
  let d : OrientedEdge G := ⟨(e.tail, f.tail), hef⟩
  have h₁ : (R.toHypermap).Reachable e d :=
    R.toHypermap_reachable_of_same_tail rfl
  have h₂ : (R.toHypermap).Reachable d d.symm :=
    (R.toHypermap).reachable_edge d
  have h₃ : (R.toHypermap).Reachable d.symm f :=
    R.toHypermap_reachable_of_same_tail rfl
  exact h₁.trans (h₂.trans h₃)

theorem toHypermap_reachable_of_walk
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {x y : V}
    (p : G.Walk x y) :
    forall {e f : OrientedEdge G},
      e.tail = x -> f.tail = y -> (R.toHypermap).Reachable e f := by
  induction p with
  | nil =>
      intro e f he hf
      exact R.toHypermap_reachable_of_same_tail (he.trans hf.symm)
  | @cons u v w huv p ih =>
      intro e f he hf
      let d : OrientedEdge G := ⟨(u, v), huv⟩
      have hstep_adj : G.Adj e.tail d.symm.tail := by
        exact he ▸ huv
      have hstep : (R.toHypermap).Reachable e d.symm :=
        R.toHypermap_reachable_of_adj_tail hstep_adj
      have hrest : (R.toHypermap).Reachable d.symm f :=
        ih rfl hf
      exact hstep.trans hrest

theorem toHypermap_reachable_of_tail_reachable
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hef : G.Reachable e.tail f.tail) :
    (R.toHypermap).Reachable e f := by
  exact hef.elim (fun p => R.toHypermap_reachable_of_walk p rfl rfl)

theorem toHypermap_preconnected_iff_tail_reachable
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).Preconnected ↔
      forall e f : OrientedEdge G, G.Reachable e.tail f.tail := by
  constructor
  · intro hconn e f
    exact R.toHypermap_reachable_tail_reachable (hconn e f)
  · intro htail e f
    exact R.toHypermap_reachable_of_tail_reachable (htail e f)

theorem toHypermap_connected_of_tail_reachable
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    [Nonempty (OrientedEdge G)]
    (htail : forall e f : OrientedEdge G, G.Reachable e.tail f.tail) :
    (R.toHypermap).Connected := by
  letI : Nonempty (R.toHypermap).Dart := inferInstanceAs (Nonempty (OrientedEdge G))
  exact Hypermap.connected_of_preconnected (G := R.toHypermap)
    ((R.toHypermap_preconnected_iff_tail_reachable).mpr htail)

theorem reachable_induce_support_of_reachable
    {x y : G.support}
    (hxy : G.Reachable x.1 y.1) :
    (G.induce G.support).Reachable x y := by
  rcases hxy with ⟨p⟩
  have hp_support : forall z : V, z ∈ p.support -> z ∈ G.support := by
    intro z hz
    by_cases hzx : z = x.1
    · simp [hzx, x.2]
    · have hp_not_nil : ¬ p.Nil := by
        intro hp_nil
        have hsupp : p.support = [x.1] :=
          SimpleGraph.Walk.nil_iff_support_eq.mp hp_nil
        rw [hsupp] at hz
        simp at hz
        exact hzx hz
      exact SimpleGraph.mem_support_of_mem_walk_support p hp_not_nil hz
  exact ⟨p.induce G.support hp_support⟩

theorem reachable_of_reachable_induce_support
    {x y : G.support}
    (hxy : (G.induce G.support).Reachable x y) :
    G.Reachable x.1 y.1 := by
  exact hxy.map (SimpleGraph.Embedding.induce (G := G) G.support).toHom

theorem toHypermap_connected_of_support_preconnected
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    [Nonempty (OrientedEdge G)]
    (hsupport : (G.induce G.support).Preconnected) :
    (R.toHypermap).Connected := by
  refine R.toHypermap_connected_of_tail_reachable ?_
  intro e f
  have hreach :
      (G.induce G.support).Reachable
        ⟨e.tail, e.adj.left_mem_support⟩
        ⟨f.tail, f.adj.left_mem_support⟩ :=
    hsupport _ _
  exact reachable_of_reachable_induce_support hreach

/-- Generated dart components of a graph rotation system are precisely the
connected components of the graph after deleting isolated vertices.  The
forward direction is the tail-reachability theorem above; the reverse chooses
one outgoing dart at a support vertex and follows an induced graph walk. -/
noncomputable def componentSupportEquiv
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).Component ≃ (G.induce G.support).ConnectedComponent where
  toFun := Quotient.lift
    (fun e : OrientedEdge G =>
      (G.induce G.support).connectedComponentMk
        ⟨e.tail, e.adj.left_mem_support⟩)
    (by
      intro e f hef
      apply SimpleGraph.ConnectedComponent.sound
      exact reachable_induce_support_of_reachable
        (R.toHypermap_reachable_tail_reachable hef))
  invFun := Quot.lift
    (fun x : G.support =>
      let hx : Exists fun w : V => G.Adj (x : V) w :=
        (SimpleGraph.mem_support (G := G)).mp x.property
      let w := hx.choose
      let h := hx.choose_spec
      (R.toHypermap).componentOf (⟨(x, w), h⟩ : OrientedEdge G))
    (by
      intro x y hxy
      apply Quot.sound
      exact R.toHypermap_reachable_of_tail_reachable
        (reachable_of_reachable_induce_support hxy))
  left_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro e
    dsimp
    apply Quot.sound
    exact R.toHypermap_reachable_of_same_tail rfl
  right_inv := by
    intro c
    refine Quot.inductionOn c ?_
    intro x
    dsimp
    apply SimpleGraph.ConnectedComponent.sound
    exact SimpleGraph.Reachable.rfl

theorem componentCount_eq_supportComponent_card
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).componentCount =
      Nat.card (G.induce G.support).ConnectedComponent := by
  classical
  rw [Hypermap.componentCount]
  exact Nat.card_congr (R.componentSupportEquiv)

/-- Node orbits of a graph rotation system are precisely the non-isolated
vertices of the original graph.  This is the count bridge from graph vertices
to hypermap node cycles. -/
noncomputable def nodeOrbitSupportEquiv
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).NodeOrbit ≃ G.support where
  toFun := Quotient.lift
    (fun e : OrientedEdge G => ⟨e.tail, e.adj.left_mem_support⟩)
    (by
      intro e f hef
      apply Subtype.ext
      exact (R.node_reachable_tail hef).symm)
  invFun := fun x =>
    let hx : Exists fun w : V => G.Adj (x : V) w :=
      (SimpleGraph.mem_support (G := G)).mp x.property
    let w := hx.choose
    let h := hx.choose_spec
    PermOrbit.of (R.toHypermap).node (⟨(x, w), h⟩ : OrientedEdge G)
  left_inv := by
    intro o
    refine Quotient.inductionOn o ?_
    intro e
    dsimp
    apply Quot.sound
    apply R.node_orbit_of_same_tail
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

theorem nodeOrbitCount_eq_support_card
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).nodeOrbitCount = Fintype.card G.support := by
  classical
  rw [Hypermap.nodeOrbitCount, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (R.nodeOrbitSupportEquiv)

theorem edgeOrbitCount_eq_edgeFinset_card
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.toHypermap).edgeOrbitCount = G.edgeFinset.card := by
  classical
  have hplain : (R.toHypermap).Plain := R.toHypermap_plain
  have hdart_orbits :
      Fintype.card (R.toHypermap).Dart =
        2 * (R.toHypermap).edgeOrbitCount :=
    Hypermap.Plain.card_dart_eq_two_mul_edgeOrbitCount
      (G := R.toHypermap) hplain
  have hdart_edges :
      Fintype.card (R.toHypermap).Dart = 2 * G.edgeFinset.card :=
    orientedEdge_card_eq_twice_card_edges (G := G)
  omega

/-- Reversing all vertex rotations conjugates the new face permutation to
the inverse old face permutation through dart reversal. -/
theorem reverse_face_conj
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    (e : OrientedEdge G) :
    OrientedEdge.edgePerm G ((R.reverse.toHypermap).face e) =
      (R.toHypermap).face.symm (OrientedEdge.edgePerm G e) := by
  change
    OrientedEdge.edgePerm G (R.node (OrientedEdge.edgePerm G e)) =
      (R.toHypermap).face.symm (OrientedEdge.edgePerm G e)
  rfl

theorem reverse_componentCount
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).componentCount =
      (R.toHypermap).componentCount := by
  rw [R.reverse.componentCount_eq_supportComponent_card,
    R.componentCount_eq_supportComponent_card]

theorem reverse_edgeOrbitCount
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).edgeOrbitCount =
      (R.toHypermap).edgeOrbitCount :=
  rfl

theorem reverse_nodeOrbitCount
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).nodeOrbitCount =
      (R.toHypermap).nodeOrbitCount := by
  change Nat.card (PermOrbit R.node.symm) = Nat.card (PermOrbit R.node)
  exact permOrbitCount_symm R.node

theorem reverse_faceOrbitCount
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).faceOrbitCount =
      (R.toHypermap).faceOrbitCount := by
  let E : OrientedEdge G ≃ OrientedEdge G := OrientedEdge.edgePerm G
  calc
    Nat.card (PermOrbit (R.reverse.toHypermap).face) =
        Nat.card (PermOrbit (R.toHypermap).face.symm) :=
      Nat.card_congr
        (permOrbitEquivOfConj E
          (R.reverse.toHypermap).face
          (R.toHypermap).face.symm
          (R.reverse_face_conj))
    _ = Nat.card (PermOrbit (R.toHypermap).face) :=
      permOrbitCount_symm (R.toHypermap).face

theorem reverse_eulerLeft
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).eulerLeft =
      (R.toHypermap).eulerLeft := by
  change
    2 * (R.reverse.toHypermap).componentCount +
        Fintype.card (OrientedEdge G) =
      2 * (R.toHypermap).componentCount +
        Fintype.card (OrientedEdge G)
  rw [R.reverse_componentCount]

theorem reverse_eulerRight
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).eulerRight =
      (R.toHypermap).eulerRight := by
  simp [Hypermap.eulerRight, R.reverse_edgeOrbitCount,
    R.reverse_nodeOrbitCount, R.reverse_faceOrbitCount]

theorem reverse_genus
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).genus =
      (R.toHypermap).genus := by
  simp [Hypermap.genus, R.reverse_eulerLeft, R.reverse_eulerRight]

theorem reverse_eulerPlanar_iff
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).EulerPlanar ↔
      (R.toHypermap).EulerPlanar := by
  simp [Hypermap.EulerPlanar, R.reverse_genus]

theorem reverse_dual_eulerPlanar_iff
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G) :
    (R.reverse.toHypermap).dual.EulerPlanar ↔
      (R.toHypermap).dual.EulerPlanar := by
  rw [Hypermap.dual_eulerPlanar_iff, Hypermap.dual_eulerPlanar_iff]
  exact R.reverse_eulerPlanar_iff

theorem dual_planarBridgelessPlainPrecubic_of
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hplanar : (R.toHypermap).dual.EulerPlanar)
    (hbridgeless : (R.toHypermap).dual.Bridgeless)
    (hprecubic : (R.toHypermap).dual.Precubic) :
    (R.toHypermap).dual.PlanarBridgelessPlainPrecubic where
  base := {
    base := {
      planar := hplanar
      bridgeless := hbridgeless }
    plain := R.toHypermap_dual_plain }
  precubic := hprecubic

end RotationSystem

end FourColor

end Schematic.Math.GraphTheory
