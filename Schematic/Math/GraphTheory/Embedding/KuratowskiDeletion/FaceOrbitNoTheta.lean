import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.ThetaContours


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace EdgeDeletion

/-- Being carried by a face orbit is exactly containment in the canonical
face-orbit subgraph. -/
theorem subgraphCarriedByFaceOrbit_iff_le_faceOrbitSubgraph
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph} :
    SubgraphCarriedByFaceOrbit R e S ↔ S ≤ faceOrbitSubgraph R e := by
  constructor
  · intro hS
    constructor
    · intro x hx
      exact hS.1 hx
    · intro x y hxy
      exact hS.2 hxy
  · intro hS
    constructor
    · intro x hx
      exact hS.1 hx
    · intro x y hxy
      exact hS.2 hxy

/-- Carried-by-face-orbit is monotone when passing to a smaller subgraph. -/
theorem SubgraphCarriedByFaceOrbit.mono
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S T : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    (hTS : T ≤ S) :
    SubgraphCarriedByFaceOrbit R e T := by
  exact subgraphCarriedByFaceOrbit_iff_le_faceOrbitSubgraph.mpr
    (hTS.trans
      (subgraphCarriedByFaceOrbit_iff_le_faceOrbitSubgraph.mp hS))

/-- Homeomorphic-theta freeness is monotone when passing to a smaller
subgraph. -/
theorem not_containsHomeomorphicTheta_subgraph_of_le
    {W : Type u}
    {H : SimpleGraph W}
    {S T : H.Subgraph}
    (hTS : T ≤ S)
    (hno : Not (ContainsHomeomorphicTheta S.coe)) :
    Not (ContainsHomeomorphicTheta T.coe) := by
  intro htheta
  exact hno
    (ContainsHomeomorphicTheta.map
      (SimpleGraph.Subgraph.inclusion hTS)
      (SimpleGraph.Subgraph.inclusion.injective hTS)
      htheta)

/-- The full selected contraction face-boundary subgraph is carried by the
selected face orbit. -/
theorem contractionFaceBoundarySubgraph_carriedByFaceOrbit
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    SubgraphCarriedByFaceOrbit R e
      (contractionFaceBoundarySubgraph hab R e) := by
  constructor
  · intro x hx
    rcases hx with ⟨d, hd, hdx⟩
    exact ⟨d, (mem_contractionFaceBoundary hab R e d).mp hd, hdx⟩
  · intro x y hxy
    rcases hxy with ⟨d, hd, hxy⟩
    exact ⟨d, (mem_contractionFaceBoundary hab R e d).mp hd, hxy⟩

/-- The outside part of the selected contraction face boundary, after removing
the collapsed vertex and the darts incident with it.  This is the graph-side
object corresponding to the boundary `C` of `G/xy - xy` in the
Skopenkov/Makarychev proof. -/
def contractionFaceBoundaryOutsideSubgraph
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (GraphContraction.collapseEdge G hab).graph.Subgraph where
  verts := {x |
    x ≠ (none : (GraphContraction.collapseEdge G hab).Target) ∧
      Exists fun d : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
        d ∈ contractionFaceBoundary hab R e ∧
          d.tail ≠ (none : (GraphContraction.collapseEdge G hab).Target) ∧
          d.head ≠ (none : (GraphContraction.collapseEdge G hab).Target) ∧
          (d.tail = x ∨ d.head = x)}
  Adj x y :=
    Exists fun d : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
      d ∈ contractionFaceBoundary hab R e ∧
        d.tail ≠ (none : (GraphContraction.collapseEdge G hab).Target) ∧
        d.head ≠ (none : (GraphContraction.collapseEdge G hab).Target) ∧
        ((d.tail = x ∧ d.head = y) ∨ (d.tail = y ∧ d.head = x))
  adj_sub := by
    rintro x y ⟨d, _hd, _htail, _hhead, hxy | hyx⟩
    · simpa [hxy.1, hxy.2] using d.adj
    · simpa [hyx.1, hyx.2] using d.adj.symm
  edge_vert := by
    rintro x y ⟨d, hd, htail_ne, hhead_ne, hxy | hyx⟩
    · exact ⟨by simpa [hxy.1] using htail_ne,
        d, hd, htail_ne, hhead_ne, Or.inl hxy.1⟩
    · exact ⟨by simpa [hyx.2] using hhead_ne,
        d, hd, htail_ne, hhead_ne, Or.inr hyx.2⟩
  symm := by
    rintro x y ⟨d, hd, htail_ne, hhead_ne, hxy | hyx⟩
    · exact ⟨d, hd, htail_ne, hhead_ne, Or.inr hxy⟩
    · exact ⟨d, hd, htail_ne, hhead_ne, Or.inl hyx⟩

theorem contractionFaceBoundaryOutsideSubgraph_tail_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e)
    (htail :
      d.tail ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hhead :
      d.head ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    d.tail ∈ (contractionFaceBoundaryOutsideSubgraph hab R e).verts :=
  ⟨htail, d, hd, htail, hhead, Or.inl rfl⟩

theorem contractionFaceBoundaryOutsideSubgraph_head_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e)
    (htail :
      d.tail ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hhead :
      d.head ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    d.head ∈ (contractionFaceBoundaryOutsideSubgraph hab R e).verts :=
  ⟨hhead, d, hd, htail, hhead, Or.inr rfl⟩

theorem contractionFaceBoundaryOutsideSubgraph_adj_of_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e)
    (htail :
      d.tail ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hhead :
      d.head ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    (contractionFaceBoundaryOutsideSubgraph hab R e).Adj d.tail d.head :=
  ⟨d, hd, htail, hhead, Or.inl ⟨rfl, rfl⟩⟩

/-- The outside selected contraction face-boundary subgraph is still carried
by the selected face orbit. -/
theorem contractionFaceBoundaryOutsideSubgraph_carriedByFaceOrbit
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    SubgraphCarriedByFaceOrbit R e
      (contractionFaceBoundaryOutsideSubgraph hab R e) := by
  constructor
  · intro x hx
    rcases hx with ⟨_hne, d, hd, _htail, _hhead, hdx⟩
    exact ⟨d, (mem_contractionFaceBoundary hab R e d).mp hd, hdx⟩
  · intro x y hxy
    rcases hxy with ⟨d, hd, _htail, _hhead, hxy⟩
    exact ⟨d, (mem_contractionFaceBoundary hab R e d).mp hd, hxy⟩

/-- The precise Euler-planar face-boundary obstruction still needed from the
Skopenkov/Makarychev argument: a subgraph carried by one face orbit of a
genus-zero rotation system contains no homeomorphic theta. -/
def FaceOrbitNoThetaTheorem : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (_hplanar : (R.toHypermap).EulerPlanar)
    (e : OrientedEdge H)
    (S : H.Subgraph),
      SubgraphCarriedByFaceOrbit R e S →
        Not (ContainsHomeomorphicTheta S.coe)

/-- Jordan-facing form of the face-boundary obstruction.  This isolates the
remaining topological content from the already checked Coq `planar_Jordan`
port: once an Euler-planar rotation hypermap is known to be Jordan, a single
face-orbit boundary should contain no homeomorphic theta. -/
def FaceOrbitNoThetaFromJordanTheorem : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (_hJ : (R.toHypermap).Jordan)
    (e : OrientedEdge H),
      Not (ContainsHomeomorphicTheta (faceOrbitSubgraph R e).coe)

/-- A theta carried by one face orbit yields two same-oriented branch ports.
Trimming their alternate connector and the common-node contour produces the
alternating three-path configuration forbidden by Jordan. -/
theorem faceOrbitNoThetaFromJordan_proved :
    FaceOrbitNoThetaFromJordanTheorem.{u} := by
  intro W _ _ H _ R hJ e htheta
  rcases
      faceOrbitSubgraph_containsHomeomorphicTheta_sameOrientationPair
        R e htheta with
    ⟨P⟩
  rcases P.exists_crossingData with ⟨D⟩
  rcases D.exists_arcs with ⟨A⟩
  exact A.false_of_jordan hJ

/-- It is enough to prove theta-freeness for the canonical face-orbit
subgraph.  Arbitrary carried subgraphs then follow by monotonicity. -/
theorem faceOrbitNoThetaTheorem_of_faceOrbitSubgraph
    (hface :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {H : SimpleGraph W} [DecidableRel H.Adj]
        (R : RotationSystem H)
        (_hplanar : (R.toHypermap).EulerPlanar)
        (e : OrientedEdge H),
          Not (ContainsHomeomorphicTheta (faceOrbitSubgraph R e).coe)) :
    FaceOrbitNoThetaTheorem.{u} := by
  intro W _ _ H _ R hplanar e S hS
  exact not_containsHomeomorphicTheta_subgraph_of_le
    (subgraphCarriedByFaceOrbit_iff_le_faceOrbitSubgraph.mp hS)
    (hface R hplanar e)

/-- Euler-planar face-boundary theta-freeness follows from two independent
inputs: the hypermap theorem `EulerPlanar -> Jordan`, and the Jordan-facing
one-face no-theta lemma. -/
theorem faceOrbitNoThetaTheorem_of_jordan
    (hJordan : ∀ G : Hypermap.{u}, G.EulerPlanar → G.Jordan)
    (hface : FaceOrbitNoThetaFromJordanTheorem.{u}) :
    FaceOrbitNoThetaTheorem.{u} :=
  faceOrbitNoThetaTheorem_of_faceOrbitSubgraph
    (fun R hplanar e => hface R (hJordan R.toHypermap hplanar) e)

/-- Every subgraph carried by one face orbit of an Euler-planar rotation
system is theta-free. -/
theorem faceOrbitNoTheta_proved :
    FaceOrbitNoThetaTheorem.{u} :=
  faceOrbitNoThetaTheorem_of_jordan
    Unavoidability.eulerPlanar_jordan
    faceOrbitNoThetaFromJordan_proved

end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
