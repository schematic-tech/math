import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.TripodStructure
import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.ThreeVertexLinkages

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

def legLinkage {S : GeneralSociety V} (T : S.Tripod) :
    ThreeVertexLinkage S.graph T.attach T.boundary where
  targetEquiv := Equiv.refl (Fin 3)
  path := T.leg
  isPath := T.leg_isPath
  pairwise_vertex_disjoint := by
    intro i j hij
    simpa using T.legs_pairwise_disjoint i j hij

/-- The three side-tripod legs remain a full linkage after mapping the side
society into an ambient society.

This is the source GM IX `(2.2)` starting linkage for the side-tripod
paragraph: the later endpoint subcases may pre-fix one or two of these paths,
but the augmenting theorem needs the original full linkage in the ambient
graph as its base object. -/
def legLinkageMapLe {S H : GeneralSociety V}
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph) :
    ThreeVertexLinkage S.graph T.attach T.boundary where
  targetEquiv := Equiv.refl (Fin 3)
  path i := (T.leg i).mapLe hgraph
  isPath i := by
    simpa using (SimpleGraph.Walk.mapLe_isPath hgraph).mpr (T.leg_isPath i)
  pairwise_vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact Set.disjoint_left.mp (T.legs_pairwise_disjoint i j hij)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzi)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzj)

/-- Build a society tripod from the paper's linkage form.

This is the direct bridge to GM IX `(2.2)`: once the three rim paths and their
internal attachment vertices are fixed, any vertex-disjoint linkage from those
attachments to three boundary vertices (allowing the boundary matching to be
permuted) is exactly the leg data of a `Tripod`. -/
def ofThreeVertexLinkage {S : GeneralSociety V}
    (left right : V)
    (hleft_ne_right : left ≠ right)
    (rim : Fin 3 -> S.graph.Walk left right)
    (hrim_path : forall i : Fin 3, (rim i).IsPath)
    (attach : Fin 3 -> V)
    (hattach_mem_rim : forall i : Fin 3, attach i ∈ Walk.InternalVertices (rim i))
    (boundary : Fin 3 -> V)
    (hboundary_mem : forall i : Fin 3, boundary i ∈ S.boundarySet)
    (hboundary_injective : Function.Injective boundary)
    (L : ThreeVertexLinkage S.graph attach boundary)
    (hrim_disjoint :
      forall i j : Fin 3, i ≠ j ->
        Disjoint (Walk.InternalVertices (rim i)) (Walk.InternalVertices (rim j)))
    (hlegs_meet_rims :
      forall i j : Fin 3, forall v : V,
        v ∈ (L.path i).support ->
          v ∈ (rim j).support ->
            v = attach i) :
    S.Tripod where
  left := left
  right := right
  left_ne_right := hleft_ne_right
  rim := rim
  rim_isPath := hrim_path
  attach := attach
  attach_mem_rim := hattach_mem_rim
  boundary i := boundary (L.targetEquiv i)
  boundary_mem i := hboundary_mem (L.targetEquiv i)
  boundary_injective := by
    intro i j hij
    exact L.targetEquiv.injective (hboundary_injective hij)
  leg := L.path
  leg_isPath := L.isPath
  rim_internals_disjoint := hrim_disjoint
  legs_pairwise_disjoint := L.pairwise_vertex_disjoint
  legs_meet_rims_only_at_attach := hlegs_meet_rims

end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
