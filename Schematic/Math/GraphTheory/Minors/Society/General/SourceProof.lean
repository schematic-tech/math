import Schematic.Math.GraphTheory.Minors.Society.General.Obligations

/-! The public GM IX `(2.4)` source-proof endpoint. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The single public source endpoint for Graph Minors IX `(2.4)`.

The three-boundary/high-degree specialization in
`Schematic.Math.GraphTheory.Minors.Society.ThreeBoundary`
routes through this theorem. -/
theorem GMIX24Statement.source_proof
    [Fintype V] [Fintype (Sym2 V)] [DecidableEq V] :
    GMIX24Statement (V := V) := by
  classical
  refine
    GMIX24Statement.of_side_tripod_free_rural_gluing
      (V := V) (fun S => Classical.decRel S.graph.Adj) ?_
  intro S hthree hno_cross hno_tripod hlarge _hnot_rural P
  let O :=
    GMIX24SourceProof.local_obligations
      (S := S) hthree hno_cross hno_tripod hlarge P
  exact ⟨O.side_tripods.left_free, O.side_tripods.right_free,
    O.glues_rural⟩

end GeneralSociety

end Schematic.Math.GraphTheory
