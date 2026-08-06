import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.GraphDecomposition

/-! Ordered tripod contacts on a selected cut path and their reversal. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety.GMIX24CutPath

variable [DecidableEq V]

/-- The source-combinatorial data saying that three tripod feet occur in a
specified order on the selected cut path.  Transition theorems consume this
same package in both orientations, so reversal belongs on the package rather
than being re-proved at every call site. -/
structure OrderedTripodData
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (i j k : Fin 3) : Prop where
  first_ne_middle : i ≠ j
  first_ne_last : i ≠ k
  middle_ne_last : j ≠ k
  first_mem_path : T.boundary i ∈ P.pathSet
  middle_mem_path : T.boundary j ∈ P.pathSet
  last_mem_path : T.boundary k ∈ P.pathSet
  first_lt_middle :
    Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j)
  middle_lt_last :
    Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k)
  path_contacts : ∀ z : V, z ∈ P.pathSet → z ∈ T.vertexSet →
    ∃ m : Fin 3, z = T.boundary m

/-- Reverse both the cut-path orientation and the ordered tripod indices. -/
def OrderedTripodData.reverse
    {S H : GeneralSociety V}
    {P : GMIX24CutPath S} {T : H.Tripod}
    {i j k : Fin 3}
    (O : OrderedTripodData P T i j k) :
    OrderedTripodData P.reverse T k j i where
  first_ne_middle := O.middle_ne_last.symm
  first_ne_last := O.first_ne_last.symm
  middle_ne_last := O.first_ne_middle.symm
  first_mem_path := by simpa using O.last_mem_path
  middle_mem_path := by simpa using O.middle_mem_path
  last_mem_path := by simpa using O.first_mem_path
  first_lt_middle :=
    (P.supportIndex_reverse_lt_iff O.last_mem_path O.middle_mem_path).2
      O.middle_lt_last
  middle_lt_last :=
    (P.supportIndex_reverse_lt_iff O.middle_mem_path O.first_mem_path).2
      O.first_lt_middle
  path_contacts := by
    intro z hz_path hz_tripod
    exact O.path_contacts z (by simpa using hz_path) hz_tripod

end GeneralSociety.GMIX24CutPath

end Schematic.Math.GraphTheory
