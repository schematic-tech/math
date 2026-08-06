import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

noncomputable def canonicalOfNoCross_reverseRightCross
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Cross :=
  (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm ▸ X

noncomputable def canonicalOfNoCross_reverseLeftCross
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).rightSociety.Cross :=
  (GMIX24Split.canonicalOfNoCross_reverse_rightSociety P hno_cross).symm ▸ X

noncomputable def crossOffPathEndpointFinset
    {H : GeneralSociety V} (X : H.Cross)
    {S : GeneralSociety V} (P : GMIX24CutPath S) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun i => X.endpoints.endpoint i ∉ P.pathSet

noncomputable def crossOffPathEndpointCount
    {H : GeneralSociety V} (X : H.Cross)
    {S : GeneralSociety V} (P : GMIX24CutPath S) : Nat :=
  (crossOffPathEndpointFinset X P).card

noncomputable def endpointOffPathFinset
    (endpoint : Fin 4 -> V)
    {S : GeneralSociety V} (P : GMIX24CutPath S) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun i => endpoint i ∉ P.pathSet

noncomputable def endpointOffPathCount
    (endpoint : Fin 4 -> V)
    {S : GeneralSociety V} (P : GMIX24CutPath S) : Nat :=
  (endpointOffPathFinset endpoint P).card

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
