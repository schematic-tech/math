import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.SubdivisionObstructions
import Schematic.Math.GraphTheory.Planarity.Basic

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph

namespace RotationSoundness
/-- Every graph carrying an Euler rotation system is planar in the strict
Kuratowski sense used by the paper-facing graph library. -/
theorem hasEulerRotationSystem_isPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : HasEulerRotationSystem G) :
    Schematic.Math.GraphTheory.IsPlanar G :=
  ⟨fun hK5 =>
      not_hasEulerRotationSystem_of_containsStrictSubdivision_K5 hK5 hG,
    fun hK33 =>
      not_hasEulerRotationSystem_of_containsStrictSubdivision_K33 hK33 hG⟩



end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
