import Schematic.Math.GraphTheory.Embedding.Wagner.AttachmentLocalization

/-! The strict-subdivision form of `wagner_no_cross`. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner
/-- Strict-subdivision form of Coq's `wagner_no_cross`.  The returned first
arc is the closed segment from one `x`-attachment to the next: all
`y`-attachments lie on it and its interior has no `x`-attachment. -/
theorem IsPlanar.wagner_no_cross
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hplanar : IsPlanar G)
    {r x y xa xb ya yb : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hxaC : xa ∈ C.support) (hxbC : xb ∈ C.support)
    (hxa_ne_xb : xa ≠ xb)
    (hxxa : G.Adj x xa) (hxxb : G.Adj x xb)
    (hyaC : ya ∈ C.support) (hybC : yb ∈ C.support)
    (hya_ne_yb : ya ≠ yb)
    (hyya : G.Adj y ya) (hyyb : G.Adj y yb)
    (hxy : G.Adj x y)
    (hxC : x ∉ C.support)
    (hyC : y ∉ C.support) :
    Exists fun u : V =>
      Exists fun v : V =>
        Exists fun A : CycleTwoArcs C (x1 := u) (x2 := v) =>
          G.Adj x u ∧ G.Adj x v ∧
            (forall z, z ∈ C.support -> G.Adj y z ->
              z ∈ A.first.support) ∧
              (forall z, z ∈ Walk.InternalVertices A.first ->
                ¬ G.Adj x z) := by
  classical
  by_cases hnotSubset :
      Exists fun z : V =>
        z ∈ C.support ∧ G.Adj y z ∧ ¬ G.Adj x z
  · rcases hnotSubset with ⟨z, hzC, hyz, hxz⟩
    rcases IsPlanar.exists_attachment_arc_of_second_not_first hplanar
        C hC hxaC hxbC hxa_ne_xb hxy hxxa hxxb hzC hyz hxz hxC hyC with
      ⟨u, v, A, hxu, hxv, _hzA, hallY, hnoX⟩
    exact ⟨u, v, A, hxu, hxv, hallY, hnoX⟩
  · have hYX :
        forall z, z ∈ C.support -> G.Adj y z -> G.Adj x z := by
      intro z hzC hyz
      by_contra hxz
      exact hnotSubset ⟨z, hzC, hyz, hxz⟩
    rcases IsPlanar.exists_attachment_arc_of_second_subset_first hplanar
        C hC hyaC hybC hya_ne_yb hxy hyya hyyb hYX hxC hyC with
      ⟨A, hxya, hxyb, hallY, hnoX⟩
    exact ⟨yb, ya, A, hxyb, hxya, hallY, hnoX⟩

end Wagner

end FourColor

end Schematic.Math.GraphTheory
