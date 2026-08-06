import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.CanonicalSplit

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- A strict-subdivision model has no leakage out of the left canonical piece
when no edge of any model path lies in the right piece or in the cut path. -/
def ModelEdgesNoRightNoPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  (forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
    e ∈ ((Classical.choice hK).edgePath hxy).edges ->
      e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet) ∧
  (forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
    e ∈ ((Classical.choice hK).edgePath hxy).edges ->
      e ∉ P.pathEdgeGraph.edgeSet)

/-- A strict-subdivision model has no leakage out of the right canonical
piece when no edge of any model path lies in the left piece or in the cut
path. -/
def ModelEdgesNoLeftNoPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  (forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
    e ∈ ((Classical.choice hK).edgePath hxy).edges ->
      e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet) ∧
  (forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
    e ∈ ((Classical.choice hK).edgePath hxy).edges ->
      e ∉ P.pathEdgeGraph.edgeSet)

/-- A strict-subdivision model has no leakage out of the cut-path graph when
no edge of any model path lies in either side piece. -/
def ModelEdgesNoLeftNoRight
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  (forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
    e ∈ ((Classical.choice hK).edgePath hxy).edges ->
      e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet) ∧
  (forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
    e ∈ ((Classical.choice hK).edgePath hxy).edges ->
      e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet)

/-- Source-shaped leakage alternative for a single strict-subdivision model in
the canonical split. -/
def KuratowskiNoLeakageAlt
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  GMIX24Split.ModelEdgesNoRightNoPath P hno_cross hK ∨
    GMIX24Split.ModelEdgesNoLeftNoPath P hno_cross hK ∨
      GMIX24Split.ModelEdgesNoLeftNoRight P hno_cross hK ∨
        Nonempty S.Cross ∨ Nonempty S.Tripod

def ModelEdgeInRightOrPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  Exists fun x : W =>
    Exists fun y : W =>
      Exists fun hxy : K.Adj x y =>
        Exists fun e : Sym2 V =>
          e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
            (e ∈
              (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∨
              e ∈ P.pathEdgeGraph.edgeSet)

def ModelEdgeInLeftOrPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  Exists fun x : W =>
    Exists fun y : W =>
      Exists fun hxy : K.Adj x y =>
        Exists fun e : Sym2 V =>
          e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
            (e ∈
              (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∨
              e ∈ P.pathEdgeGraph.edgeSet)

def ModelEdgeInLeftOrRight
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  Exists fun x : W =>
    Exists fun y : W =>
      Exists fun hxy : K.Adj x y =>
        Exists fun e : Sym2 V =>
          e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
            (e ∈
              (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∨
              e ∈
                (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet)

/-- Endpoint localization for a model edge witnessing `right-or-path`.

This is the first concrete data extracted from a mixed Kuratowski witness: the
chosen model edge path contains an actual host edge whose two endpoints are
both in the right side plus the cut path, or both on the cut path. -/
theorem modelEdgeInRightOrPath_endpoint_localization
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK) :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              ((e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
                (e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet)) := by
  rcases hmixed with ⟨x, y, hxy, e, he, hePart⟩
  refine ⟨x, y, hxy, e, he, ?_⟩
  rcases hePart with heRight | hePath
  · exact Or.inl
      (GMIX24Split.canonicalOfNoCross_right_edge_out_mem_rightSide_or_path
        P hno_cross heRight)
  · exact Or.inr
      (GMIX24Split.pathEdgeGraph_edge_out_mem_pathSet P hePath)

/-- Endpoint localization for a model edge witnessing `left-or-path`. -/
theorem modelEdgeInLeftOrPath_endpoint_localization
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK) :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              ((e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet)) := by
  simpa [GMIX24Split.ModelEdgeInRightOrPath,
    GMIX24Split.ModelEdgeInLeftOrPath] using
    (GMIX24Split.modelEdgeInRightOrPath_endpoint_localization
      P.reverse hno_cross
      (by
        simpa [GMIX24Split.ModelEdgeInRightOrPath,
          GMIX24Split.ModelEdgeInLeftOrPath] using hmixed))

/-- Endpoint localization for a model edge witnessing `left-or-right`. -/
theorem modelEdgeInLeftOrRight_endpoint_localization
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              ((e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.rightSide ∪ P.pathSet)) := by
  rcases hmixed with ⟨x, y, hxy, e, he, hePart⟩
  refine ⟨x, y, hxy, e, he, ?_⟩
  rcases hePart with heLeft | heRight
  · exact Or.inl
      (GMIX24Split.canonicalOfNoCross_left_edge_out_mem_leftSide_or_path
        P hno_cross heLeft)
  · exact Or.inr
      (GMIX24Split.canonicalOfNoCross_right_edge_out_mem_rightSide_or_path
        P hno_cross heRight)

/-- Tagged, support-aware localization for a `right-or-path` mixed model
edge.  Unlike `modelEdgeInRightOrPath_endpoint_localization`, this keeps the
original edge-set tag used by the rural-gluing case split. -/
theorem modelEdgeInRightOrPath_tagged_support_localization
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK) :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e ∈
                    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
                  e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
                (e ∈ P.pathEdgeGraph.edgeSet ∧
                  e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet)) := by
  classical
  let M := Classical.choice hK
  rcases hmixed with ⟨x, y, hxy, e, he, hePart⟩
  have hsupp := Walk.out_mem_support_of_mem_edges (p := M.edgePath hxy) he
  refine ⟨x, y, hxy, e, he, hsupp.1, hsupp.2, ?_⟩
  rcases hePart with heRight | hePath
  · exact Or.inl
      ⟨heRight,
        (GMIX24Split.canonicalOfNoCross_right_edge_out_mem_rightSide_or_path
          P hno_cross heRight).1,
        (GMIX24Split.canonicalOfNoCross_right_edge_out_mem_rightSide_or_path
          P hno_cross heRight).2⟩
  · exact Or.inr
      ⟨hePath,
        (GMIX24Split.pathEdgeGraph_edge_out_mem_pathSet P hePath).1,
        (GMIX24Split.pathEdgeGraph_edge_out_mem_pathSet P hePath).2⟩

/-- Tagged, support-aware localization for a `left-or-path` mixed model
edge. -/
theorem modelEdgeInLeftOrPath_tagged_support_localization
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK) :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e ∈
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
                  e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (e ∈ P.pathEdgeGraph.edgeSet ∧
                  e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet)) := by
  simpa [GMIX24Split.ModelEdgeInRightOrPath,
    GMIX24Split.ModelEdgeInLeftOrPath] using
    (GMIX24Split.modelEdgeInRightOrPath_tagged_support_localization
      P.reverse hno_cross
      (by
        simpa [GMIX24Split.ModelEdgeInRightOrPath,
          GMIX24Split.ModelEdgeInLeftOrPath] using hmixed))

/-- Tagged, support-aware localization for a `left-or-right` mixed model
edge. -/
theorem modelEdgeInLeftOrRight_tagged_support_localization
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e ∈
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
                  e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (e ∈
                    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
                  e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.rightSide ∪ P.pathSet)) := by
  classical
  let M := Classical.choice hK
  rcases hmixed with ⟨x, y, hxy, e, he, hePart⟩
  have hsupp := Walk.out_mem_support_of_mem_edges (p := M.edgePath hxy) he
  refine ⟨x, y, hxy, e, he, hsupp.1, hsupp.2, ?_⟩
  rcases hePart with heLeft | heRight
  · exact Or.inl
      ⟨heLeft,
        (GMIX24Split.canonicalOfNoCross_left_edge_out_mem_leftSide_or_path
          P hno_cross heLeft).1,
        (GMIX24Split.canonicalOfNoCross_left_edge_out_mem_leftSide_or_path
          P hno_cross heLeft).2⟩
  · exact Or.inr
      ⟨heRight,
        (GMIX24Split.canonicalOfNoCross_right_edge_out_mem_rightSide_or_path
          P hno_cross heRight).1,
        (GMIX24Split.canonicalOfNoCross_right_edge_out_mem_rightSide_or_path
          P hno_cross heRight).2⟩

/-- Endpoint-localized form of a model edge lying in the right side or on the
cut path.  This is the geometric data used by the source mixed-Kuratowski
argument. -/
def ModelEdgeEndpointInRightOrPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (_hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  Exists fun x : W =>
    Exists fun y : W =>
      Exists fun hxy : K.Adj x y =>
        Exists fun e : Sym2 V =>
          e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
            ((e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
              (e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet))

/-- Endpoint-localized form of a model edge lying in the left side or on the
cut path. -/
def ModelEdgeEndpointInLeftOrPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (_hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  Exists fun x : W =>
    Exists fun y : W =>
      Exists fun hxy : K.Adj x y =>
        Exists fun e : Sym2 V =>
          e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
            ((e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
              (e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet))

/-- Endpoint-localized form of a model edge lying in one of the two side
pieces. -/
def ModelEdgeEndpointInLeftOrRight
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (_hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop :=
  Exists fun x : W =>
    Exists fun y : W =>
      Exists fun hxy : K.Adj x y =>
        Exists fun e : Sym2 V =>
          e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
            ((e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
              (e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                e.out.2 ∈ P.rightSide ∪ P.pathSet))

theorem modelEdgeEndpointInRightOrPath_of_modelEdgeInRightOrPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK) :
    GMIX24Split.ModelEdgeEndpointInRightOrPath P hno_cross hK := by
  simpa [GMIX24Split.ModelEdgeEndpointInRightOrPath] using
    GMIX24Split.modelEdgeInRightOrPath_endpoint_localization
      P hno_cross hmixed

theorem modelEdgeEndpointInLeftOrPath_of_modelEdgeInLeftOrPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK) :
    GMIX24Split.ModelEdgeEndpointInLeftOrPath P hno_cross hK := by
  simpa [GMIX24Split.ModelEdgeEndpointInLeftOrPath] using
    GMIX24Split.modelEdgeInLeftOrPath_endpoint_localization
      P hno_cross hmixed

theorem modelEdgeEndpointInLeftOrRight_of_modelEdgeInLeftOrRight
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed : GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) :
    GMIX24Split.ModelEdgeEndpointInLeftOrRight P hno_cross hK := by
  simpa [GMIX24Split.ModelEdgeEndpointInLeftOrRight] using
    GMIX24Split.modelEdgeInLeftOrRight_endpoint_localization
      P hno_cross hmixed

/-- Endpoint-localized package for the three mixed edges in an ambient
Kuratowski subdivision. -/
structure MixedEdgeEndpointWitnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop where
  right_or_path :
    GMIX24Split.ModelEdgeEndpointInRightOrPath P hno_cross hK
  left_or_path :
    GMIX24Split.ModelEdgeEndpointInLeftOrPath P hno_cross hK
  left_or_right :
    GMIX24Split.ModelEdgeEndpointInLeftOrRight P hno_cross hK

theorem mixedEdgeEndpointWitnesses_of_mixed_edge_witnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hmixed :
      GMIX24Split.ModelEdgeInRightOrPath P hno_cross hK ∧
        GMIX24Split.ModelEdgeInLeftOrPath P hno_cross hK ∧
          GMIX24Split.ModelEdgeInLeftOrRight P hno_cross hK) :
    GMIX24Split.MixedEdgeEndpointWitnesses P hno_cross hK where
  right_or_path :=
    GMIX24Split.modelEdgeEndpointInRightOrPath_of_modelEdgeInRightOrPath
      P hno_cross hmixed.1
  left_or_path :=
    GMIX24Split.modelEdgeEndpointInLeftOrPath_of_modelEdgeInLeftOrPath
      P hno_cross hmixed.2.1
  left_or_right :=
    GMIX24Split.modelEdgeEndpointInLeftOrRight_of_modelEdgeInLeftOrRight
      P hno_cross hmixed.2.2

/-- Support-aware endpoint-localized package for the three mixed edges in an
ambient Kuratowski subdivision.  Each localized host edge is also recorded as
lying on the support of its strict-subdivision source-edge path. -/
structure MixedEdgeEndpointSupportWitnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop where
  right_or_path :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
                (e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet))
  left_or_path :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet))
  left_or_right :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.rightSide ∪ P.pathSet))

/-- Tagged support-aware endpoint-localized package for the three mixed edges
in an ambient Kuratowski subdivision.

This is sharper than `MixedEdgeEndpointSupportWitnesses`: it keeps the
original edge-set tag (`left`, `right`, or `path`) attached to each localized
host edge.  The mixed-edge Kuratowski proof needs these tags to distinguish
the genuine side-switching cases from edges already contained in the cut
path. -/
structure MixedEdgeTaggedSupportWitnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Prop where
  right_or_path :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e ∈
                    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
                  e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
                (e ∈ P.pathEdgeGraph.edgeSet ∧
                  e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet))
  left_or_path :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e ∈
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
                  e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (e ∈ P.pathEdgeGraph.edgeSet ∧
                  e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet))
  left_or_right :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : K.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges ∧
              e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support ∧
              ((e ∈
                    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
                  e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
                (e ∈
                    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
                  e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
                  e.out.2 ∈ P.rightSide ∪ P.pathSet))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
