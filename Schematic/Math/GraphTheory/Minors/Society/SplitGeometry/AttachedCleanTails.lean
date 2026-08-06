import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.EndpointPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Named predicate for the clean right-side tail alternative from a selected
right endpoint path.  This keeps the final mixed-Kuratowski tag cases from
repeating the full existential tail package. -/
def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.CleanTailToRightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath) : Prop :=
  Exists fun x : V =>
    Exists fun a : V =>
      Exists fun tail : S.graph.Walk x a =>
        x ∈ R.path.support ∧
          a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
            (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                  forall w : V,
                    w ∈ tail.support -> w ∈ R.path.support -> w = x

/-- Named predicate for the clean left-side tail alternative from a selected
left endpoint path. -/
def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.CleanTailToLeftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath) : Prop :=
  Exists fun x : V =>
    Exists fun a : V =>
      Exists fun tail : S.graph.Walk x a =>
        x ∈ L.path.support ∧
          a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
            (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                  forall w : V,
                    w ∈ tail.support -> w ∈ L.path.support -> w = x

/-- Named predicate for the clean left-side tail alternative from a selected
side endpoint path. -/
def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.CleanTailToLeftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath) : Prop :=
  Exists fun x : V =>
    Exists fun a : V =>
      Exists fun tail : S.graph.Walk x a =>
        x ∈ E.path.support ∧
          a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
            (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                  forall w : V,
                    w ∈ tail.support -> w ∈ E.path.support -> w = x

/-- Named predicate for the clean right-side tail alternative from a selected
side endpoint path. -/
def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.CleanTailToRightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath) : Prop :=
  Exists fun x : V =>
    Exists fun a : V =>
      Exists fun tail : S.graph.Walk x a =>
        x ∈ E.path.support ∧
          a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
            (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                  forall w : V,
                    w ∈ tail.support -> w ∈ E.path.support -> w = x

/-- A right-side clean tail together with an initial attachment segment from
an arbitrary start vertex to the tail start.  The attachment segment is
required to stay on the selected endpoint path, so the clean-tail condition
immediately proves that the concatenation is a path. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.AttachedCleanTailToRightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath) (start : V) : Type _ where
  x : V
  a : V
  attach : S.graph.Walk start x
  tail : S.graph.Walk x a
  x_mem_path : x ∈ R.path.support
  a_mem_rightBoundaryArc : a ∈ P.rightBoundaryArc
  attach_isPath : attach.IsPath
  attach_support_subset_path :
    forall w : V, w ∈ attach.support -> w ∈ R.path.support
  tail_isPath : tail.IsPath
  tail_support_right :
    forall w : V, w ∈ tail.support -> w ∈ P.rightSide
  tail_support_outside :
    forall w : V, w ∈ tail.support -> w ∈ P.outside
  tail_internal_boundary_clean :
    Walk.InternalVertices tail ∩ S.boundarySet = ∅
  tail_clean_path :
    forall w : V, w ∈ tail.support -> w ∈ R.path.support -> w = x

/-- The concatenated right attached clean tail. -/
noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.AttachedCleanTailToRightBoundaryArc.walk
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {R : C.RightEndpointPath} {start : V}
    (A : R.AttachedCleanTailToRightBoundaryArc start) :
    S.graph.Walk start A.a :=
  A.attach.append A.tail

private theorem append_isPath_of_support_inter_eq_endpoint
    {G : SimpleGraph V} {start x a : V}
    (attach : G.Walk start x) (tail : G.Walk x a)
    (hattach : attach.IsPath) (htail : tail.IsPath)
    (hinter :
      forall w : V,
        w ∈ attach.support -> w ∈ tail.support -> w = x) :
    (attach.append tail).IsPath := by
  exact
    Walk.IsPath.append_of_support_inter_eq_endpoint
      hattach htail hinter

private theorem append_support_cases
    {G : SimpleGraph V} {start x a : V}
    (attach : G.Walk start x) (tail : G.Walk x a)
    (firstSet secondSet : Set V)
    (hattach : forall w : V, w ∈ attach.support -> w ∈ firstSet)
    (htail : forall w : V, w ∈ tail.support -> w ∈ secondSet)
    {w : V} (hw : w ∈ (attach.append tail).support) :
    w ∈ firstSet ∨ w ∈ secondSet := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hwAttach | hwTail
  · exact Or.inl (hattach w hwAttach)
  · exact Or.inr (htail w hwTail)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.AttachedCleanTailToRightBoundaryArc.walk_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {R : C.RightEndpointPath} {start : V}
    (A : R.AttachedCleanTailToRightBoundaryArc start) :
    A.walk.IsPath := by
  exact
    append_isPath_of_support_inter_eq_endpoint
      A.attach A.tail A.attach_isPath A.tail_isPath
      (fun w hwAttach hwTail =>
        A.tail_clean_path w hwTail
          (A.attach_support_subset_path w hwAttach))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.AttachedCleanTailToRightBoundaryArc.walk_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {R : C.RightEndpointPath} {start : V}
    (A : R.AttachedCleanTailToRightBoundaryArc start)
    {w : V}
    (hw : w ∈ A.walk.support) :
    w ∈ R.path.support ∨ w ∈ P.rightSide := by
  exact
    append_support_cases A.attach A.tail
      {v : V | v ∈ R.path.support} P.rightSide
      A.attach_support_subset_path A.tail_support_right
      (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.AttachedCleanTailToRightBoundaryArc.walk] using hw)

/-- Build a right attached clean tail from a clean-tail package and any
attachment-segment constructor that stays inside the selected endpoint path. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.CleanTailToRightBoundaryArc.exists_attached
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {R : C.RightEndpointPath} {start : V}
    (hclean : R.CleanTailToRightBoundaryArc)
    (hattach :
      forall {x : V}, x ∈ R.path.support ->
        Exists fun q : S.graph.Walk start x =>
          q.IsPath ∧
            forall w : V, w ∈ q.support -> w ∈ R.path.support) :
    Nonempty (R.AttachedCleanTailToRightBoundaryArc start) := by
  rcases hclean with
    ⟨x, a, tail, hx, ha, htail_path, htail_right, htail_outside,
      htail_boundary, htail_clean⟩
  rcases hattach hx with ⟨q, hq_path, hq_subset⟩
  exact ⟨{
    x := x
    a := a
    attach := q
    tail := tail
    x_mem_path := hx
    a_mem_rightBoundaryArc := ha
    attach_isPath := hq_path
    attach_support_subset_path := hq_subset
    tail_isPath := htail_path
    tail_support_right := htail_right
    tail_support_outside := htail_outside
    tail_internal_boundary_clean := htail_boundary
    tail_clean_path := htail_clean }⟩

/-- Left-side analogue of `AttachedCleanTailToRightBoundaryArc`. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.AttachedCleanTailToLeftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath) (start : V) : Type _ where
  x : V
  a : V
  attach : S.graph.Walk start x
  tail : S.graph.Walk x a
  x_mem_path : x ∈ L.path.support
  a_mem_leftBoundaryArc : a ∈ P.leftBoundaryArc
  attach_isPath : attach.IsPath
  attach_support_subset_path :
    forall w : V, w ∈ attach.support -> w ∈ L.path.support
  tail_isPath : tail.IsPath
  tail_support_left :
    forall w : V, w ∈ tail.support -> w ∈ P.leftSide
  tail_support_outside :
    forall w : V, w ∈ tail.support -> w ∈ P.outside
  tail_internal_boundary_clean :
    Walk.InternalVertices tail ∩ S.boundarySet = ∅
  tail_clean_path :
    forall w : V, w ∈ tail.support -> w ∈ L.path.support -> w = x

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.AttachedCleanTailToLeftBoundaryArc.walk
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {L : C.LeftEndpointPath} {start : V}
    (A : L.AttachedCleanTailToLeftBoundaryArc start) :
    S.graph.Walk start A.a :=
  A.attach.append A.tail

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.AttachedCleanTailToLeftBoundaryArc.walk_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {L : C.LeftEndpointPath} {start : V}
    (A : L.AttachedCleanTailToLeftBoundaryArc start) :
    A.walk.IsPath := by
  exact
    append_isPath_of_support_inter_eq_endpoint
      A.attach A.tail A.attach_isPath A.tail_isPath
      (fun w hwAttach hwTail =>
        A.tail_clean_path w hwTail
          (A.attach_support_subset_path w hwAttach))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.AttachedCleanTailToLeftBoundaryArc.walk_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {L : C.LeftEndpointPath} {start : V}
    (A : L.AttachedCleanTailToLeftBoundaryArc start)
    {w : V}
    (hw : w ∈ A.walk.support) :
    w ∈ L.path.support ∨ w ∈ P.leftSide := by
  exact
    append_support_cases A.attach A.tail
      {v : V | v ∈ L.path.support} P.leftSide
      A.attach_support_subset_path A.tail_support_left
      (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.AttachedCleanTailToLeftBoundaryArc.walk] using hw)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.CleanTailToLeftBoundaryArc.exists_attached
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {L : C.LeftEndpointPath} {start : V}
    (hclean : L.CleanTailToLeftBoundaryArc)
    (hattach :
      forall {x : V}, x ∈ L.path.support ->
        Exists fun q : S.graph.Walk start x =>
          q.IsPath ∧
            forall w : V, w ∈ q.support -> w ∈ L.path.support) :
    Nonempty (L.AttachedCleanTailToLeftBoundaryArc start) := by
  rcases hclean with
    ⟨x, a, tail, hx, ha, htail_path, htail_left, htail_outside,
      htail_boundary, htail_clean⟩
  rcases hattach hx with ⟨q, hq_path, hq_subset⟩
  exact ⟨{
    x := x
    a := a
    attach := q
    tail := tail
    x_mem_path := hx
    a_mem_leftBoundaryArc := ha
    attach_isPath := hq_path
    attach_support_subset_path := hq_subset
    tail_isPath := htail_path
    tail_support_left := htail_left
    tail_support_outside := htail_outside
    tail_internal_boundary_clean := htail_boundary
    tail_clean_path := htail_clean }⟩

/-- Side-endpoint clean tail to the left boundary arc, with an attachment
segment that stays on the selected side endpoint path. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToLeftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath) (start : V) : Type _ where
  x : V
  a : V
  attach : S.graph.Walk start x
  tail : S.graph.Walk x a
  x_mem_path : x ∈ E.path.support
  a_mem_leftBoundaryArc : a ∈ P.leftBoundaryArc
  attach_isPath : attach.IsPath
  attach_support_subset_path :
    forall w : V, w ∈ attach.support -> w ∈ E.path.support
  tail_isPath : tail.IsPath
  tail_support_left :
    forall w : V, w ∈ tail.support -> w ∈ P.leftSide
  tail_support_outside :
    forall w : V, w ∈ tail.support -> w ∈ P.outside
  tail_internal_boundary_clean :
    Walk.InternalVertices tail ∩ S.boundarySet = ∅
  tail_clean_path :
    forall w : V, w ∈ tail.support -> w ∈ E.path.support -> w = x

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToLeftBoundaryArc.walk
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {E : C.SideEndpointPath} {start : V}
    (A : E.AttachedCleanTailToLeftBoundaryArc start) :
    S.graph.Walk start A.a :=
  A.attach.append A.tail

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToLeftBoundaryArc.walk_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {E : C.SideEndpointPath} {start : V}
    (A : E.AttachedCleanTailToLeftBoundaryArc start) :
    A.walk.IsPath := by
  exact
    append_isPath_of_support_inter_eq_endpoint
      A.attach A.tail A.attach_isPath A.tail_isPath
      (fun w hwAttach hwTail =>
        A.tail_clean_path w hwTail
          (A.attach_support_subset_path w hwAttach))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToLeftBoundaryArc.walk_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {E : C.SideEndpointPath} {start : V}
    (A : E.AttachedCleanTailToLeftBoundaryArc start)
    {w : V}
    (hw : w ∈ A.walk.support) :
    w ∈ E.path.support ∨ w ∈ P.leftSide := by
  exact
    append_support_cases A.attach A.tail
      {v : V | v ∈ E.path.support} P.leftSide
      A.attach_support_subset_path A.tail_support_left
      (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToLeftBoundaryArc.walk] using hw)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.CleanTailToLeftBoundaryArc.exists_attached
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {E : C.SideEndpointPath} {start : V}
    (hclean : E.CleanTailToLeftBoundaryArc)
    (hattach :
      forall {x : V}, x ∈ E.path.support ->
        Exists fun q : S.graph.Walk start x =>
          q.IsPath ∧
            forall w : V, w ∈ q.support -> w ∈ E.path.support) :
    Nonempty (E.AttachedCleanTailToLeftBoundaryArc start) := by
  rcases hclean with
    ⟨x, a, tail, hx, ha, htail_path, htail_left, htail_outside,
      htail_boundary, htail_clean⟩
  rcases hattach hx with ⟨q, hq_path, hq_subset⟩
  exact ⟨{
    x := x
    a := a
    attach := q
    tail := tail
    x_mem_path := hx
    a_mem_leftBoundaryArc := ha
    attach_isPath := hq_path
    attach_support_subset_path := hq_subset
    tail_isPath := htail_path
    tail_support_left := htail_left
    tail_support_outside := htail_outside
    tail_internal_boundary_clean := htail_boundary
    tail_clean_path := htail_clean }⟩

/-- Side-endpoint clean tail to the right boundary arc, with an attachment
segment that stays on the selected side endpoint path. -/
structure MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToRightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath) (start : V) : Type _ where
  x : V
  a : V
  attach : S.graph.Walk start x
  tail : S.graph.Walk x a
  x_mem_path : x ∈ E.path.support
  a_mem_rightBoundaryArc : a ∈ P.rightBoundaryArc
  attach_isPath : attach.IsPath
  attach_support_subset_path :
    forall w : V, w ∈ attach.support -> w ∈ E.path.support
  tail_isPath : tail.IsPath
  tail_support_right :
    forall w : V, w ∈ tail.support -> w ∈ P.rightSide
  tail_support_outside :
    forall w : V, w ∈ tail.support -> w ∈ P.outside
  tail_internal_boundary_clean :
    Walk.InternalVertices tail ∩ S.boundarySet = ∅
  tail_clean_path :
    forall w : V, w ∈ tail.support -> w ∈ E.path.support -> w = x

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToRightBoundaryArc.walk
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {E : C.SideEndpointPath} {start : V}
    (A : E.AttachedCleanTailToRightBoundaryArc start) :
    S.graph.Walk start A.a :=
  A.attach.append A.tail

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToRightBoundaryArc.walk_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {E : C.SideEndpointPath} {start : V}
    (A : E.AttachedCleanTailToRightBoundaryArc start) :
    A.walk.IsPath := by
  exact
    append_isPath_of_support_inter_eq_endpoint
      A.attach A.tail A.attach_isPath A.tail_isPath
      (fun w hwAttach hwTail =>
        A.tail_clean_path w hwTail
          (A.attach_support_subset_path w hwAttach))

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToRightBoundaryArc.walk_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {E : C.SideEndpointPath} {start : V}
    (A : E.AttachedCleanTailToRightBoundaryArc start)
    {w : V}
    (hw : w ∈ A.walk.support) :
    w ∈ E.path.support ∨ w ∈ P.rightSide := by
  exact
    append_support_cases A.attach A.tail
      {v : V | v ∈ E.path.support} P.rightSide
      A.attach_support_subset_path A.tail_support_right
      (by simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.AttachedCleanTailToRightBoundaryArc.walk] using hw)

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.CleanTailToRightBoundaryArc.exists_attached
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    {E : C.SideEndpointPath} {start : V}
    (hclean : E.CleanTailToRightBoundaryArc)
    (hattach :
      forall {x : V}, x ∈ E.path.support ->
        Exists fun q : S.graph.Walk start x =>
          q.IsPath ∧
            forall w : V, w ∈ q.support -> w ∈ E.path.support) :
    Nonempty (E.AttachedCleanTailToRightBoundaryArc start) := by
  rcases hclean with
    ⟨x, a, tail, hx, ha, htail_path, htail_right, htail_outside,
      htail_boundary, htail_clean⟩
  rcases hattach hx with ⟨q, hq_path, hq_subset⟩
  exact ⟨{
    x := x
    a := a
    attach := q
    tail := tail
    x_mem_path := hx
    a_mem_rightBoundaryArc := ha
    attach_isPath := hq_path
    attach_support_subset_path := hq_subset
    tail_isPath := htail_path
    tail_support_right := htail_right
    tail_support_outside := htail_outside
    tail_internal_boundary_clean := htail_boundary
    tail_clean_path := htail_clean }⟩

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.cleanTailToRightBoundaryArc_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (R : C.RightEndpointPath) :
    R.CleanTailToRightBoundaryArc ∨ R.target ∈ P.pathSet := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.RightEndpointPath.CleanTailToRightBoundaryArc]
    using R.clean_tail_to_rightBoundaryArc_or_pathSet

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.cleanTailToLeftBoundaryArc_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (L : C.LeftEndpointPath) :
    L.CleanTailToLeftBoundaryArc ∨ L.target ∈ P.pathSet := by
  simpa [MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.LeftEndpointPath.CleanTailToLeftBoundaryArc]
    using L.clean_tail_to_leftBoundaryArc_or_pathSet

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.cleanTailToBoundaryArc_or_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths}
    (E : C.SideEndpointPath) :
    (E.CleanTailToLeftBoundaryArc ∨ E.CleanTailToRightBoundaryArc) ∨
      E.target ∈ P.pathSet := by
  simpa [
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.CleanTailToLeftBoundaryArc,
      MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.SideEndpointPath.CleanTailToRightBoundaryArc]
    using E.clean_tail_to_boundaryArc_or_pathSet

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.rightFstEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.RightEndpointPath where
  target := D.right_or_path.e.out.1
  path := C.right_paths.fst_path
  isPath := C.right_paths.fst_isPath
  support_subset := C.right_paths.fst_support_subset
  target_mem := C.right_fst_mem_right_or_path

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.rightSndEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.RightEndpointPath where
  target := D.right_or_path.e.out.2
  path := C.right_paths.snd_path
  isPath := C.right_paths.snd_isPath
  support_subset := C.right_paths.snd_support_subset
  target_mem := C.right_snd_mem_right_or_path

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.leftFstEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.LeftEndpointPath where
  target := D.left_or_path.e.out.1
  path := C.left_paths.fst_path
  isPath := C.left_paths.fst_isPath
  support_subset := C.left_paths.fst_support_subset
  target_mem := C.left_fst_mem_left_or_path

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.leftSndEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.LeftEndpointPath where
  target := D.left_or_path.e.out.2
  path := C.left_paths.snd_path
  isPath := C.left_paths.snd_isPath
  support_subset := C.left_paths.snd_support_subset
  target_mem := C.left_snd_mem_left_or_path

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideFstEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.SideEndpointPath where
  target := D.left_or_right.e.out.1
  path := C.side_paths.fst_path
  isPath := C.side_paths.fst_isPath
  support_subset := C.side_paths.fst_support_subset
  target_mem := C.side_fst_mem_side_or_path

noncomputable def MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.sideSndEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    C.SideEndpointPath where
  target := D.left_or_right.e.out.2
  path := C.side_paths.snd_path
  isPath := C.side_paths.snd_isPath
  support_subset := C.side_paths.snd_support_subset
  target_mem := C.side_snd_mem_side_or_path


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
