import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.Sides.Definitions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

@[simp]
theorem leftCutBoundary_vertexSet [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftCutBoundary.vertexSet = P.leftCutBoundarySet := by
  simp [leftCutBoundary]

@[simp]
theorem rightCutBoundary_vertexSet [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightCutBoundary.vertexSet = P.rightCutBoundarySet := by
  simp [rightCutBoundary]

noncomputable def leftBoundaryArcBool [instV : DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) (v : V) : Bool :=
  @decide
    (@CyclicBoundary.ClockwiseOpenBetween V instV
      S.boundary P.s P.t v)
    (Classical.propDecidable _)

noncomputable def rightBoundaryArcBool [instV : DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) (v : V) : Bool :=
  @decide
    (@CyclicBoundary.ClockwiseOpenBetween V instV
      S.boundary P.t P.s v)
    (Classical.propDecidable _)

noncomputable def leftBoundaryArcList [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : List V :=
  (S.boundary.vertices.rotate (S.boundary.indexOf P.s + 1)).filter
    (P.leftBoundaryArcBool)

noncomputable def rightBoundaryArcList [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : List V :=
  (S.boundary.vertices.rotate (S.boundary.indexOf P.t + 1)).filter
    (P.rightBoundaryArcBool)

@[simp]
theorem reverse_leftBoundaryArcList [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.leftBoundaryArcList = P.rightBoundaryArcList := by
  rfl

@[simp]
theorem reverse_rightBoundaryArcList [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.rightBoundaryArcList = P.leftBoundaryArcList := by
  rfl

@[simp]
theorem mem_leftBoundaryArcList [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V} :
    v ∈ P.leftBoundaryArcList ↔ v ∈ P.leftBoundaryArc := by
  constructor
  · intro hv
    have hfilter := (List.mem_filter.mp (by
      simpa [leftBoundaryArcList] using hv))
    have hopen : S.boundary.ClockwiseOpenBetween P.s P.t v := by
      simpa [leftBoundaryArcBool] using hfilter.2
    simpa [leftBoundaryArc, CyclicBoundary.clockwiseArcSet] using hopen
  · intro hv
    have hopen : S.boundary.ClockwiseOpenBetween P.s P.t v := by
      simpa [leftBoundaryArc, CyclicBoundary.clockwiseArcSet] using hv
    have hmem : v ∈ S.boundary.vertices := by
      simpa [CyclicBoundary.vertexSet] using hopen.1.1
    have hmem_rot :
        v ∈ S.boundary.vertices.rotate (S.boundary.indexOf P.s + 1) := by
      exact (List.mem_rotate).mpr hmem
    have hb : P.leftBoundaryArcBool v = true := by
      simpa [leftBoundaryArcBool] using hopen
    exact List.mem_filter.mpr ⟨hmem_rot, hb⟩

@[simp]
theorem mem_rightBoundaryArcList [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V} :
    v ∈ P.rightBoundaryArcList ↔ v ∈ P.rightBoundaryArc := by
  constructor
  · intro hv
    have hfilter := (List.mem_filter.mp (by
      simpa [rightBoundaryArcList] using hv))
    have hopen : S.boundary.ClockwiseOpenBetween P.t P.s v := by
      simpa [rightBoundaryArcBool] using hfilter.2
    simpa [rightBoundaryArc, CyclicBoundary.clockwiseArcSet] using hopen
  · intro hv
    have hopen : S.boundary.ClockwiseOpenBetween P.t P.s v := by
      simpa [rightBoundaryArc, CyclicBoundary.clockwiseArcSet] using hv
    have hmem : v ∈ S.boundary.vertices := by
      simpa [CyclicBoundary.vertexSet] using hopen.1.1
    have hmem_rot :
        v ∈ S.boundary.vertices.rotate (S.boundary.indexOf P.t + 1) := by
      exact (List.mem_rotate).mpr hmem
    have hb : P.rightBoundaryArcBool v = true := by
      simpa [rightBoundaryArcBool] using hopen
    exact List.mem_filter.mpr ⟨hmem_rot, hb⟩

theorem leftBoundaryArcList_eq_nil_of_leftBoundaryArc_eq_empty
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) (hArc : P.leftBoundaryArc = ∅) :
    P.leftBoundaryArcList = [] := by
  cases hlist : P.leftBoundaryArcList with
  | nil => rfl
  | cons z zs =>
      have hzList : z ∈ P.leftBoundaryArcList := by simp [hlist]
      have hzArc : z ∈ P.leftBoundaryArc := P.mem_leftBoundaryArcList.mp hzList
      rw [hArc] at hzArc
      simp at hzArc

theorem rightBoundaryArcList_eq_nil_of_rightBoundaryArc_eq_empty
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) (hArc : P.rightBoundaryArc = ∅) :
    P.rightBoundaryArcList = [] := by
  simpa using
    P.reverse.leftBoundaryArcList_eq_nil_of_leftBoundaryArc_eq_empty
      (by simpa using hArc)

theorem leftBoundaryArcList_nodup [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftBoundaryArcList.Nodup :=
  (List.nodup_rotate.mpr S.boundary.nodup).filter
    (P.leftBoundaryArcBool)

theorem rightBoundaryArcList_nodup [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightBoundaryArcList.Nodup :=
  (List.nodup_rotate.mpr S.boundary.nodup).filter
    (P.rightBoundaryArcBool)

theorem end_not_mem_leftBoundaryArcList [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.t ∉ P.leftBoundaryArcList := by
  intro ht
  have htArc : P.t ∈ P.leftBoundaryArc := by
    simpa using (GMIX24CutPath.mem_leftBoundaryArcList P).mp ht
  have htOpen : S.boundary.ClockwiseOpenBetween P.s P.t P.t := by
    simpa [GMIX24CutPath.leftBoundaryArc, CyclicBoundary.clockwiseArcSet]
      using htArc
  exact htOpen.2.2 rfl

theorem start_not_mem_leftBoundaryArcList [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.s ∉ P.leftBoundaryArcList := by
  intro hs
  have hsArc : P.s ∈ P.leftBoundaryArc := by
    simpa using (GMIX24CutPath.mem_leftBoundaryArcList P).mp hs
  have hsOpen : S.boundary.ClockwiseOpenBetween P.s P.t P.s := by
    simpa [GMIX24CutPath.leftBoundaryArc, CyclicBoundary.clockwiseArcSet]
      using hsArc
  exact hsOpen.2.1 rfl

theorem start_not_mem_rightBoundaryArcList [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.s ∉ P.rightBoundaryArcList := by
  intro hs
  have hsArc : P.s ∈ P.rightBoundaryArc := by
    simpa using (GMIX24CutPath.mem_rightBoundaryArcList P).mp hs
  have hsOpen : S.boundary.ClockwiseOpenBetween P.t P.s P.s := by
    simpa [GMIX24CutPath.rightBoundaryArc, CyclicBoundary.clockwiseArcSet]
      using hsArc
  exact hsOpen.2.2 rfl

theorem end_not_mem_rightBoundaryArcList [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.t ∉ P.rightBoundaryArcList := by
  intro ht
  have htArc : P.t ∈ P.rightBoundaryArc := by
    simpa using (GMIX24CutPath.mem_rightBoundaryArcList P).mp ht
  have htOpen : S.boundary.ClockwiseOpenBetween P.t P.s P.t := by
    simpa [GMIX24CutPath.rightBoundaryArc, CyclicBoundary.clockwiseArcSet]
      using htArc
  exact htOpen.2.1 rfl

theorem leftBoundaryArcList_append_end_nodup [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    (P.leftBoundaryArcList ++ [P.t]).Nodup := by
  exact P.leftBoundaryArcList_nodup.append (by simp)
    (by
      intro v hvArc hvEnd
      simp at hvEnd
      subst v
      exact P.end_not_mem_leftBoundaryArcList hvArc)

theorem leftBoundaryArcList_append_start_nodup [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    (P.leftBoundaryArcList ++ [P.s]).Nodup := by
  exact P.leftBoundaryArcList_nodup.append (by simp)
    (by
      intro v hvArc hvStart
      simp at hvStart
      subst v
      exact P.start_not_mem_leftBoundaryArcList hvArc)

theorem rightBoundaryArcList_append_start_nodup [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    (P.rightBoundaryArcList ++ [P.s]).Nodup := by
  exact P.rightBoundaryArcList_nodup.append (by simp)
    (by
      intro v hvArc hvStart
      simp at hvStart
      subst v
      exact P.start_not_mem_rightBoundaryArcList hvArc)

theorem rightBoundaryArcList_append_end_nodup [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    (P.rightBoundaryArcList ++ [P.t]).Nodup := by
  exact P.rightBoundaryArcList_nodup.append (by simp)
    (by
      intro v hvArc hvEnd
      simp at hvEnd
      subst v
      exact P.end_not_mem_rightBoundaryArcList hvArc)

theorem leftBoundaryArcList_eq_rotate_take_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    let Ωrot : CyclicBoundary V :=
      { vertices := S.boundary.vertices.rotate (S.boundary.indexOf P.s + 1),
        nodup := List.nodup_rotate.mpr S.boundary.nodup }
    P.leftBoundaryArcList = Ωrot.vertices.take (Ωrot.indexOf P.t) := by
  classical
  intro Ωrot
  have hs_mem : P.s ∈ S.boundary.vertexSet := by
    simpa [GeneralSociety.boundarySet] using P.s_mem_boundary
  have ht_mem : P.t ∈ S.boundary.vertexSet := by
    simpa [GeneralSociety.boundarySet] using P.t_mem_boundary
  have htake :
      Ωrot.vertices.take (Ωrot.indexOf P.t) =
        Ωrot.vertices.filter (Ωrot.vertices.take (Ωrot.indexOf P.t)).elem :=
    List.Nodup.take_eq_filter_mem Ωrot.nodup
  rw [htake]
  apply List.filter_congr
  intro v hv
  have hv_orig : v ∈ S.boundary.vertexSet := by
    simpa [Ωrot, CyclicBoundary.vertexSet] using
      (List.mem_rotate.mp hv)
  have hopen_iff :
      S.boundary.ClockwiseOpenBetween P.s P.t v ↔
        Ωrot.indexOf v < Ωrot.indexOf P.t := by
    simpa [Ωrot] using
      S.boundary.clockwiseOpenBetween_rotate_after_start_iff_index_lt
        hs_mem ht_mem P.s_ne_t hv_orig
  have hbool_iff :
      P.leftBoundaryArcBool v = true ↔
        Ωrot.indexOf v < Ωrot.indexOf P.t := by
    simpa [GMIX24CutPath.leftBoundaryArcBool] using hopen_iff
  have htake_iff :
      (Ωrot.vertices.take (Ωrot.indexOf P.t)).elem v = true ↔
        Ωrot.indexOf v < Ωrot.indexOf P.t := by
    constructor
    · intro h
      have hmem_take : v ∈ Ωrot.vertices.take (Ωrot.indexOf P.t) := by
        simpa [List.elem_iff] using h
      exact (List.mem_take_iff_idxOf_lt hv).mp hmem_take
    · intro hlt
      have hmem_take : v ∈ Ωrot.vertices.take (Ωrot.indexOf P.t) :=
        (List.mem_take_iff_idxOf_lt hv).mpr hlt
      simpa [List.elem_iff] using hmem_take
  exact Bool.eq_iff_iff.mpr (hbool_iff.trans htake_iff.symm)

theorem rightBoundaryArcList_eq_rotate_take_to_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    let Ωrot : CyclicBoundary V :=
      { vertices := S.boundary.vertices.rotate (S.boundary.indexOf P.t + 1),
        nodup := List.nodup_rotate.mpr S.boundary.nodup }
    P.rightBoundaryArcList = Ωrot.vertices.take (Ωrot.indexOf P.s) := by
  classical
  intro Ωrot
  have ht_mem : P.t ∈ S.boundary.vertexSet := by
    simpa [GeneralSociety.boundarySet] using P.t_mem_boundary
  have hs_mem : P.s ∈ S.boundary.vertexSet := by
    simpa [GeneralSociety.boundarySet] using P.s_mem_boundary
  have htake :
      Ωrot.vertices.take (Ωrot.indexOf P.s) =
        Ωrot.vertices.filter (Ωrot.vertices.take (Ωrot.indexOf P.s)).elem :=
    List.Nodup.take_eq_filter_mem Ωrot.nodup
  rw [htake]
  apply List.filter_congr
  intro v hv
  have hv_orig : v ∈ S.boundary.vertexSet := by
    simpa [Ωrot, CyclicBoundary.vertexSet] using
      (List.mem_rotate.mp hv)
  have hopen_iff :
      S.boundary.ClockwiseOpenBetween P.t P.s v ↔
        Ωrot.indexOf v < Ωrot.indexOf P.s := by
    simpa [Ωrot] using
      S.boundary.clockwiseOpenBetween_rotate_after_start_iff_index_lt
        ht_mem hs_mem (Ne.symm P.s_ne_t) hv_orig
  have hbool_iff :
      P.rightBoundaryArcBool v = true ↔
        Ωrot.indexOf v < Ωrot.indexOf P.s := by
    simpa [GMIX24CutPath.rightBoundaryArcBool] using hopen_iff
  have htake_iff :
      (Ωrot.vertices.take (Ωrot.indexOf P.s)).elem v = true ↔
        Ωrot.indexOf v < Ωrot.indexOf P.s := by
    constructor
    · intro h
      have hmem_take : v ∈ Ωrot.vertices.take (Ωrot.indexOf P.s) := by
        simpa [List.elem_iff] using h
      exact (List.mem_take_iff_idxOf_lt hv).mp hmem_take
    · intro hlt
      have hmem_take : v ∈ Ωrot.vertices.take (Ωrot.indexOf P.s) :=
        (List.mem_take_iff_idxOf_lt hv).mpr hlt
      simpa [List.elem_iff] using hmem_take
  exact Bool.eq_iff_iff.mpr (hbool_iff.trans htake_iff.symm)

/-- Rebase the ambient cyclic boundary at the start of a cut path.  The exact
ordered vertex list is the start, the open left arc, the end, and the open
right arc. -/
theorem boundary_rotate_start_eq_arcs
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    S.boundary.vertices.rotate (S.boundary.indexOf P.s) =
      P.s :: P.leftBoundaryArcList ++ P.t :: P.rightBoundaryArcList := by
  classical
  have hs : P.s ∈ S.boundary.vertices := by
    simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
      P.s_mem_boundary
  have ht : P.t ∈ S.boundary.vertices := by
    simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
      P.t_mem_boundary
  have hleft :
      P.leftBoundaryArcList =
        (S.boundary.vertices.rotate (S.boundary.indexOf P.s + 1)).take
          ((S.boundary.vertices.rotate
            (S.boundary.indexOf P.s + 1)).idxOf P.t) := by
    simpa [CyclicBoundary.indexOf] using
      P.leftBoundaryArcList_eq_rotate_take_to_end
  have hright :
      P.rightBoundaryArcList =
        (S.boundary.vertices.rotate (S.boundary.indexOf P.t + 1)).take
          ((S.boundary.vertices.rotate
            (S.boundary.indexOf P.t + 1)).idxOf P.s) := by
    simpa [CyclicBoundary.indexOf] using
      P.rightBoundaryArcList_eq_rotate_take_to_start
  have h :=
    Schematic.Math.GraphTheory.list_rotate_idxOf_two_arc_decomposition
      S.boundary.vertices P.s P.t S.boundary.nodup hs ht P.s_ne_t
  simp only [CyclicBoundary.indexOf] at hleft hright ⊢
  rw [← hleft, ← hright] at h
  exact h


/-- Ordered boundary vertices for the left split society.

The list is the original clockwise open arc `Ω(s,t)`, followed by the cut path
traversed from `t` back to `s`, matching the construction of `Ω₁` in GM IX
`(2.4)` up to cyclic rotation. -/
noncomputable def leftOrderedCutBoundaryVertices [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : List V :=
  P.leftBoundaryArcList ++ P.path.support.reverse

/-- Ordered boundary vertices for the right split society.

This is the clockwise open arc `Ω(t,s)`, followed by the cut path from `s` to
`t`, matching the construction of `Ω₂` in GM IX `(2.4)` up to cyclic rotation. -/
noncomputable def rightOrderedCutBoundaryVertices [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : List V :=
  P.rightBoundaryArcList ++ P.path.support

theorem leftBoundaryArcList_disjoint_path_reverse
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftBoundaryArcList.Disjoint P.path.support.reverse := by
  intro v hvArc hvPath
  have hvArcSet : v ∈ P.leftBoundaryArc := by
    simpa using hvArc
  have hvSupport : v ∈ P.path.support := by
    simpa using (List.mem_reverse.mp hvPath)
  exact (P.leftBoundaryArc_subset_outside hvArcSet).2 hvSupport

theorem rightBoundaryArcList_disjoint_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightBoundaryArcList.Disjoint P.path.support := by
  intro v hvArc hvPath
  have hvArcSet : v ∈ P.rightBoundaryArc := by
    simpa using hvArc
  exact (P.rightBoundaryArc_subset_outside hvArcSet).2 hvPath

theorem leftOrderedCutBoundaryVertices_nodup
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftOrderedCutBoundaryVertices.Nodup := by
  dsimp [leftOrderedCutBoundaryVertices]
  exact P.leftBoundaryArcList_nodup.append
    (List.nodup_reverse.mpr P.path_isPath.support_nodup)
    P.leftBoundaryArcList_disjoint_path_reverse

theorem rightOrderedCutBoundaryVertices_nodup
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightOrderedCutBoundaryVertices.Nodup := by
  dsimp [rightOrderedCutBoundaryVertices]
  exact P.rightBoundaryArcList_nodup.append
    P.path_isPath.support_nodup
    P.rightBoundaryArcList_disjoint_path

noncomputable def leftOrderedCutBoundary [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : CyclicBoundary V where
  vertices := P.leftOrderedCutBoundaryVertices
  nodup := P.leftOrderedCutBoundaryVertices_nodup

noncomputable def rightOrderedCutBoundary [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : CyclicBoundary V where
  vertices := P.rightOrderedCutBoundaryVertices
  nodup := P.rightOrderedCutBoundaryVertices_nodup

@[simp]
theorem reverse_leftOrderedCutBoundaryVertices
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.leftOrderedCutBoundaryVertices =
      P.rightOrderedCutBoundaryVertices := by
  simp only [leftOrderedCutBoundaryVertices, rightOrderedCutBoundaryVertices,
    reverse_leftBoundaryArcList, reverse_path]
  congr 1
  exact (congrArg List.reverse P.path.support_reverse).trans
    (List.reverse_reverse P.path.support)

@[simp]
theorem reverse_rightOrderedCutBoundaryVertices
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.rightOrderedCutBoundaryVertices =
      P.leftOrderedCutBoundaryVertices := by
  simp only [leftOrderedCutBoundaryVertices, rightOrderedCutBoundaryVertices,
    reverse_rightBoundaryArcList, reverse_path]
  congr 1
  exact P.path.support_reverse

@[simp]
theorem reverse_leftOrderedCutBoundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.leftOrderedCutBoundary = P.rightOrderedCutBoundary := by
  ext
  simp [leftOrderedCutBoundary, rightOrderedCutBoundary]

@[simp]
theorem reverse_rightOrderedCutBoundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.rightOrderedCutBoundary = P.leftOrderedCutBoundary := by
  ext
  simp [leftOrderedCutBoundary, rightOrderedCutBoundary]

@[simp]
theorem leftOrderedCutBoundary_vertexSet [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.leftOrderedCutBoundary.vertexSet = P.leftCutBoundarySet := by
  ext v
  simp [leftOrderedCutBoundary, leftOrderedCutBoundaryVertices,
    CyclicBoundary.vertexSet, leftCutBoundarySet, pathSet]

@[simp]
theorem rightOrderedCutBoundary_vertexSet [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.rightOrderedCutBoundary.vertexSet = P.rightCutBoundarySet := by
  simpa using P.reverse.leftOrderedCutBoundary_vertexSet

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
