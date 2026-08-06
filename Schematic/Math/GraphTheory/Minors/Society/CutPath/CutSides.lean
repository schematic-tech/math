import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath
/-- A canonical cut boundary always contains the two distinct ends of the
cut path. -/
theorem leftCutBoundarySet_ncard_ge_two [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    2 <= P.leftCutBoundarySet.ncard := by
  have hpair : ({P.s, P.t} : Set V) ⊆ P.leftCutBoundarySet := by
    intro v hv
    rcases hv with rfl | rfl
    · exact Or.inr P.s_mem_pathSet
    · exact Or.inr P.t_mem_pathSet
  have hcard : ({P.s, P.t} : Set V).ncard = 2 := by
    exact Set.ncard_pair P.s_ne_t
  rw [← hcard]
  exact Set.ncard_le_ncard hpair P.leftCutBoundarySet_finite

/-- Right-side version of `leftCutBoundarySet_ncard_ge_two`. -/
theorem rightCutBoundarySet_ncard_ge_two [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    2 <= P.rightCutBoundarySet.ncard := by
  simpa using P.reverse.leftCutBoundarySet_ncard_ge_two

/-- A genuine vertex on the open left boundary arc, together with the two
distinct cut endpoints, gives three distinct vertices of the left cut
boundary. -/
theorem leftCutBoundarySet_ncard_ge_three_of_leftBoundaryArc_nonempty
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hArc : P.leftBoundaryArc.Nonempty) :
    3 <= P.leftCutBoundarySet.ncard := by
  rcases hArc with ⟨z, hz⟩
  have hzs : z ≠ P.s := P.leftBoundaryArc_ne_s hz
  have hzt : z ≠ P.t := P.leftBoundaryArc_ne_t hz
  have hsubset : ({P.s, P.t, z} : Set V) ⊆ P.leftCutBoundarySet := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inr P.s_mem_pathSet
    · exact Or.inr P.t_mem_pathSet
    · exact Or.inl hz
  have hcard : ({P.s, P.t, z} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
      simp [P.s_ne_t, hzs.symm])]
    rw [Set.ncard_insert_of_notMem (by
      simp [hzt.symm])]
    simp
  rw [← hcard]
  exact Set.ncard_le_ncard hsubset P.leftCutBoundarySet_finite

/-- Right-side form of
`leftCutBoundarySet_ncard_ge_three_of_leftBoundaryArc_nonempty`. -/
theorem rightCutBoundarySet_ncard_ge_three_of_rightBoundaryArc_nonempty
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hArc : P.rightBoundaryArc.Nonempty) :
    3 <= P.rightCutBoundarySet.ncard := by
  simpa using
    P.reverse.leftCutBoundarySet_ncard_ge_three_of_leftBoundaryArc_nonempty
      (by simpa using hArc)

/-- If the left cut boundary has only its forced two vertices, its open
original-boundary arc is empty.  This is the exceptional side in disk
gluing: there is no genuine piece on that side of the cut path. -/
theorem leftBoundaryArc_eq_empty_of_leftCutBoundarySet_ncard_le_two
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hcard : P.leftCutBoundarySet.ncard <= 2) :
    P.leftBoundaryArc = ∅ := by
  have hpath_subset : P.pathSet ⊆ P.leftCutBoundarySet := by
    intro v hv
    exact Or.inr hv
  have hpair : ({P.s, P.t} : Set V) ⊆ P.pathSet := by
    intro v hv
    rcases hv with rfl | rfl
    · exact P.s_mem_pathSet
    · exact P.t_mem_pathSet
  have hpairCard : ({P.s, P.t} : Set V).ncard = 2 := by
    exact Set.ncard_pair P.s_ne_t
  have hpath_ge : 2 <= P.pathSet.ncard := by
    rw [← hpairCard]
    exact Set.ncard_le_ncard hpair P.pathSet_finite
  have hcut_le_path :
      P.leftCutBoundarySet.ncard <= P.pathSet.ncard := by
    have hpath_le_cut :=
      Set.ncard_le_ncard hpath_subset P.leftCutBoundarySet_finite
    omega
  have hpath_eq_cut : P.pathSet = P.leftCutBoundarySet :=
    Set.eq_of_subset_of_ncard_le hpath_subset hcut_le_path
      P.leftCutBoundarySet_finite
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hvArc
  have hvCut : v ∈ P.leftCutBoundarySet := Or.inl hvArc
  have hvPath : v ∈ P.pathSet := by
    rw [hpath_eq_cut]
    exact hvCut
  exact (P.leftBoundaryArc_subset_outside hvArc).2
    (by simpa [GMIX24CutPath.pathSet] using hvPath)

/-- Right-side version of the empty-open-arc small case. -/
theorem rightBoundaryArc_eq_empty_of_rightCutBoundarySet_ncard_le_two
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hcard : P.rightCutBoundarySet.ncard <= 2) :
    P.rightBoundaryArc = ∅ := by
  simpa using
    P.reverse.leftBoundaryArc_eq_empty_of_leftCutBoundarySet_ncard_le_two
      (by simpa using hcard)

private theorem leftGraph_eq_bot_of_leftBoundaryArc_eq_empty_aux
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hArc : P.leftBoundaryArc = ∅) :
    P.leftGraph = ⊥ := by
  have hSide : P.leftSide = ∅ := by
    ext v
    simp [GMIX24CutPath.leftSide, ComponentUnionMeeting, hArc]
  ext u v
  constructor
  · intro huv
    have huPath : u ∈ P.pathSet := by
      rcases P.leftGraph_support_subset huv.left_mem_support with huSide | huPath
      · simp [hSide] at huSide
      · exact huPath
    have hvPath : v ∈ P.pathSet := by
      rcases P.leftGraph_support_subset huv.right_mem_support with hvSide | hvPath
      · simp [hSide] at hvSide
      · exact hvPath
    exact False.elim
      (P.leftGraph_not_adj_between_path_vertices huPath hvPath huv)
  · simp

/-- The canonical left graph is empty when the corresponding cut boundary
has only the two cut-path ends.  Its support can then lie only on the cut
path, while all cut-path edges were deliberately deleted from the side
graph. -/
theorem leftGraph_eq_bot_of_leftCutBoundarySet_ncard_le_two
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hcard : P.leftCutBoundarySet.ncard <= 2) :
    P.leftGraph = ⊥ := by
  have hArc : P.leftBoundaryArc = ∅ :=
    P.leftBoundaryArc_eq_empty_of_leftCutBoundarySet_ncard_le_two hcard
  exact leftGraph_eq_bot_of_leftBoundaryArc_eq_empty_aux P hArc

/-- Right-side version of the empty canonical side graph. -/
theorem rightGraph_eq_bot_of_rightCutBoundarySet_ncard_le_two
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hcard : P.rightCutBoundarySet.ncard <= 2) :
    P.rightGraph = ⊥ := by
  simpa using
    P.reverse.leftGraph_eq_bot_of_leftCutBoundarySet_ncard_le_two
      (by simpa using hcard)

/-- If the open left boundary arc is empty, there is no left component of the
cut.  Every remaining endpoint of a left-side edge would lie on the induced
cut path, but all edges of that path were removed in `leftGraph`; hence the
entire side graph is empty. -/
theorem leftGraph_eq_bot_of_leftBoundaryArc_eq_empty
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hArc : P.leftBoundaryArc = ∅) :
    P.leftGraph = ⊥ :=
  leftGraph_eq_bot_of_leftBoundaryArc_eq_empty_aux P hArc

/-- Right-side counterpart of
`leftGraph_eq_bot_of_leftBoundaryArc_eq_empty`. -/
theorem rightGraph_eq_bot_of_rightBoundaryArc_eq_empty
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hArc : P.rightBoundaryArc = ∅) :
    P.rightGraph = ⊥ := by
  simpa using
    P.reverse.leftGraph_eq_bot_of_leftBoundaryArc_eq_empty (by simpa using hArc)

private theorem walk_from_set_meets_side
    [DecidableEq V]
    {G : SimpleGraph V} {pathSet side : Set V}
    {u v : V} (q : G.Walk u v)
    (hu : u ∈ pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ side ∪ pathSet)
    (hno_adj : forall {x y : V}, x ∈ pathSet -> y ∈ pathSet -> ¬ G.Adj x y) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ side := by
  classical
  have hnot_nil : ¬ q.Nil := by
    intro hnil
    exact hq_nontrivial (SimpleGraph.Walk.nil_iff_length_eq.mp hnil)
  let w : V := q.snd
  have he : s(u, w) ∈ q.edges := by
    simpa [w] using q.mk_start_snd_mem_edges hnot_nil
  have huw : G.Adj u w := q.adj_of_mem_edges he
  have hw_support : w ∈ q.support := q.snd_mem_support_of_mem_edges he
  rcases hq_support hw_support with hwSide | hwPath
  · exact ⟨w, hw_support, hwSide⟩
  · exact False.elim (hno_adj hu hwPath huw)

private theorem walk_touching_set_meets_side
    [DecidableEq V]
    {G : SimpleGraph V} {pathSet side : Set V}
    {u v x : V} (q : G.Walk u v)
    (hxq : x ∈ q.support)
    (hxPath : x ∈ pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ side ∪ pathSet)
    (hno_adj : forall {x y : V}, x ∈ pathSet -> y ∈ pathSet -> ¬ G.Adj x y) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ side := by
  classical
  have hnot_nil : ¬ q.Nil := by
    intro hnil
    exact hq_nontrivial (SimpleGraph.Walk.nil_iff_length_eq.mp hnil)
  obtain ⟨y, hyq, hxy⟩ :=
    SimpleGraph.adj_of_mem_walk_support q hnot_nil hxq
  rcases hq_support hyq with hySide | hyPath
  · exact ⟨y, hyq, hySide⟩
  · exact False.elim (hno_adj hxPath hyPath hxy)

private theorem walk_to_set_meets_side
    [DecidableEq V]
    {G : SimpleGraph V} {pathSet side : Set V}
    {u v : V} (q : G.Walk u v)
    (hv : v ∈ pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ side ∪ pathSet)
    (hno_adj : forall {x y : V}, x ∈ pathSet -> y ∈ pathSet -> ¬ G.Adj x y) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ side := by
  obtain ⟨z, hzrev, hzSide⟩ :=
    walk_from_set_meets_side q.reverse hv
      (by simpa using hq_nontrivial)
      (by
        intro z hz
        exact hq_support (by
          rw [SimpleGraph.Walk.support_reverse] at hz
          exact List.mem_reverse.mp hz))
      hno_adj
  refine ⟨z, ?_, hzSide⟩
  rw [SimpleGraph.Walk.support_reverse] at hzrev
  exact List.mem_reverse.mp hzrev

theorem leftGraph_walk_from_path_meets_leftSide
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V} (q : P.leftGraph.Walk u v)
    (hu : u ∈ P.pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ P.leftSide ∪ P.pathSet) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ P.leftSide := by
  exact walk_from_set_meets_side q hu hq_nontrivial hq_support
    (fun hx hy => P.leftGraph_not_adj_between_path_vertices hx hy)

theorem leftGraph_walk_touching_path_meets_leftSide
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v x : V} (q : P.leftGraph.Walk u v)
    (hxq : x ∈ q.support)
    (hxPath : x ∈ P.pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ P.leftSide ∪ P.pathSet) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ P.leftSide := by
  exact walk_touching_set_meets_side q hxq hxPath hq_nontrivial hq_support
    (fun hx hy => P.leftGraph_not_adj_between_path_vertices hx hy)

theorem leftGraph_walk_to_path_meets_leftSide
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V} (q : P.leftGraph.Walk u v)
    (hv : v ∈ P.pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ P.leftSide ∪ P.pathSet) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ P.leftSide := by
  exact walk_to_set_meets_side q hv hq_nontrivial hq_support
    (fun hx hy => P.leftGraph_not_adj_between_path_vertices hx hy)

theorem rightGraph_walk_from_path_meets_rightSide
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V} (q : P.rightGraph.Walk u v)
    (hu : u ∈ P.pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ P.rightSide ∪ P.pathSet) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ P.rightSide := by
  exact walk_from_set_meets_side q hu hq_nontrivial hq_support
    (fun hx hy => P.rightGraph_not_adj_between_path_vertices hx hy)

theorem rightGraph_walk_touching_path_meets_rightSide
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v x : V} (q : P.rightGraph.Walk u v)
    (hxq : x ∈ q.support)
    (hxPath : x ∈ P.pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ P.rightSide ∪ P.pathSet) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ P.rightSide := by
  exact walk_touching_set_meets_side q hxq hxPath hq_nontrivial hq_support
    (fun hx hy => P.rightGraph_not_adj_between_path_vertices hx hy)

theorem rightGraph_walk_to_path_meets_rightSide
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V} (q : P.rightGraph.Walk u v)
    (hv : v ∈ P.pathSet)
    (hq_nontrivial : q.length ≠ 0)
    (hq_support : {z : V | z ∈ q.support} ⊆ P.rightSide ∪ P.pathSet) :
    Exists fun z : V => z ∈ q.support ∧ z ∈ P.rightSide := by
  exact walk_to_set_meets_side q hv hq_nontrivial hq_support
    (fun hx hy => P.rightGraph_not_adj_between_path_vertices hx hy)

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
