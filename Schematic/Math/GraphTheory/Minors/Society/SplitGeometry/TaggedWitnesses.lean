import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.MixedEdgeLocalization

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- One tagged mixed-edge witness, with the source edge, host edge and
support data unpacked into named fields.

The three fields of `MixedEdgeTaggedSupportWitnesses` are existential
packages.  This record is a small bookkeeping layer used by the remaining
mixed-Kuratowski case analysis: it lets subsequent lemmas compare the source
edges of the three witnesses using the strict-subdivision disjointness
axioms without repeatedly destructing nested existentials. -/
structure TaggedSupportWitnessData
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (_hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Type _ where
  x : W
  y : W
  hxy : K.Adj x y
  e : Sym2 V
  edge_mem : e ∈ ((Classical.choice hK).edgePath hxy).edges
  out_fst_support :
    e.out.1 ∈ ((Classical.choice hK).edgePath hxy).support
  out_snd_support :
    e.out.2 ∈ ((Classical.choice hK).edgePath hxy).support

namespace TaggedSupportWitnessData

def supportSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK) :
    Set V :=
  {z : V | z ∈ ((Classical.choice hK).edgePath D.hxy).support}

def SourceEdgesShareEndpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (A B : GMIX24Split.TaggedSupportWitnessData P hno_cross hK) : Prop :=
  A.x = B.x ∨ A.x = B.y ∨ A.y = B.x ∨ A.y = B.y

theorem support_disjoint_or_sourceEdgesShareEndpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (A B : GMIX24Split.TaggedSupportWitnessData P hno_cross hK) :
    Disjoint A.supportSet B.supportSet ∨
      A.SourceEdgesShareEndpoint B := by
  classical
  simpa [supportSet, SourceEdgesShareEndpoint] using
    (Classical.choice hK).edgePath_support_disjoint_or_common_endpoint
      A.hxy B.hxy

/-- Specialized common-end support intersection for tagged strict-subdivision
edge witnesses.

If two tagged source edges have a unique common source endpoint `c`, then any
host vertex in the intersection of their support sets is exactly the branch
vertex of `c`.  This is the support-level fact needed in the mixed
Kuratowski common-end branch: the extracted endpoint paths from two different
source edges may only meet at the common branch vertex. -/
theorem support_inter_eq_common_branchVertex
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (A B : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {c : W}
    (hne :
      Not ((A.x = B.x ∧ A.y = B.y) ∨
        (A.x = B.y ∧ A.y = B.x)))
    (hunique :
      forall w : W,
        (w = A.x ∨ w = A.y) ->
          (w = B.x ∨ w = B.y) ->
            w = c)
    {z : V}
    (hzA : z ∈ A.supportSet)
    (hzB : z ∈ B.supportSet) :
    z = (Classical.choice hK).branchVertex c := by
  classical
  simpa [supportSet] using
    (Classical.choice hK).edgePath_support_inter_eq_common_branchVertex
      A.hxy B.hxy hne hunique (by simpa [supportSet] using hzA)
      (by simpa [supportSet] using hzB)

theorem branchVertex_mem_supportSet_of_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {v : W}
    (hv : v = D.x ∨ v = D.y) :
    (Classical.choice hK).branchVertex v ∈ D.supportSet := by
  classical
  rcases hv with rfl | rfl
  · exact (Classical.choice hK).edgePath D.hxy |>.start_mem_support
  · exact (Classical.choice hK).edgePath D.hxy |>.end_mem_support

theorem out_fst_mem_supportSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK) :
    D.e.out.1 ∈ D.supportSet := by
  simpa [supportSet] using D.out_fst_support

theorem out_snd_mem_supportSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK) :
    D.e.out.2 ∈ D.supportSet := by
  simpa [supportSet] using D.out_snd_support

theorem supportSet_nonempty
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK) :
    Exists fun z : V => z ∈ D.supportSet :=
  ⟨D.e.out.1, D.out_fst_mem_supportSet⟩

theorem source_endpoint_branch_vertices_mem_supportSet
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK) :
    (Classical.choice hK).branchVertex D.x ∈ D.supportSet ∧
      (Classical.choice hK).branchVertex D.y ∈ D.supportSet := by
  constructor
  · exact D.branchVertex_mem_supportSet_of_endpoint (Or.inl rfl)
  · exact D.branchVertex_mem_supportSet_of_endpoint (Or.inr rfl)

/-- Any two vertices on the support of one tagged strict-subdivision edge are
joined by an oriented path segment whose support stays on that same edge path.

This is the path-extraction step needed by the mixed rural-gluing case: after
the source-endpoint analysis produces a common host support vertex, the
Kuratowski fragments must use actual subpaths from that common vertex to the
localized host-edge endpoints. -/
theorem exists_support_path_between
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {a b : V}
    (ha : a ∈ D.supportSet)
    (hb : b ∈ D.supportSet) :
    Exists fun q : S.graph.Walk a b =>
      q.IsPath ∧ forall z : V, z ∈ q.support -> z ∈ D.supportSet := by
  classical
  let M := Classical.choice hK
  let p : S.graph.Walk (M.branchVertex D.x) (M.branchVertex D.y) :=
    M.edgePath D.hxy
  have hp : p.IsPath := by
    simpa [p, M] using M.edgePath_isPath D.hxy
  have ha_p : a ∈ p.support := by
    simpa [supportSet, p, M] using ha
  have hb_p : b ∈ p.support := by
    simpa [supportSet, p, M] using hb
  by_cases hle : Walk.supportIndex p a <= Walk.supportIndex p b
  · refine ⟨Walk.segmentBetween p ha_p hb_p hle, ?_, ?_⟩
    · exact Walk.segmentBetween_isPath hp ha_p hb_p hle
    · intro z hz
      have hz_p :
          z ∈ ((Classical.choice hK).edgePath D.hxy).support := by
        simpa [p, M] using
          Walk.segmentBetween_support_subset ha_p hb_p hle hz
      simpa [supportSet] using hz_p
  · have hba :
        Walk.supportIndex p b <= Walk.supportIndex p a :=
      Nat.le_of_lt (lt_of_not_ge hle)
    refine ⟨(Walk.segmentBetween p hb_p ha_p hba).reverse, ?_, ?_⟩
    · exact Walk.segmentBetween_reverse_isPath hp hb_p ha_p hba
    · intro z hz
      have hz_p :
          z ∈ ((Classical.choice hK).edgePath D.hxy).support := by
        simpa [p, M] using
          Walk.segmentBetween_reverse_support_subset hb_p ha_p hba hz
      simpa [supportSet] using hz_p

theorem exists_support_path_from_other_endpoint_avoiding_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {common other : W}
    (hcommon : common = D.x ∨ common = D.y)
    (hother : other = D.x ∨ other = D.y)
    (hcommon_ne_other : common ≠ other)
    {target : V}
    (htarget : target ∈ D.supportSet)
    (htarget_ne_common :
      target ≠ (Classical.choice hK).branchVertex common) :
    Exists fun q : S.graph.Walk
        ((Classical.choice hK).branchVertex other) target =>
      q.IsPath ∧
        (forall z : V, z ∈ q.support -> z ∈ D.supportSet) ∧
          (Classical.choice hK).branchVertex common ∉ q.support := by
  classical
  let M := Classical.choice hK
  let p : S.graph.Walk (M.branchVertex D.x) (M.branchVertex D.y) :=
    M.edgePath D.hxy
  have hp : p.IsPath := by
    simpa [p, M] using M.edgePath_isPath D.hxy
  have ht_p : target ∈ p.support := by
    simpa [supportSet, p, M] using htarget
  rcases hcommon with rfl | rfl <;> rcases hother with rfl | rfl
  · exact False.elim (hcommon_ne_other rfl)
  · have hle : Walk.supportIndex p target <=
        Walk.supportIndex p (M.branchVertex D.y) :=
      Walk.IsPath.supportIndex_le_end hp ht_p
    refine
      ⟨(Walk.segmentBetween p ht_p p.end_mem_support hle).reverse,
        ?_, ?_, ?_⟩
    · exact Walk.segmentBetween_reverse_isPath hp ht_p p.end_mem_support hle
    · intro z hz
      have hz_p : z ∈ (M.edgePath D.hxy).support := by
        simpa [p, M] using
          Walk.segmentBetween_reverse_support_subset ht_p
            p.end_mem_support hle hz
      simpa [supportSet, M] using hz_p
    · intro hmem
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hmem
      have htarget_le_start :
          Walk.supportIndex p target <=
            Walk.supportIndex p (M.branchVertex D.x) :=
        Walk.segmentBetween_supportIndex_left_le hp ht_p
          p.end_mem_support hle hmem
      have hstart_lt_target :
          Walk.supportIndex p (M.branchVertex D.x) <
            Walk.supportIndex p target :=
        Walk.supportIndex_lt_of_le_of_mem_of_ne
          p.start_mem_support
          (Walk.supportIndex_start_le (p := p))
          (by
            intro h
            exact htarget_ne_common (by simpa [M] using h.symm))
      exact (lt_irrefl (Walk.supportIndex p (M.branchVertex D.x)))
        (lt_of_lt_of_le hstart_lt_target htarget_le_start)
  · have hle : Walk.supportIndex p (M.branchVertex D.x) <=
        Walk.supportIndex p target :=
      Walk.supportIndex_start_le (p := p)
    refine
      ⟨Walk.segmentBetween p p.start_mem_support ht_p hle, ?_, ?_, ?_⟩
    · exact Walk.segmentBetween_isPath hp p.start_mem_support ht_p hle
    · intro z hz
      have hz_p : z ∈ (M.edgePath D.hxy).support := by
        simpa [p, M] using
          Walk.segmentBetween_support_subset p.start_mem_support ht_p hle hz
      simpa [supportSet, M] using hz_p
    · intro hmem
      have hend_le_target :
          Walk.supportIndex p (M.branchVertex D.y) <=
            Walk.supportIndex p target :=
        Walk.segmentBetween_supportIndex_right_le p.start_mem_support
          ht_p hle hmem
      have htarget_lt_end :
          Walk.supportIndex p target <
            Walk.supportIndex p (M.branchVertex D.y) :=
        Walk.supportIndex_lt_of_le_of_mem_of_ne ht_p
          (Walk.IsPath.supportIndex_le_end hp ht_p)
          (by
            intro h
            exact htarget_ne_common (by simpa [M] using h))
      exact (lt_irrefl (Walk.supportIndex p target))
        (lt_of_lt_of_le htarget_lt_end hend_le_target)
  · exact False.elim (hcommon_ne_other rfl)

theorem exists_support_path_to_out_fst
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {z : V}
    (hz : z ∈ D.supportSet) :
    Exists fun q : S.graph.Walk z D.e.out.1 =>
      q.IsPath ∧ forall w : V, w ∈ q.support -> w ∈ D.supportSet :=
  D.exists_support_path_between hz D.out_fst_mem_supportSet

theorem exists_support_path_to_out_snd
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {z : V}
    (hz : z ∈ D.supportSet) :
    Exists fun q : S.graph.Walk z D.e.out.2 =>
      q.IsPath ∧ forall w : V, w ∈ q.support -> w ∈ D.supportSet :=
  D.exists_support_path_between hz D.out_snd_mem_supportSet

theorem exists_support_path_to_source_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {z : V} {v : W}
    (hz : z ∈ D.supportSet)
    (hv : v = D.x ∨ v = D.y) :
    Exists fun q : S.graph.Walk z ((Classical.choice hK).branchVertex v) =>
      q.IsPath ∧ forall w : V, w ∈ q.support -> w ∈ D.supportSet :=
  D.exists_support_path_between hz
    (D.branchVertex_mem_supportSet_of_endpoint hv)

/-- From a point on a tagged source-edge support, one can route along that
support to the source edge endpoint opposite a specified endpoint. -/
theorem exists_support_path_to_other_source_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {z : V} {c : W}
    (hz : z ∈ D.supportSet)
    (hc : c = D.x ∨ c = D.y) :
    Exists fun d : W =>
      d ≠ c ∧
        (d = D.x ∨ d = D.y) ∧
          Exists fun q : S.graph.Walk z ((Classical.choice hK).branchVertex d) =>
            q.IsPath ∧
              forall w : V, w ∈ q.support -> w ∈ D.supportSet := by
  rcases hc with rfl | rfl
  · exact ⟨D.y, D.hxy.ne.symm, Or.inr rfl,
      D.exists_support_path_to_source_endpoint hz (Or.inr rfl)⟩
  · exact ⟨D.x, D.hxy.ne, Or.inl rfl,
      D.exists_support_path_to_source_endpoint hz (Or.inl rfl)⟩

/-- Named data for the path from a support vertex to the source-edge endpoint
opposite a specified endpoint. -/
structure OtherSourceEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    (z : V) (c : W) : Type _ where
  other : W
  other_ne : other ≠ c
  other_endpoint : other = D.x ∨ other = D.y
  path : S.graph.Walk z ((Classical.choice hK).branchVertex other)
  isPath : path.IsPath
  support_subset :
    forall w : V, w ∈ path.support -> w ∈ D.supportSet

noncomputable def otherSourceEndpointPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {z : V} {c : W}
    (hz : z ∈ D.supportSet)
    (hc : c = D.x ∨ c = D.y) :
    D.OtherSourceEndpointPath z c := by
  classical
  let H := D.exists_support_path_to_other_source_endpoint hz hc
  let d : W := Classical.choose H
  have hd := Classical.choose_spec H
  let Hq := hd.2.2
  let q : S.graph.Walk z ((Classical.choice hK).branchVertex d) :=
    Classical.choose Hq
  have hq := Classical.choose_spec Hq
  exact {
    other := d
    other_ne := hd.1
    other_endpoint := hd.2.1
    path := q
    isPath := hq.1
    support_subset := hq.2
  }

/-- The two endpoint segments from a fixed support vertex to the concrete host
edge endpoints of a tagged witness. -/
structure EndpointPathPair
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    (z : V) : Type _ where
  z_mem : z ∈ D.supportSet
  fst_path : S.graph.Walk z D.e.out.1
  fst_isPath : fst_path.IsPath
  fst_support_subset :
    forall w : V, w ∈ fst_path.support -> w ∈ D.supportSet
  snd_path : S.graph.Walk z D.e.out.2
  snd_isPath : snd_path.IsPath
  snd_support_subset :
    forall w : V, w ∈ snd_path.support -> w ∈ D.supportSet

noncomputable def endpointPathPair
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK)
    {z : V}
    (hz : z ∈ D.supportSet) :
    GMIX24Split.TaggedSupportWitnessData.EndpointPathPair D z := by
  classical
  let q1 := Classical.choose (D.exists_support_path_to_out_fst hz)
  have hq1 := Classical.choose_spec (D.exists_support_path_to_out_fst hz)
  let q2 := Classical.choose (D.exists_support_path_to_out_snd hz)
  have hq2 := Classical.choose_spec (D.exists_support_path_to_out_snd hz)
  exact {
    z_mem := hz
    fst_path := q1
    fst_isPath := hq1.1
    fst_support_subset := hq1.2
    snd_path := q2
    snd_isPath := hq2.1
    snd_support_subset := hq2.2
  }

/-- The concrete host edge selected by a tagged witness has distinct
endpoints. -/
theorem out_fst_ne_out_snd
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.TaggedSupportWitnessData P hno_cross hK) :
    D.e.out.1 ≠ D.e.out.2 := by
  classical
  have heGraph : D.e ∈ S.graph.edgeSet := by
    exact
      ((Classical.choice hK).edgePath D.hxy).edges_subset_edgeSet
        D.edge_mem
  have hnot_diag : ¬ D.e.IsDiag :=
    S.graph.not_isDiag_of_mem_edgeSet heGraph
  intro h
  exact hnot_diag (by
    have hmk : Sym2.mk D.e.out.1 D.e.out.2 = D.e := D.e.out_eq
    rw [← hmk]
    simp [h])

end TaggedSupportWitnessData

/-- Fully unpacked form of `MixedEdgeTaggedSupportWitnesses`.

In addition to the three tagged host-edge witnesses, this records the
strict-subdivision consequence for every pair: either the corresponding
source-edge path supports are disjoint, or the two source edges share a
source endpoint.  The latter alternatives are the finite `K_5`/`K_{3,3}`
cases that the mixed-obstruction proof must analyze. -/
structure MixedEdgeTaggedSupportData
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph) : Type _ where
  right_or_path :
    GMIX24Split.TaggedSupportWitnessData P hno_cross hK
  right_or_path_tag :
    ((right_or_path.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
        right_or_path.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
        right_or_path.e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
      (right_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
        right_or_path.e.out.1 ∈ P.pathSet ∧
        right_or_path.e.out.2 ∈ P.pathSet))
  left_or_path :
    GMIX24Split.TaggedSupportWitnessData P hno_cross hK
  left_or_path_tag :
    ((left_or_path.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
        left_or_path.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
        left_or_path.e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
      (left_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
        left_or_path.e.out.1 ∈ P.pathSet ∧
        left_or_path.e.out.2 ∈ P.pathSet))
  left_or_right :
    GMIX24Split.TaggedSupportWitnessData P hno_cross hK
  left_or_right_tag :
    ((left_or_right.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
        left_or_right.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
        left_or_right.e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
      (left_or_right.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
        left_or_right.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
        left_or_right.e.out.2 ∈ P.rightSide ∪ P.pathSet))
  right_left_relation :
    Disjoint right_or_path.supportSet left_or_path.supportSet ∨
      right_or_path.SourceEdgesShareEndpoint left_or_path
  right_side_relation :
    Disjoint right_or_path.supportSet left_or_right.supportSet ∨
      right_or_path.SourceEdgesShareEndpoint left_or_right
  left_side_relation :
    Disjoint left_or_path.supportSet left_or_right.supportSet ∨
      left_or_path.SourceEdgesShareEndpoint left_or_right

/-- The selected source edges have one endpoint in common. -/
abbrev MixedEdgeTaggedSupportData.CommonSourceEndpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) : Prop :=
  Exists fun v : W =>
    (v = D.right_or_path.x ∨ v = D.right_or_path.y) ∧
      (v = D.left_or_path.x ∨ v = D.left_or_path.y) ∧
        (v = D.left_or_right.x ∨ v = D.left_or_right.y)

/-- The three-source cover alternative for the six endpoints of the selected
mixed `K_5` source edges.  Naming this source-combinatorial predicate keeps
the obstruction interfaces independent of its expanded finite encoding. -/
abbrev MixedEdgeTaggedSupportData.K5ThreeSourceCover
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5) : Prop :=
  Exists fun x : Fin 5 =>
    Exists fun y : Fin 5 =>
      Exists fun z : Fin 5 =>
        (D.right_or_path.x = x ∨ D.right_or_path.x = y ∨
          D.right_or_path.x = z) ∧
        (D.right_or_path.y = x ∨ D.right_or_path.y = y ∨
          D.right_or_path.y = z) ∧
        (D.left_or_path.x = x ∨ D.left_or_path.x = y ∨
          D.left_or_path.x = z) ∧
        (D.left_or_path.y = x ∨ D.left_or_path.y = y ∨
          D.left_or_path.y = z) ∧
        (D.left_or_right.x = x ∨ D.left_or_right.x = y ∨
          D.left_or_right.x = z) ∧
        (D.left_or_right.y = x ∨ D.left_or_right.y = y ∨
          D.left_or_right.y = z)

theorem mixedEdgeTaggedSupportData_of_witnesses
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (H : GMIX24Split.MixedEdgeTaggedSupportWitnesses P hno_cross hK) :
    Nonempty (GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) := by
  classical
  rcases H.right_or_path with
    ⟨rx, ry, rhxy, re, rhe, rhs1, rhs2, rtag⟩
  rcases H.left_or_path with
    ⟨lx, ly, lhxy, le, lhe, lhs1, lhs2, ltag⟩
  rcases H.left_or_right with
    ⟨sx, sy, shxy, se, she, shs1, shs2, stag⟩
  let R : GMIX24Split.TaggedSupportWitnessData P hno_cross hK := {
    x := rx
    y := ry
    hxy := rhxy
    e := re
    edge_mem := rhe
    out_fst_support := rhs1
    out_snd_support := rhs2
  }
  let L : GMIX24Split.TaggedSupportWitnessData P hno_cross hK := {
    x := lx
    y := ly
    hxy := lhxy
    e := le
    edge_mem := lhe
    out_fst_support := lhs1
    out_snd_support := lhs2
  }
  let Sdata : GMIX24Split.TaggedSupportWitnessData P hno_cross hK := {
    x := sx
    y := sy
    hxy := shxy
    e := se
    edge_mem := she
    out_fst_support := shs1
    out_snd_support := shs2
  }
  refine ⟨{
    right_or_path := R
    right_or_path_tag := by simpa [R] using rtag
    left_or_path := L
    left_or_path_tag := by simpa [L] using ltag
    left_or_right := Sdata
    left_or_right_tag := by simpa [Sdata] using stag
    right_left_relation :=
      GMIX24Split.TaggedSupportWitnessData.support_disjoint_or_sourceEdgesShareEndpoint
        R L
    right_side_relation :=
      GMIX24Split.TaggedSupportWitnessData.support_disjoint_or_sourceEdgesShareEndpoint
        R Sdata
    left_side_relation :=
      GMIX24Split.TaggedSupportWitnessData.support_disjoint_or_sourceEdgesShareEndpoint
        L Sdata
  }⟩

theorem tagged_support_obstruction_of_data_obstruction
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (hdata :
      Nonempty (GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) ->
        Nonempty S.Cross ∨ Nonempty S.Tripod) :
    GMIX24Split.MixedEdgeTaggedSupportWitnesses P hno_cross hK ->
      Nonempty S.Cross ∨ Nonempty S.Tripod := by
  intro H
  exact hdata
    (GMIX24Split.mixedEdgeTaggedSupportData_of_witnesses
      P hno_cross H)

theorem MixedEdgeTaggedSupportData.right_or_path_endpoint_regions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    ((D.right_or_path.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
        D.right_or_path.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
        D.right_or_path.e.out.2 ∈ P.rightSide ∪ P.pathSet) ∨
      (D.right_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
        D.right_or_path.e.out.1 ∈ P.pathSet ∧
        D.right_or_path.e.out.2 ∈ P.pathSet)) := by
  exact D.right_or_path_tag

theorem MixedEdgeTaggedSupportData.left_or_path_endpoint_regions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    ((D.left_or_path.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
        D.left_or_path.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
        D.left_or_path.e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
      (D.left_or_path.e ∈ P.pathEdgeGraph.edgeSet ∧
        D.left_or_path.e.out.1 ∈ P.pathSet ∧
        D.left_or_path.e.out.2 ∈ P.pathSet)) := by
  exact D.left_or_path_tag

theorem MixedEdgeTaggedSupportData.left_or_right_endpoint_regions
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    ((D.left_or_right.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∧
        D.left_or_right.e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
        D.left_or_right.e.out.2 ∈ P.leftSide ∪ P.pathSet) ∨
      (D.left_or_right.e ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∧
        D.left_or_right.e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
        D.left_or_right.e.out.2 ∈ P.rightSide ∪ P.pathSet)) := by
  exact D.left_or_right_tag

theorem MixedEdgeTaggedSupportData.right_or_path_out_fst_mem_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    D.right_or_path.e.out.1 ∈ P.rightSide ∪ P.pathSet := by
  rcases D.right_or_path_endpoint_regions with hright | hpath
  · exact hright.2.1
  · exact Or.inr hpath.2.1

theorem MixedEdgeTaggedSupportData.right_or_path_out_snd_mem_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    D.right_or_path.e.out.2 ∈ P.rightSide ∪ P.pathSet := by
  rcases D.right_or_path_endpoint_regions with hright | hpath
  · exact hright.2.2
  · exact Or.inr hpath.2.2

theorem MixedEdgeTaggedSupportData.left_or_path_out_fst_mem_left_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    D.left_or_path.e.out.1 ∈ P.leftSide ∪ P.pathSet := by
  rcases D.left_or_path_endpoint_regions with hleft | hpath
  · exact hleft.2.1
  · exact Or.inr hpath.2.1

theorem MixedEdgeTaggedSupportData.left_or_path_out_snd_mem_left_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    D.left_or_path.e.out.2 ∈ P.leftSide ∪ P.pathSet := by
  rcases D.left_or_path_endpoint_regions with hleft | hpath
  · exact hleft.2.2
  · exact Or.inr hpath.2.2

theorem MixedEdgeTaggedSupportData.left_or_right_out_fst_mem_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    D.left_or_right.e.out.1 ∈ (P.leftSide ∪ P.rightSide) ∪ P.pathSet := by
  rcases D.left_or_right_endpoint_regions with hleft | hright
  · rcases hleft.2.1 with hside | hpath
    · exact Or.inl (Or.inl hside)
    · exact Or.inr hpath
  · rcases hright.2.1 with hside | hpath
    · exact Or.inl (Or.inr hside)
    · exact Or.inr hpath

theorem MixedEdgeTaggedSupportData.left_or_right_out_snd_mem_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) :
    D.left_or_right.e.out.2 ∈ (P.leftSide ∪ P.rightSide) ∪ P.pathSet := by
  rcases D.left_or_right_endpoint_regions with hleft | hright
  · rcases hleft.2.2 with hside | hpath
    · exact Or.inl (Or.inl hside)
    · exact Or.inr hpath
  · rcases hright.2.2 with hside | hpath
    · exact Or.inl (Or.inr hside)
    · exact Or.inr hpath

def MixedEdgeTaggedSupportData.rightLeftSame
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) : Prop :=
  ((D.right_or_path.x = D.left_or_path.x ∧
      D.right_or_path.y = D.left_or_path.y) ∨
    (D.right_or_path.x = D.left_or_path.y ∧
      D.right_or_path.y = D.left_or_path.x))

def MixedEdgeTaggedSupportData.rightSideSame
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) : Prop :=
  ((D.right_or_path.x = D.left_or_right.x ∧
      D.right_or_path.y = D.left_or_right.y) ∨
    (D.right_or_path.x = D.left_or_right.y ∧
      D.right_or_path.y = D.left_or_right.x))

def MixedEdgeTaggedSupportData.leftSideSame
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK) : Prop :=
  ((D.left_or_path.x = D.left_or_right.x ∧
      D.left_or_path.y = D.left_or_right.y) ∨
    (D.left_or_path.x = D.left_or_right.y ∧
      D.left_or_path.y = D.left_or_right.x))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
