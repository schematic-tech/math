import Schematic.Math.GraphTheory.Subdivisions.SourceEmbeddings

/-! Extra K5 subdivision paths relative to a selected source triangle. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

/-- For a strict `K_5` subdivision and three selected source vertices, record
the two unused source vertices and the six source-edge paths from them to the
selected triple. This is the finite source-graph package needed in the
triangle-source branch of mixed Kuratowski localization. -/
structure StrictSubdivisionModel.K5TriangleExtraPaths
    {V : Type v} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K5Graph G) (a b c : Fin 5) : Type v where
  d : Fin 5
  e : Fin 5
  d_ne_e : d ≠ e
  d_ne_a : d ≠ a
  d_ne_b : d ≠ b
  d_ne_c : d ≠ c
  e_ne_a : e ≠ a
  e_ne_b : e ≠ b
  e_ne_c : e ≠ c
  d_a_path : G.Walk (M.branchVertex d) (M.branchVertex a)
  d_a_isPath : d_a_path.IsPath
  d_a_support_subset :
    forall w : V, w ∈ d_a_path.support ->
      w ∈ (M.edgePath (K5Graph.adj_of_ne d_ne_a)).support
  d_b_path : G.Walk (M.branchVertex d) (M.branchVertex b)
  d_b_isPath : d_b_path.IsPath
  d_b_support_subset :
    forall w : V, w ∈ d_b_path.support ->
      w ∈ (M.edgePath (K5Graph.adj_of_ne d_ne_b)).support
  d_c_path : G.Walk (M.branchVertex d) (M.branchVertex c)
  d_c_isPath : d_c_path.IsPath
  d_c_support_subset :
    forall w : V, w ∈ d_c_path.support ->
      w ∈ (M.edgePath (K5Graph.adj_of_ne d_ne_c)).support
  e_a_path : G.Walk (M.branchVertex e) (M.branchVertex a)
  e_a_isPath : e_a_path.IsPath
  e_a_support_subset :
    forall w : V, w ∈ e_a_path.support ->
      w ∈ (M.edgePath (K5Graph.adj_of_ne e_ne_a)).support
  e_b_path : G.Walk (M.branchVertex e) (M.branchVertex b)
  e_b_isPath : e_b_path.IsPath
  e_b_support_subset :
    forall w : V, w ∈ e_b_path.support ->
      w ∈ (M.edgePath (K5Graph.adj_of_ne e_ne_b)).support
  e_c_path : G.Walk (M.branchVertex e) (M.branchVertex c)
  e_c_isPath : e_c_path.IsPath
  e_c_support_subset :
    forall w : V, w ∈ e_c_path.support ->
      w ∈ (M.edgePath (K5Graph.adj_of_ne e_ne_c)).support

noncomputable def StrictSubdivisionModel.K5TriangleExtraPaths.of_sources
    {V : Type v} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K5Graph G) (a b c : Fin 5) :
    M.K5TriangleExtraPaths a b c := by
  classical
  let d : Fin 5 := Classical.choose (K5Graph.exists_two_vertices_not_three a b c)
  let Hde := Classical.choose_spec (K5Graph.exists_two_vertices_not_three a b c)
  let e : Fin 5 := Classical.choose Hde
  have he := Classical.choose_spec Hde
  have hde : d ≠ e := he.1
  have hda : d ≠ a := he.2.1
  have hdb : d ≠ b := he.2.2.1
  have hdc : d ≠ c := he.2.2.2.1
  have hea : e ≠ a := he.2.2.2.2.1
  have heb : e ≠ b := he.2.2.2.2.2.1
  have hec : e ≠ c := he.2.2.2.2.2.2
  exact {
    d := d
    e := e
    d_ne_e := hde
    d_ne_a := hda
    d_ne_b := hdb
    d_ne_c := hdc
    e_ne_a := hea
    e_ne_b := heb
    e_ne_c := hec
    d_a_path := M.edgePath (K5Graph.adj_of_ne hda)
    d_a_isPath := M.edgePath_isPath (K5Graph.adj_of_ne hda)
    d_a_support_subset := by intro w hw; simpa using hw
    d_b_path := M.edgePath (K5Graph.adj_of_ne hdb)
    d_b_isPath := M.edgePath_isPath (K5Graph.adj_of_ne hdb)
    d_b_support_subset := by intro w hw; simpa using hw
    d_c_path := M.edgePath (K5Graph.adj_of_ne hdc)
    d_c_isPath := M.edgePath_isPath (K5Graph.adj_of_ne hdc)
    d_c_support_subset := by intro w hw; simpa using hw
    e_a_path := M.edgePath (K5Graph.adj_of_ne hea)
    e_a_isPath := M.edgePath_isPath (K5Graph.adj_of_ne hea)
    e_a_support_subset := by intro w hw; simpa using hw
    e_b_path := M.edgePath (K5Graph.adj_of_ne heb)
    e_b_isPath := M.edgePath_isPath (K5Graph.adj_of_ne heb)
    e_b_support_subset := by intro w hw; simpa using hw
    e_c_path := M.edgePath (K5Graph.adj_of_ne hec)
    e_c_isPath := M.edgePath_isPath (K5Graph.adj_of_ne hec)
    e_c_support_subset := by intro w hw; simpa using hw
  }

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_branchVertex_ne_e
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c) :
    M.branchVertex T.d ≠ M.branchVertex T.e := by
  intro h
  exact T.d_ne_e (M.branchVertex_injective h)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_branchVertex_ne_a
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c) :
    M.branchVertex T.d ≠ M.branchVertex a := by
  intro h
  exact T.d_ne_a (M.branchVertex_injective h)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_branchVertex_ne_b
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c) :
    M.branchVertex T.d ≠ M.branchVertex b := by
  intro h
  exact T.d_ne_b (M.branchVertex_injective h)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_branchVertex_ne_c
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c) :
    M.branchVertex T.d ≠ M.branchVertex c := by
  intro h
  exact T.d_ne_c (M.branchVertex_injective h)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.e_branchVertex_ne_a
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c) :
    M.branchVertex T.e ≠ M.branchVertex a := by
  intro h
  exact T.e_ne_a (M.branchVertex_injective h)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.e_branchVertex_ne_b
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c) :
    M.branchVertex T.e ≠ M.branchVertex b := by
  intro h
  exact T.e_ne_b (M.branchVertex_injective h)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.e_branchVertex_ne_c
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c) :
    M.branchVertex T.e ≠ M.branchVertex c := by
  intro h
  exact T.e_ne_c (M.branchVertex_injective h)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_a_inter_e_a_eq_a
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    {w : V}
    (hwd : w ∈ T.d_a_path.support)
    (hwe : w ∈ T.e_a_path.support) :
    w = M.branchVertex a := by
  have hwd' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_a)).support :=
    T.d_a_support_subset w hwd
  have hwe' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_a)).support :=
    T.e_a_support_subset w hwe
  have hne :
      Not ((T.d = T.e ∧ a = a) ∨ (T.d = a ∧ a = T.e)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact T.d_ne_e hsame.1
    · exact T.d_ne_a hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.d ∨ u = a) -> (u = T.e ∨ u = a) -> u = a := by
    intro u huD huE
    rcases huD with rfl | rfl
    · rcases huE with hdE | hdA
      · exact False.elim (T.d_ne_e hdE)
      · exact False.elim (T.d_ne_a hdA)
    · rfl
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.d_ne_a) (K5Graph.adj_of_ne T.e_ne_a)
      hne hunique hwd' hwe'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_b_inter_e_b_eq_b
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    {w : V}
    (hwd : w ∈ T.d_b_path.support)
    (hwe : w ∈ T.e_b_path.support) :
    w = M.branchVertex b := by
  have hwd' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_b)).support :=
    T.d_b_support_subset w hwd
  have hwe' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_b)).support :=
    T.e_b_support_subset w hwe
  have hne :
      Not ((T.d = T.e ∧ b = b) ∨ (T.d = b ∧ b = T.e)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact T.d_ne_e hsame.1
    · exact T.d_ne_b hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.d ∨ u = b) -> (u = T.e ∨ u = b) -> u = b := by
    intro u huD huE
    rcases huD with rfl | rfl
    · rcases huE with hdE | hdB
      · exact False.elim (T.d_ne_e hdE)
      · exact False.elim (T.d_ne_b hdB)
    · rfl
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.d_ne_b) (K5Graph.adj_of_ne T.e_ne_b)
      hne hunique hwd' hwe'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_c_inter_e_c_eq_c
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    {w : V}
    (hwd : w ∈ T.d_c_path.support)
    (hwe : w ∈ T.e_c_path.support) :
    w = M.branchVertex c := by
  have hwd' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_c)).support :=
    T.d_c_support_subset w hwd
  have hwe' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_c)).support :=
    T.e_c_support_subset w hwe
  have hne :
      Not ((T.d = T.e ∧ c = c) ∨ (T.d = c ∧ c = T.e)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact T.d_ne_e hsame.1
    · exact T.d_ne_c hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.d ∨ u = c) -> (u = T.e ∨ u = c) -> u = c := by
    intro u huD huE
    rcases huD with rfl | rfl
    · rcases huE with hdE | hdC
      · exact False.elim (T.d_ne_e hdE)
      · exact False.elim (T.d_ne_c hdC)
    · rfl
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.d_ne_c) (K5Graph.adj_of_ne T.e_ne_c)
      hne hunique hwd' hwe'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_a_inter_d_b_eq_d
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hab : a ≠ b)
    {w : V}
    (hwa : w ∈ T.d_a_path.support)
    (hwb : w ∈ T.d_b_path.support) :
    w = M.branchVertex T.d := by
  have hwa' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_a)).support :=
    T.d_a_support_subset w hwa
  have hwb' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_b)).support :=
    T.d_b_support_subset w hwb
  have hne :
      Not ((T.d = T.d ∧ a = b) ∨ (T.d = b ∧ a = T.d)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact hab hsame.2
    · exact T.d_ne_b hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.d ∨ u = a) -> (u = T.d ∨ u = b) -> u = T.d := by
    intro u huA huB
    rcases huA with rfl | rfl
    · rfl
    · rcases huB with haD | haB
      · exact False.elim (T.d_ne_a haD.symm)
      · exact False.elim (hab haB)
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.d_ne_a) (K5Graph.adj_of_ne T.d_ne_b)
      hne hunique hwa' hwb'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_a_inter_d_c_eq_d
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hac : a ≠ c)
    {w : V}
    (hwa : w ∈ T.d_a_path.support)
    (hwc : w ∈ T.d_c_path.support) :
    w = M.branchVertex T.d := by
  have hwa' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_a)).support :=
    T.d_a_support_subset w hwa
  have hwc' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_c)).support :=
    T.d_c_support_subset w hwc
  have hne :
      Not ((T.d = T.d ∧ a = c) ∨ (T.d = c ∧ a = T.d)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact hac hsame.2
    · exact T.d_ne_c hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.d ∨ u = a) -> (u = T.d ∨ u = c) -> u = T.d := by
    intro u huA huC
    rcases huA with rfl | rfl
    · rfl
    · rcases huC with haD | haC
      · exact False.elim (T.d_ne_a haD.symm)
      · exact False.elim (hac haC)
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.d_ne_a) (K5Graph.adj_of_ne T.d_ne_c)
      hne hunique hwa' hwc'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_b_inter_d_c_eq_d
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hbc : b ≠ c)
    {w : V}
    (hwb : w ∈ T.d_b_path.support)
    (hwc : w ∈ T.d_c_path.support) :
    w = M.branchVertex T.d := by
  have hwb' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_b)).support :=
    T.d_b_support_subset w hwb
  have hwc' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_c)).support :=
    T.d_c_support_subset w hwc
  have hne :
      Not ((T.d = T.d ∧ b = c) ∨ (T.d = c ∧ b = T.d)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact hbc hsame.2
    · exact T.d_ne_c hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.d ∨ u = b) -> (u = T.d ∨ u = c) -> u = T.d := by
    intro u huB huC
    rcases huB with rfl | rfl
    · rfl
    · rcases huC with hbD | hbC
      · exact False.elim (T.d_ne_b hbD.symm)
      · exact False.elim (hbc hbC)
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.d_ne_b) (K5Graph.adj_of_ne T.d_ne_c)
      hne hunique hwb' hwc'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.e_a_inter_e_b_eq_e
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hab : a ≠ b)
    {w : V}
    (hwa : w ∈ T.e_a_path.support)
    (hwb : w ∈ T.e_b_path.support) :
    w = M.branchVertex T.e := by
  have hwa' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_a)).support :=
    T.e_a_support_subset w hwa
  have hwb' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_b)).support :=
    T.e_b_support_subset w hwb
  have hne :
      Not ((T.e = T.e ∧ a = b) ∨ (T.e = b ∧ a = T.e)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact hab hsame.2
    · exact T.e_ne_b hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.e ∨ u = a) -> (u = T.e ∨ u = b) -> u = T.e := by
    intro u huA huB
    rcases huA with rfl | rfl
    · rfl
    · rcases huB with haE | haB
      · exact False.elim (T.e_ne_a haE.symm)
      · exact False.elim (hab haB)
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.e_ne_a) (K5Graph.adj_of_ne T.e_ne_b)
      hne hunique hwa' hwb'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.e_a_inter_e_c_eq_e
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hac : a ≠ c)
    {w : V}
    (hwa : w ∈ T.e_a_path.support)
    (hwc : w ∈ T.e_c_path.support) :
    w = M.branchVertex T.e := by
  have hwa' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_a)).support :=
    T.e_a_support_subset w hwa
  have hwc' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_c)).support :=
    T.e_c_support_subset w hwc
  have hne :
      Not ((T.e = T.e ∧ a = c) ∨ (T.e = c ∧ a = T.e)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact hac hsame.2
    · exact T.e_ne_c hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.e ∨ u = a) -> (u = T.e ∨ u = c) -> u = T.e := by
    intro u huA huC
    rcases huA with rfl | rfl
    · rfl
    · rcases huC with haE | haC
      · exact False.elim (T.e_ne_a haE.symm)
      · exact False.elim (hac haC)
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.e_ne_a) (K5Graph.adj_of_ne T.e_ne_c)
      hne hunique hwa' hwc'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.e_b_inter_e_c_eq_e
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hbc : b ≠ c)
    {w : V}
    (hwb : w ∈ T.e_b_path.support)
    (hwc : w ∈ T.e_c_path.support) :
    w = M.branchVertex T.e := by
  have hwb' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_b)).support :=
    T.e_b_support_subset w hwb
  have hwc' : w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_c)).support :=
    T.e_c_support_subset w hwc
  have hne :
      Not ((T.e = T.e ∧ b = c) ∨ (T.e = c ∧ b = T.e)) := by
    intro hsame
    rcases hsame with hsame | hrev
    · exact hbc hsame.2
    · exact T.e_ne_c hrev.1
  have hunique :
      forall u : Fin 5,
        (u = T.e ∨ u = b) -> (u = T.e ∨ u = c) -> u = T.e := by
    intro u huB huC
    rcases huB with rfl | rfl
    · rfl
    · rcases huC with hbE | hbC
      · exact False.elim (T.e_ne_b hbE.symm)
      · exact False.elim (hbc hbC)
  exact
    M.edgePath_support_inter_eq_common_branchVertex
      (K5Graph.adj_of_ne T.e_ne_b) (K5Graph.adj_of_ne T.e_ne_c)
      hne hunique hwb' hwc'

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_a_disjoint_e_b
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hab : a ≠ b) :
    Disjoint
      {w : V | w ∈ T.d_a_path.support}
      {w : V | w ∈ T.e_b_path.support} := by
  have hdisj :
      Disjoint
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_a)).support}
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_b)).support} :=
    M.edgePath_support_disjoint_of_no_common_endpoint
      (K5Graph.adj_of_ne T.d_ne_a) (K5Graph.adj_of_ne T.e_ne_b)
      T.d_ne_e T.d_ne_b (fun hae => T.e_ne_a hae.symm) hab
  rw [Set.disjoint_left]
  intro w hwa hwb
  exact Set.disjoint_left.mp hdisj
    (T.d_a_support_subset w hwa) (T.e_b_support_subset w hwb)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_a_disjoint_e_c
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hac : a ≠ c) :
    Disjoint
      {w : V | w ∈ T.d_a_path.support}
      {w : V | w ∈ T.e_c_path.support} := by
  have hdisj :
      Disjoint
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_a)).support}
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_c)).support} :=
    M.edgePath_support_disjoint_of_no_common_endpoint
      (K5Graph.adj_of_ne T.d_ne_a) (K5Graph.adj_of_ne T.e_ne_c)
      T.d_ne_e T.d_ne_c (fun hae => T.e_ne_a hae.symm) hac
  rw [Set.disjoint_left]
  intro w hwa hwc
  exact Set.disjoint_left.mp hdisj
    (T.d_a_support_subset w hwa) (T.e_c_support_subset w hwc)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_b_disjoint_e_a
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hab : a ≠ b) :
    Disjoint
      {w : V | w ∈ T.d_b_path.support}
      {w : V | w ∈ T.e_a_path.support} := by
  have hdisj :
      Disjoint
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_b)).support}
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_a)).support} :=
    M.edgePath_support_disjoint_of_no_common_endpoint
      (K5Graph.adj_of_ne T.d_ne_b) (K5Graph.adj_of_ne T.e_ne_a)
      T.d_ne_e T.d_ne_a (fun hbe => T.e_ne_b hbe.symm) hab.symm
  rw [Set.disjoint_left]
  intro w hwb hwa
  exact Set.disjoint_left.mp hdisj
    (T.d_b_support_subset w hwb) (T.e_a_support_subset w hwa)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_b_disjoint_e_c
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hbc : b ≠ c) :
    Disjoint
      {w : V | w ∈ T.d_b_path.support}
      {w : V | w ∈ T.e_c_path.support} := by
  have hdisj :
      Disjoint
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_b)).support}
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_c)).support} :=
    M.edgePath_support_disjoint_of_no_common_endpoint
      (K5Graph.adj_of_ne T.d_ne_b) (K5Graph.adj_of_ne T.e_ne_c)
      T.d_ne_e T.d_ne_c (fun hbe => T.e_ne_b hbe.symm) hbc
  rw [Set.disjoint_left]
  intro w hwb hwc
  exact Set.disjoint_left.mp hdisj
    (T.d_b_support_subset w hwb) (T.e_c_support_subset w hwc)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_c_disjoint_e_a
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hac : a ≠ c) :
    Disjoint
      {w : V | w ∈ T.d_c_path.support}
      {w : V | w ∈ T.e_a_path.support} := by
  have hdisj :
      Disjoint
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_c)).support}
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_a)).support} :=
    M.edgePath_support_disjoint_of_no_common_endpoint
      (K5Graph.adj_of_ne T.d_ne_c) (K5Graph.adj_of_ne T.e_ne_a)
      T.d_ne_e T.d_ne_a (fun hce => T.e_ne_c hce.symm) hac.symm
  rw [Set.disjoint_left]
  intro w hwc hwa
  exact Set.disjoint_left.mp hdisj
    (T.d_c_support_subset w hwc) (T.e_a_support_subset w hwa)

theorem StrictSubdivisionModel.K5TriangleExtraPaths.d_c_disjoint_e_b
    {V : Type v} {G : SimpleGraph V}
    {M : StrictSubdivisionModel K5Graph G} {a b c : Fin 5}
    (T : M.K5TriangleExtraPaths a b c)
    (hbc : b ≠ c) :
    Disjoint
      {w : V | w ∈ T.d_c_path.support}
      {w : V | w ∈ T.e_b_path.support} := by
  have hdisj :
      Disjoint
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.d_ne_c)).support}
        {w : V | w ∈ (M.edgePath (K5Graph.adj_of_ne T.e_ne_b)).support} :=
    M.edgePath_support_disjoint_of_no_common_endpoint
      (K5Graph.adj_of_ne T.d_ne_c) (K5Graph.adj_of_ne T.e_ne_b)
      T.d_ne_e T.d_ne_b (fun hce => T.e_ne_c hce.symm) hbc.symm
  rw [Set.disjoint_left]
  intro w hwc hwb
  exact Set.disjoint_left.mp hdisj
    (T.d_c_support_subset w hwc) (T.e_b_support_subset w hwb)


end Schematic.Math.GraphTheory
