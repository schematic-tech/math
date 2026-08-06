import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c s t : W}
    (hst : K.Adj s t)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hsc : s ≠ c)
    (htc : t ≠ c) :
    forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target) := by
  intro qv hqv hqv_none
  have hc_support :
      M.branchVertex c ∈ (M.edgePath hst).support := by
    simpa [hc, hqv_none] using hqv
  have hc_endpoint : c = s ∨ c = t :=
    (M.branchVertex_mem_edgePath_support_iff hst).mp hc_support
  rcases hc_endpoint with hcs | hct
  · exact hsc hcs.symm
  · exact htc hct.symm

theorem strictSubdivisionModel_collapseEdge_branch_attachment_disjoint_clean_lift
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y s t : W}
    (hcy : K.Adj c y)
    (hst : K.Adj s t)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hsc : s ≠ c)
    (htc : t ≠ c)
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    {hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target)}
    {v : V}
    {q : G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy)}
    (hside : G.Adj a v ∨ G.Adj b v)
    (hq_reflect :
      forall z : V, z ∈ q.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z) :
    Disjoint
      (Walk.InternalVertices (Walk.branchAttachmentPath hab hside q))
      (Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          (havoid (M.branchVertex s) (M.edgePath hst).start_mem_support)
          (havoid (M.branchVertex t) (M.edgePath hst).end_mem_support)
          (M.edgePath hst) havoid)) := by
  classical
  rw [Set.disjoint_left]
  intro z hzarm hzclean
  let hs : M.branchVertex s ≠
      (none : (GraphContraction.collapseEdge G hab).Target) :=
    havoid (M.branchVertex s) (M.edgePath hst).start_mem_support
  let ht : M.branchVertex t ≠
      (none : (GraphContraction.collapseEdge G hab).Target) :=
    havoid (M.branchVertex t) (M.edgePath hst).end_mem_support
  have hzclean_out :
      z ∉ ({a, b} : Set V) :=
    GraphContraction.collapseEdgeWalkOutside_support_outside G hab
      hs ht (M.edgePath hst) havoid hzclean.1
  have hzarm_cases : z = a ∨ z = b ∨ z ∈ q.support := by
    have hz_support :=
      Walk.branchAttachmentPath_support_subset hab hside hzarm.1
    simpa using hz_support
  rcases hzarm_cases with rfl | rfl | hzq
  · exact hzclean_out (by simp)
  · exact hzclean_out (by simp)
  · rcases hq_reflect z hzq with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab hs ht (M.edgePath hst) havoid hzclean.1 with
      ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
    have hqv_rv : qv = rv :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
        (hqv_eq.trans hrv_eq.symm)
    have hqv_internal : qv ∈ Walk.InternalVertices (M.edgePath hcy) := by
      refine ⟨hqv_mem, ?_, ?_⟩
      · intro hqc
        exact hqv_ne (by simpa [hc] using hqc)
      · intro hqy
        have hz_end :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) hy := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
              hqv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) hy :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
                hy hqy
        exact hzarm.2.2 hz_end
    have hrv_internal : rv ∈ Walk.InternalVertices (M.edgePath hst) := by
      refine ⟨hrv_mem, ?_, ?_⟩
      · intro hrs
        have hz_start :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) hs := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
              hrv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) hs :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
                hs hrs
        exact hzclean.2.1 hz_start
      · intro hrt
        have hz_end :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex t) ht := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
              hrv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex t) ht :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
                ht hrt
        exact hzclean.2.2 hz_end
    have hne :
        Not ((c = s ∧ y = t) ∨ (c = t ∧ y = s)) := by
      intro hsame
      rcases hsame with hsame | hsame
      · exact hsc hsame.1.symm
      · exact htc hsame.1.symm
    exact Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hcy hst hne)
      hqv_internal (by simpa [hqv_rv] using hrv_internal)

theorem strictSubdivisionModel_collapseEdge_branch_attachment_no_uncollapsed_branch
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y w : W}
    (hcy : K.Adj c y)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hwc : w ≠ c)
    {hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target)}
    {v : V}
    {q : G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy)}
    (hside : G.Adj a v ∨ G.Adj b v)
    (hq_reflect :
      forall z : V, z ∈ q.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z)
    {z : V}
    (hz : z ∈ Walk.InternalVertices (Walk.branchAttachmentPath hab hside q)) :
    z ≠
      GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex w)
        (by
          intro hw_none
          exact hwc
            (M.branchVertex_injective (hw_none.trans hc.symm))) := by
  classical
  let hw_ne :
      M.branchVertex w ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro hw_none
    exact hwc (M.branchVertex_injective (hw_none.trans hc.symm))
  intro hzw
  have hz_cases : z = a ∨ z = b ∨ z ∈ q.support := by
    have hz_support :=
      Walk.branchAttachmentPath_support_subset hab hside hz.1
    simpa using hz_support
  rcases hz_cases with hza | hzb | hzq
  · exact
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab hw_ne
        (by
          rw [← hzw, hza]
          simp)
  · exact
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab hw_ne
        (by
          rw [← hzw, hzb]
          simp)
  · rcases hq_reflect z hzq with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    have hqv_branch : qv = M.branchVertex w :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hw_ne
        (hqv_eq.trans hzw)
    have hw_endpoint : w = c ∨ w = y := by
      have hmem : M.branchVertex w ∈ (M.edgePath hcy).support := by
        simpa [hqv_branch] using hqv_mem
      exact (M.branchVertex_mem_edgePath_support_iff hcy).mp hmem
    rcases hw_endpoint with hwc_eq | hwy
    · exact hwc hwc_eq
    · have hz_end :
          z =
            GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex w) hw_ne := hzw
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy := by
            subst w
            exact GraphContraction.collapseEdgeUncollapse_congr G hab
              hw_ne hy rfl
      exact hz.2.2 hz_end

theorem strictSubdivisionModel_collapseEdge_branch_attachment_direct_no_uncollapsed_branch
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y w : W}
    (hcy : K.Adj c y)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hwc : w ≠ c)
    {hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target)}
    {v : V}
    {q : G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy)}
    (hrootv : G.Adj root v)
    (hq_reflect :
      forall z : V, z ∈ q.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z)
    {z : V}
    (hz :
      z ∈ Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv) q)) :
    z ≠
      GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex w)
        (by
          intro hw_none
          exact hwc
            (M.branchVertex_injective (hw_none.trans hc.symm))) := by
  classical
  let hw_ne :
      M.branchVertex w ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro hw_none
    exact hwc (M.branchVertex_injective (hw_none.trans hc.symm))
  intro hzw
  have hz_cases : z = root ∨ z ∈ q.support := by
    have hz_support :=
      Walk.edge_append_support_subset_insert (q := q) hrootv
        (by simpa [Walk.branchAttachmentPath, hrootv] using hz.1)
    simpa using hz_support
  rcases hz_cases with hroot | hzq
  · exact
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab hw_ne
        (by
          rw [← hzw, hroot]
          exact hroot_pair)
  · rcases hq_reflect z hzq with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    have hqv_branch : qv = M.branchVertex w :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hw_ne
        (hqv_eq.trans hzw)
    have hw_endpoint : w = c ∨ w = y := by
      have hmem : M.branchVertex w ∈ (M.edgePath hcy).support := by
        simpa [hqv_branch] using hqv_mem
      exact (M.branchVertex_mem_edgePath_support_iff hcy).mp hmem
    rcases hw_endpoint with hwc_eq | hwy
    · exact hwc hwc_eq
    · have hz_end :
          z =
            GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex w) hw_ne := hzw
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy := by
            subst w
            exact GraphContraction.collapseEdgeUncollapse_congr G hab
              hw_ne hy rfl
      exact hz.2.2 hz_end

theorem strictSubdivisionModel_collapseEdge_branch_attachment_direct_no_listed_branches
    {W B : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y : W}
    (hcy : K.Adj c y)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    {hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target)}
    {v : V}
    {q : G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy)}
    (hrootv : G.Adj root v)
    (hq_outside : forall z : V, z ∈ q.support -> z ∉ ({a, b} : Set V))
    (hq_reflect :
      forall z : V, z ∈ q.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z)
    (branch : B -> V)
    (hbranch_cases :
      forall w : B,
        branch w = root ∨ branch w = other ∨
          Exists fun x : W =>
            x ≠ c ∧
              Exists fun hx :
                M.branchVertex x ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                branch w =
                  GraphContraction.collapseEdgeUncollapse G hab
                    (M.branchVertex x) hx)
    {z : V}
    (hz :
      z ∈ Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv) q))
    (w : B) :
    z ≠ branch w := by
  classical
  rcases hbranch_cases w with hroot | hother | huncollapsed
  · intro hzw
    exact hz.2.1 (hzw.trans hroot)
  · have hother_not : other ∉ q.support := by
      intro hmem
      exact hq_outside other hmem hother_pair
    have hnot :
        other ∉
          Walk.InternalVertices
            (Walk.branchAttachmentPath hroot_other (Or.inl hrootv) q) :=
      Walk.branchAttachmentPath_direct_other_not_mem_internal
        hroot_other hrootv hother_not
    intro hzw
    exact hnot (by simpa [hzw, hother] using hz)
  · rcases huncollapsed with ⟨x, hxc, hx, hw_eq⟩
    have hz_ne :=
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_no_uncollapsed_branch
        hab hroot_pair hroot_other M hcy hc hxc hrootv hq_reflect hz
    intro hzw
    apply hz_ne
    calc
      z = branch w := hzw
      _ =
          GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex x) hx := hw_eq
      _ =
          GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex x)
            (by
              intro hw_none
              exact hxc
                (M.branchVertex_injective (hw_none.trans hc.symm))) := by
            exact
              (GraphContraction.collapseEdgeUncollapse_congr G hab hx _ rfl)

theorem strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y s t : W}
    (hcy : K.Adj c y)
    (hst : K.Adj s t)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hsc : s ≠ c)
    (htc : t ≠ c)
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    {hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target)}
    {v : V}
    {q : G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy)}
    (hrootv : G.Adj root v)
    (hq_reflect :
      forall z : V, z ∈ q.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z) :
    Disjoint
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv) q))
      (Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          (havoid (M.branchVertex s) (M.edgePath hst).start_mem_support)
          (havoid (M.branchVertex t) (M.edgePath hst).end_mem_support)
          (M.edgePath hst) havoid)) := by
  classical
  rw [Set.disjoint_left]
  intro z hzarm hzclean
  let hs : M.branchVertex s ≠
      (none : (GraphContraction.collapseEdge G hab).Target) :=
    havoid (M.branchVertex s) (M.edgePath hst).start_mem_support
  let ht : M.branchVertex t ≠
      (none : (GraphContraction.collapseEdge G hab).Target) :=
    havoid (M.branchVertex t) (M.edgePath hst).end_mem_support
  have hzclean_out :
      z ∉ ({a, b} : Set V) :=
    GraphContraction.collapseEdgeWalkOutside_support_outside G hab
      hs ht (M.edgePath hst) havoid hzclean.1
  have hzarm_cases : z = root ∨ z ∈ q.support := by
    have hz_support :=
      Walk.edge_append_support_subset_insert (q := q) hrootv
        (by simpa [Walk.branchAttachmentPath, hrootv] using hzarm.1)
    simpa using hz_support
  rcases hzarm_cases with hroot | hzq
  · exact hzclean_out (by simpa [hroot] using hroot_pair)
  · rcases hq_reflect z hzq with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab hs ht (M.edgePath hst) havoid hzclean.1 with
      ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
    have hqv_rv : qv = rv :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
        (hqv_eq.trans hrv_eq.symm)
    have hqv_internal : qv ∈ Walk.InternalVertices (M.edgePath hcy) := by
      refine ⟨hqv_mem, ?_, ?_⟩
      · intro hqc
        exact hqv_ne (by simpa [hc] using hqc)
      · intro hqy
        have hz_end :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) hy := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
              hqv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) hy :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
                hy hqy
        exact hzarm.2.2 hz_end
    have hrv_internal : rv ∈ Walk.InternalVertices (M.edgePath hst) := by
      refine ⟨hrv_mem, ?_, ?_⟩
      · intro hrs
        have hz_start :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) hs := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
              hrv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) hs :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
                hs hrs
        exact hzclean.2.1 hz_start
      · intro hrt
        have hz_end :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex t) ht := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
              hrv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex t) ht :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
                ht hrt
        exact hzclean.2.2 hz_end
    have hne :
        Not ((c = s ∧ y = t) ∨ (c = t ∧ y = s)) := by
      intro hsame
      rcases hsame with hsame | hsame
      · exact hsc hsame.1.symm
      · exact htc hsame.1.symm
    exact Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hcy hst hne)
      hqv_internal (by simpa [hqv_rv] using hrv_internal)

theorem strictSubdivisionModel_collapseEdge_branch_attachment_root_no_uncollapsed_branch
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y w : W}
    (hcy : K.Adj c y)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hwc : w ≠ c)
    {hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target)}
    {v : V}
    {q : G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy)}
    (hside : G.Adj root v ∨ G.Adj other v)
    (hq_reflect :
      forall z : V, z ∈ q.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z)
    {z : V}
    (hz :
      z ∈ Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other hside q)) :
    z ≠
      GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex w)
        (by
          intro hw_none
          exact hwc
            (M.branchVertex_injective (hw_none.trans hc.symm))) := by
  classical
  let hw_ne :
      M.branchVertex w ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro hw_none
    exact hwc (M.branchVertex_injective (hw_none.trans hc.symm))
  intro hzw
  have hz_cases : z = root ∨ z = other ∨ z ∈ q.support := by
    have hz_support :=
      Walk.branchAttachmentPath_support_subset hroot_other hside hz.1
    simpa using hz_support
  rcases hz_cases with hroot | hother | hzq
  · exact
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab hw_ne
        (by
          rw [← hzw, hroot]
          exact hroot_pair)
  · exact
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab hw_ne
        (by
          rw [← hzw, hother]
          exact hother_pair)
  · rcases hq_reflect z hzq with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    have hqv_branch : qv = M.branchVertex w :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hw_ne
        (hqv_eq.trans hzw)
    have hw_endpoint : w = c ∨ w = y := by
      have hmem : M.branchVertex w ∈ (M.edgePath hcy).support := by
        simpa [hqv_branch] using hqv_mem
      exact (M.branchVertex_mem_edgePath_support_iff hcy).mp hmem
    rcases hw_endpoint with hwc_eq | hwy
    · exact hwc hwc_eq
    · have hz_end :
          z =
            GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex w) hw_ne := hzw
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy := by
            subst w
            exact GraphContraction.collapseEdgeUncollapse_congr G hab
              hw_ne hy rfl
      exact hz.2.2 hz_end

theorem strictSubdivisionModel_collapseEdge_branch_attachment_root_disjoint_clean_lift
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y s t : W}
    (hcy : K.Adj c y)
    (hst : K.Adj s t)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hsc : s ≠ c)
    (htc : t ≠ c)
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    {hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target)}
    {v : V}
    {q : G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy)}
    (hside : G.Adj root v ∨ G.Adj other v)
    (hq_reflect :
      forall z : V, z ∈ q.support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z) :
    Disjoint
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other hside q))
      (Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          (havoid (M.branchVertex s) (M.edgePath hst).start_mem_support)
          (havoid (M.branchVertex t) (M.edgePath hst).end_mem_support)
          (M.edgePath hst) havoid)) := by
  classical
  rw [Set.disjoint_left]
  intro z hzarm hzclean
  let hs : M.branchVertex s ≠
      (none : (GraphContraction.collapseEdge G hab).Target) :=
    havoid (M.branchVertex s) (M.edgePath hst).start_mem_support
  let ht : M.branchVertex t ≠
      (none : (GraphContraction.collapseEdge G hab).Target) :=
    havoid (M.branchVertex t) (M.edgePath hst).end_mem_support
  have hzclean_out :
      z ∉ ({a, b} : Set V) :=
    GraphContraction.collapseEdgeWalkOutside_support_outside G hab
      hs ht (M.edgePath hst) havoid hzclean.1
  have hzarm_cases : z = root ∨ z = other ∨ z ∈ q.support := by
    have hz_support :=
      Walk.branchAttachmentPath_support_subset hroot_other hside hzarm.1
    simpa using hz_support
  rcases hzarm_cases with hroot | hother | hzq
  · exact hzclean_out (by rw [hroot]; exact hroot_pair)
  · exact hzclean_out (by rw [hother]; exact hother_pair)
  · rcases hq_reflect z hzq with ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
    rcases
        GraphContraction.collapseEdgeWalkOutside_support_reflects
          G hab hs ht (M.edgePath hst) havoid hzclean.1 with
      ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
    have hqv_rv : qv = rv :=
      GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
        (hqv_eq.trans hrv_eq.symm)
    have hqv_internal : qv ∈ Walk.InternalVertices (M.edgePath hcy) := by
      refine ⟨hqv_mem, ?_, ?_⟩
      · intro hqc
        exact hqv_ne (by simpa [hc] using hqc)
      · intro hqy
        have hz_end :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) hy := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
              hqv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex y) hy :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
                hy hqy
        exact hzarm.2.2 hz_end
    have hrv_internal : rv ∈ Walk.InternalVertices (M.edgePath hst) := by
      refine ⟨hrv_mem, ?_, ?_⟩
      · intro hrs
        have hz_start :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) hs := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
              hrv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) hs :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
                hs hrs
        exact hzclean.2.1 hz_start
      · intro hrt
        have hz_end :
            z =
              GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex t) ht := by
          calc
            z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
              hrv_eq.symm
            _ = GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex t) ht :=
              GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
                ht hrt
        exact hzclean.2.2 hz_end
    have hne :
        Not ((c = s ∧ y = t) ∨ (c = t ∧ y = s)) := by
      intro hsame
      rcases hsame with hsame | hsame
      · exact hsc hsame.1.symm
      · exact htc hsame.1.symm
    exact Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hcy hst hne)
      hqv_internal (by simpa [hqv_rv] using hrv_internal)

theorem strictSubdivisionModel_collapseEdge_branch_attachment_direct_arms_internally_disjoint
    {V : Type u}
    {G : SimpleGraph V}
    {a b root other : V}
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    {v₁ v₂ end₁ end₂ : V}
    {q₁ : G.Walk v₁ end₁}
    {q₂ : G.Walk v₂ end₂}
    (hrootv₁ : G.Adj root v₁)
    (hrootv₂ : G.Adj root v₂)
    (hq₁_outside :
      forall z : V, z ∈ q₁.support -> z ∉ ({a, b} : Set V))
    (hdisj :
      Disjoint {z : V | z ∈ q₁.support} {z : V | z ∈ q₂.support}) :
    Disjoint
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv₁) q₁))
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv₂) q₂)) := by
  classical
  refine
    Walk.branchAttachmentPath_internal_disjoint_of_left_direct
      hroot_other hrootv₁ (Or.inl hrootv₂) ?_ hdisj
  intro z hz hz_pair
  rcases hz_pair with hzroot | hzother
  · subst z
    exact hq₁_outside root hz hroot_pair
  · subst z
    exact hq₁_outside other hz hother_pair

theorem strictSubdivisionModel_collapseEdge_branch_attachment_pair_direct_arms_internally_disjoint
    {V : Type u}
    {G : SimpleGraph V}
    {a b root other : V}
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    {v₁ v₂ end₁ end₂ : V}
    {q₁ : G.Walk v₁ end₁}
    {q₂ : G.Walk v₂ end₂}
    (hside₁ : G.Adj root v₁ ∨ G.Adj other v₁)
    (hside₂ : G.Adj root v₂ ∨ G.Adj other v₂)
    (hdirect : G.Adj root v₁ ∨ G.Adj root v₂)
    (hq₁_outside :
      forall z : V, z ∈ q₁.support -> z ∉ ({a, b} : Set V))
    (hq₂_outside :
      forall z : V, z ∈ q₂.support -> z ∉ ({a, b} : Set V))
    (hdisj :
      Disjoint {z : V | z ∈ q₁.support} {z : V | z ∈ q₂.support}) :
    Disjoint
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other hside₁ q₁))
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other hside₂ q₂)) := by
  classical
  rcases hdirect with hrootv₁ | hrootv₂
  · refine
      Walk.branchAttachmentPath_internal_disjoint_of_left_direct
        hroot_other hrootv₁ hside₂ ?_ hdisj
    intro z hz hz_pair
    rcases hz_pair with hzroot | hzother
    · subst z
      exact hq₁_outside root hz hroot_pair
    · subst z
      exact hq₁_outside other hz hother_pair
  · refine
      Walk.branchAttachmentPath_internal_disjoint_of_right_direct
        hroot_other hside₁ hrootv₂ ?_ hdisj
    intro z hz hz_pair
    rcases hz_pair with hzroot | hzother
    · subst z
      exact hq₂_outside root hz hroot_pair
    · subst z
      exact hq₂_outside other hz hother_pair

theorem collapseEdge_pair_side_to_root_other
    {V : Type u} {G : SimpleGraph V}
    {a b root other v : V}
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (hside : G.Adj a v ∨ G.Adj b v) :
    G.Adj root v ∨ G.Adj other v := by
  rcases hroot_pair with hroot | hroot <;>
    rcases hother_pair with hother | hother
  · subst root
    subst other
    exact False.elim (G.loopless.irrefl a hroot_other)
  · subst root
    subst other
    exact hside
  · subst root
    subst other
    exact hside.symm
  · subst root
    subst other
    exact False.elim (G.loopless.irrefl b hroot_other)

theorem fin3_bool_pair_majority (f : Fin 3 -> Bool) :
    Exists fun r : Bool =>
      forall i j : Fin 3, i ≠ j -> f i = r ∨ f j = r := by
  by_cases h0 : f 0 = true
  · by_cases h1 : f 1 = true
    · refine ⟨true, ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · by_cases h2 : f 2 = true
      · refine ⟨true, ?_⟩
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · refine ⟨false, ?_⟩
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
  · by_cases h1 : f 1 = true
    · by_cases h2 : f 2 = true
      · refine ⟨true, ?_⟩
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · refine ⟨false, ?_⟩
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
    · refine ⟨false, ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all

theorem fin4_bool_pair_majority_or_two_two (f : Fin 4 -> Bool) :
    (Exists fun r : Bool =>
      forall i j : Fin 4, i ≠ j -> f i = r ∨ f j = r) ∨
      Exists fun i : Fin 4 =>
        Exists fun j : Fin 4 =>
          Exists fun k : Fin 4 =>
            Exists fun l : Fin 4 =>
              i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
                f i = true ∧ f j = true ∧ f k = false ∧ f l = false := by
  by_cases h0 : f 0 = true <;>
    by_cases h1 : f 1 = true <;>
    by_cases h2 : f 2 = true <;>
    by_cases h3 : f 3 = true
  all_goals
    solve
    | left
      refine ⟨true, ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    | left
      refine ⟨false, ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    | right
      refine ⟨0, 1, 2, 3, ?_⟩
      simp_all
    | right
      refine ⟨0, 2, 1, 3, ?_⟩
      simp_all
    | right
      refine ⟨0, 3, 1, 2, ?_⟩
      simp_all
    | right
      refine ⟨1, 2, 0, 3, ?_⟩
      simp_all
    | right
      refine ⟨1, 3, 0, 2, ?_⟩
      simp_all
    | right
      refine ⟨2, 3, 0, 1, ?_⟩
      simp_all

theorem K33Graph.exists_bool_pair_majority
    (c : K33Vertex) (side : K33Vertex -> Bool) :
    Exists fun r : Bool =>
      forall {y z : K33Vertex},
        K33Graph.Adj c y -> K33Graph.Adj c z -> y ≠ z ->
          side y = r ∨ side z = r := by
  cases c with
  | inl ci =>
      let f : Fin 3 -> Bool := fun i => side (Sum.inr i)
      rcases fin3_bool_pair_majority f with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      intro y z hcy hcz hyz
      cases y with
      | inl yi =>
          simp [K33Graph] at hcy
      | inr yi =>
          cases z with
          | inl zi =>
              simp [K33Graph] at hcz
          | inr zi =>
              have hyz_fin : yi ≠ zi := by
                intro h
                exact hyz (by simp [h])
              simpa [f] using hr yi zi hyz_fin
  | inr ci =>
      let f : Fin 3 -> Bool := fun i => side (Sum.inl i)
      rcases fin3_bool_pair_majority f with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      intro y z hcy hcz hyz
      cases y with
      | inl yi =>
          cases z with
          | inl zi =>
              have hyz_fin : yi ≠ zi := by
                intro h
                exact hyz (by simp [h])
              simpa [f] using hr yi zi hyz_fin
          | inr zi =>
              simp [K33Graph] at hcz
      | inr yi =>
          simp [K33Graph] at hcy

noncomputable def k5TieK33Branch
    {V : Type u} (a b p q r s : V) : K33Vertex -> V
  | Sum.inl 0 => a
  | Sum.inl 1 => r
  | Sum.inl 2 => s
  | Sum.inr 0 => b
  | Sum.inr 1 => p
  | Sum.inr 2 => q
end FourColor

end Schematic.Math.GraphTheory
