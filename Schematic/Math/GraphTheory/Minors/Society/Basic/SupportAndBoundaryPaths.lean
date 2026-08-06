import Schematic.Math.GraphTheory.Minors.Society.Basic.OuterTailLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

theorem Tripod.rim_support_subset_graph_support
    {S : GeneralSociety V} (T : S.Tripod) (i : Fin 3) :
    {z : V | z ∈ (T.rim i).support} ⊆ S.graph.support := by
  intro z hz
  exact SimpleGraph.mem_support_of_mem_walk_support (T.rim i)
    (SimpleGraph.Walk.not_nil_of_ne (p := T.rim i) T.left_ne_right)
    hz

theorem Tripod.leg_support_subset_graph_support
    {S : GeneralSociety V} (T : S.Tripod) (i : Fin 3) :
    {z : V | z ∈ (T.leg i).support} ⊆ S.graph.support := by
  intro z hz
  by_cases hnil : (T.leg i).Nil
  · have hz_attach : z = T.attach i := by
      have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hnil
      simpa [hsupport] using hz
    subst z
    exact SimpleGraph.mem_support_of_mem_walk_support (T.rim i)
      (SimpleGraph.Walk.not_nil_of_ne (p := T.rim i) T.left_ne_right)
      (T.attach_mem_rim i).1
  · exact SimpleGraph.mem_support_of_mem_walk_support (T.leg i) hnil hz

/-- A path between two distinct boundary vertices contains a boundary-to-boundary
subpath whose internal vertices avoid the society boundary.

This is the local normalization used in the source proof before invoking GM IX
`(2.1)`: global preconnectedness is unnecessary once any boundary-to-boundary
path has been found. -/
theorem exists_boundary_clean_subpath_of_path [DecidableEq V]
    (S : GeneralSociety V)
    {s t : V}
    (hs : s ∈ S.boundarySet)
    (ht : t ∈ S.boundarySet)
    (hst : s ≠ t)
    {q : S.graph.Walk s t}
    (hq_path : q.IsPath) :
    Exists fun s' : V =>
      Exists fun t' : V =>
        s' ∈ S.boundarySet ∧ t' ∈ S.boundarySet ∧ s' ≠ t' ∧
          Exists fun r : S.graph.Walk s' t' =>
            r.IsPath ∧ Walk.InternalVertices r ∩ S.boundarySet = ∅ := by
  classical
  let Q : Nat -> Prop := fun n =>
    forall {s t : V},
      s ∈ S.boundarySet ->
        t ∈ S.boundarySet ->
          s ≠ t ->
            forall {q : S.graph.Walk s t},
              q.IsPath ->
                q.length = n ->
                  Exists fun s' : V =>
                    Exists fun t' : V =>
                      s' ∈ S.boundarySet ∧
                        t' ∈ S.boundarySet ∧ s' ≠ t' ∧
                          Exists fun r : S.graph.Walk s' t' =>
                            r.IsPath ∧
                              Walk.InternalVertices r ∩ S.boundarySet = ∅
  have hQ : forall n : Nat, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s t hs ht hst q hq_path hlen
      by_cases hclean :
          Walk.InternalVertices q ∩ S.boundarySet = ∅
      · exact ⟨s, t, hs, ht, hst, q, hq_path, hclean⟩
      · have hnonempty :
            (Walk.InternalVertices q ∩ S.boundarySet).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          exact hclean
        rcases hnonempty with ⟨x, hx⟩
        have hx_internal : x ∈ Walk.InternalVertices q := hx.1
        have hx_boundary : x ∈ S.boundarySet := hx.2
        have hx_support : x ∈ q.support := hx_internal.1
        have hxs : x ≠ s := hx_internal.2.1
        have hxt : x ≠ t := hx_internal.2.2
        let q' : S.graph.Walk s x := q.takeUntil x hx_support
        have hq'_path : q'.IsPath := by
          simpa [q'] using hq_path.takeUntil hx_support
        have hlt : q'.length < n := by
          have htake : q'.length < q.length := by
            simpa [q'] using
              SimpleGraph.Walk.length_takeUntil_lt hx_support hxt
          omega
        exact ih q'.length hlt hs hx_boundary hxs.symm hq'_path rfl
  exact hQ q.length hs ht hst hq_path rfl

end GeneralSociety

end Schematic.Math.GraphTheory
