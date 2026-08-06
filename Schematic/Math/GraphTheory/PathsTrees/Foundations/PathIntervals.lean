import Schematic.Math.GraphTheory.PathsTrees.Foundations.InternalVertices

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
theorem Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
    [DecidableEq V]
    {u v w z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support)
    (hz_take : z ∈ (p.takeUntil w hw).support)
    (hz_drop : z ∈ (p.dropUntil w hw).support) :
    z = w := by
  by_contra hzw
  have hp_split :
      ((p.takeUntil w hw).append (p.dropUntil w hw)).IsPath := by
    rwa [SimpleGraph.Walk.take_spec p hw]
  exact
    (hp_split.ne_of_mem_support_of_append hzw hz_take hz_drop) rfl

theorem Walk.IsPath.start_not_mem_dropUntil_support_of_ne
    [DecidableEq V]
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ p.support)
    (hzu : z ≠ u) :
    u ∉ (p.dropUntil z hz).support := by
  intro hu_drop
  have hu_take : u ∈ (p.takeUntil z hz).support :=
    (p.takeUntil z hz).start_mem_support
  have hsplit :
      u = z :=
    Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      hp hz hu_take hu_drop
  exact hzu hsplit.symm

theorem Walk.IsPath.dropUntil_internalVertices_disjoint_of_internalVertices_disjoint
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (B : Set V)
    (hclean : Walk.InternalVertices p ∩ B = ∅) :
    Walk.InternalVertices (p.dropUntil x hx) ∩ B = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hzInternal : z ∈ Walk.InternalVertices (p.dropUntil x hx) := hz.1
  have hzB : z ∈ B := hz.2
  have hzSupport : z ∈ p.support :=
    SimpleGraph.Walk.support_dropUntil_subset p hx hzInternal.1
  have hz_ne_start : z ≠ u := by
    intro hzu
    by_cases hxu : x = u
    · exact hzInternal.2.1 (by simpa [hxu] using hzu)
    · have hu_not :
          u ∉ (p.dropUntil x hx).support :=
        Walk.IsPath.start_not_mem_dropUntil_support_of_ne hp hx hxu
      exact hu_not (by simpa [hzu] using hzInternal.1)
  have hz_ne_end : z ≠ v := by
    intro hzv
    exact hzInternal.2.2 (by simp [hzv])
  have hzP : z ∈ Walk.InternalVertices p :=
    ⟨hzSupport, hz_ne_start, hz_ne_end⟩
  have hnot : z ∉ Walk.InternalVertices p ∩ B := by
    rw [hclean]
    simp
  exact hnot ⟨hzP, hzB⟩

theorem Walk.IsPath.takeUntil_boundary_subset_start_or_cut
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (B : Set V)
    (hclean : Walk.InternalVertices p ∩ B = ∅) :
    forall z : V,
      z ∈ (p.takeUntil x hx).support -> z ∈ B -> z = u ∨ z = x := by
  intro z hz_take hzB
  have hz_support : z ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hx hz_take
  by_cases hzu : z = u
  · exact Or.inl hzu
  · by_cases hzv : z = v
    · right
      by_cases hxv : x = v
      · exact hzv.trans hxv.symm
      · have hv_not :
            v ∉ (p.takeUntil x hx).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            hp hx (by exact fun h => hxv h.symm)
        exact False.elim (hv_not (by simpa [hzv] using hz_take))
    · have hzInternal : z ∈ Walk.InternalVertices p :=
        ⟨hz_support, hzu, hzv⟩
      have hnot : z ∉ Walk.InternalVertices p ∩ B := by
        rw [hclean]
        simp
      exact False.elim (hnot ⟨hzInternal, hzB⟩)

theorem Walk.IsPath.dropUntil_boundary_subset_cut_or_end
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (B : Set V)
    (hclean : Walk.InternalVertices p ∩ B = ∅) :
    forall z : V,
      z ∈ (p.dropUntil x hx).support -> z ∈ B -> z = x ∨ z = v := by
  intro z hz_drop hzB
  have hz_support : z ∈ p.support :=
    SimpleGraph.Walk.support_dropUntil_subset p hx hz_drop
  by_cases hzu : z = u
  · left
    by_cases hxu : x = u
    · exact hzu.trans hxu.symm
    · have hu_not :
          u ∉ (p.dropUntil x hx).support :=
        Walk.IsPath.start_not_mem_dropUntil_support_of_ne hp hx hxu
      exact False.elim (hu_not (by simpa [hzu] using hz_drop))
  · by_cases hzv : z = v
    · exact Or.inr hzv
    · have hzInternal : z ∈ Walk.InternalVertices p :=
        ⟨hz_support, hzu, hzv⟩
      have hnot : z ∉ Walk.InternalVertices p ∩ B := by
        rw [hclean]
        simp
      exact False.elim (hnot ⟨hzInternal, hzB⟩)

theorem Walk.edge_append_dropUntil_internalVertices_subset
    [DecidableEq V]
    {a b u x : V}
    {p : G.Walk a b}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hx_ne_start : x ≠ a)
    (hux : G.Adj u x) :
    Walk.InternalVertices (hux.toWalk.append (p.dropUntil x hx)) ⊆
      Walk.InternalVertices p := by
  intro z hz
  have hz_support' :=
    Walk.edge_append_support_subset_insert (q := p.dropUntil x hx) hux hz.1
  rcases hz_support' with rfl | hz_drop
  · exact False.elim (hz.2.1 rfl)
  · refine ⟨?_, ?_, ?_⟩
    · exact SimpleGraph.Walk.support_dropUntil_subset p hx hz_drop
    · intro hza
      have ha_not_drop : a ∉ (p.dropUntil x hx).support :=
        Walk.IsPath.start_not_mem_dropUntil_support_of_ne hp hx hx_ne_start
      exact ha_not_drop (by simpa [hza] using hz_drop)
    · exact hz.2.2

theorem Walk.mem_support_takeUntil_of_idxOf_le
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hidx : p.support.idxOf y <= p.support.idxOf x) :
    y ∈ (p.takeUntil x hx).support := by
  rw [SimpleGraph.Walk.takeUntil_eq_take]
  simp only [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.take_support_eq_support_take_succ]
  rw [List.mem_take_iff_idxOf_lt hy]
  omega

theorem Walk.mem_support_dropUntil_of_idxOf_le
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hidx : p.support.idxOf x <= p.support.idxOf y) :
    y ∈ (p.dropUntil x hx).support := by
  rw [SimpleGraph.Walk.dropUntil_eq_drop]
  simp only [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min]
  have hxidx_le_length : p.support.idxOf x <= p.length := by
    have hxlt := List.idxOf_lt_length_of_mem hx
    rw [SimpleGraph.Walk.length_support] at hxlt
    omega
  rw [Nat.min_eq_left hxidx_le_length]
  let n := p.support.idxOf x
  let m := p.support.idxOf y - p.support.idxOf x
  have hyidx_lt : p.support.idxOf y < p.support.length :=
    List.idxOf_lt_length_of_mem hy
  have hm_length : m < (p.support.drop n).length := by
    rw [List.length_drop]
    omega
  have hnm : n + m = p.support.idxOf y := by
    simp [n, m]
    omega
  have hget_idx : p.support[n + m] = y := by
    simp [hnm]
  have hget : (p.support.drop n)[m] = y := by
    rw [List.getElem_drop]
    exact hget_idx
  exact hget ▸ List.getElem_mem hm_length

theorem Walk.idxOf_le_of_mem_takeUntil
    [DecidableEq V]
    {u v x z : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hz : z ∈ (p.takeUntil x hx).support) :
    p.support.idxOf z <= p.support.idxOf x := by
  rw [SimpleGraph.Walk.takeUntil_eq_take] at hz
  simp only [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
  have hz_p : z ∈ p.support := List.mem_of_mem_take hz
  have hlt := (List.mem_take_iff_idxOf_lt hz_p).mp hz
  omega

theorem Walk.idxOf_le_of_mem_dropUntil
    [DecidableEq V]
    {u v x z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hz : z ∈ (p.dropUntil x hx).support) :
    p.support.idxOf x <= p.support.idxOf z := by
  rw [SimpleGraph.Walk.dropUntil_eq_drop] at hz
  simp only [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min] at hz
  have hxidx_le_length : p.support.idxOf x <= p.length := by
    have hxlt := List.idxOf_lt_length_of_mem hx
    rw [SimpleGraph.Walk.length_support] at hxlt
    omega
  rw [Nat.min_eq_left hxidx_le_length] at hz
  exact list_le_idxOf_of_mem_drop_of_nodup hp.support_nodup hz

theorem Walk.idxOf_start_support
    [DecidableEq V]
    {u v : V}
    (p : G.Walk u v) :
    p.support.idxOf u = 0 := by
  induction p with
  | nil => simp [SimpleGraph.Walk.support]
  | cons h p ih => simp [SimpleGraph.Walk.support]

theorem Walk.idxOf_pos_of_mem_support_ne_start
    [DecidableEq V]
    {u v y : V}
    {p : G.Walk u v}
    (hy : y ∈ p.support)
    (hyu : y ≠ u) :
    0 < p.support.idxOf y := by
  have hidx_ne : p.support.idxOf y ≠ 0 := by
    intro hidx_zero
    have hstart : p.support.idxOf u = 0 := Walk.idxOf_start_support p
    have hidx_eq : p.support.idxOf y = p.support.idxOf u := by
      rw [hidx_zero, hstart]
    exact hyu ((List.idxOf_inj hy).mp hidx_eq)
  omega

theorem Walk.IsPath.idxOf_lt_end_of_mem_support_ne_end
    [DecidableEq V]
    {u v y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hy : y ∈ p.support)
    (hyv : y ≠ v) :
    p.support.idxOf y < p.support.idxOf v := by
  have hy_drop : y ∈ p.support.dropLast := by
    refine List.mem_dropLast_of_mem_of_ne_getLast hy ?_
    intro hy_last
    exact hyv (by
      simpa [SimpleGraph.Walk.getLast_support] using hy_last)
  have hsucc : p.support.idxOf y + 1 < p.support.length :=
    List.succ_idxOf_lt_length_of_mem_dropLast hy_drop
  have hv_last_not_drop :
      p.support.getLast (SimpleGraph.Walk.support_ne_nil p) ∉
        p.support.dropLast := by
    have hsupport_eq :
        p.support.dropLast ++
            [p.support.getLast (SimpleGraph.Walk.support_ne_nil p)] =
          p.support :=
      List.dropLast_append_getLast (SimpleGraph.Walk.support_ne_nil p)
    have hnodup_append :
        (p.support.dropLast ++
            [p.support.getLast (SimpleGraph.Walk.support_ne_nil p)]).Nodup := by
      simpa [hsupport_eq] using hp.support_nodup
    have hdis := List.disjoint_of_nodup_append hnodup_append
    intro hlast_drop
    exact hdis hlast_drop (by simp)
  have hv_not_drop : v ∉ p.support.dropLast := by
    intro hv_drop
    exact hv_last_not_drop (by
      simpa [SimpleGraph.Walk.getLast_support] using hv_drop)
  have hv_idx : p.support.idxOf v = p.support.length - 1 := by
    simpa [SimpleGraph.Walk.getLast_support] using
      List.idxOf_getLast (SimpleGraph.Walk.support_ne_nil p) hv_last_not_drop
  omega

theorem Walk.IsPath.penultimate_ne_start_of_length_gt_one
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hlen : 1 < p.length) :
    p.penultimate ≠ u := by
  have hnot_nil : ¬ p.Nil := by
    intro hnil
    cases hnil
    simp at hlen
  have hidx_bound : p.length - 1 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hidx_pen :
      p.support.idxOf p.penultimate = p.length - 1 := by
    have hget :
        p.support[p.length - 1] = p.penultimate :=
      SimpleGraph.Walk.support_getElem_length_sub_one_eq_penultimate
        (p := p)
    rw [← hget]
    exact hp.support_nodup.idxOf_getElem (p.length - 1) hidx_bound
  intro hpen
  have hidx_start : p.support.idxOf u = 0 :=
    Walk.idxOf_start_support p
  rw [hpen, hidx_start] at hidx_pen
  omega

theorem Walk.length_dropUntil_lt_of_mem_support_ne_start
    [DecidableEq V]
    {u v y : V}
    {p : G.Walk u v}
    (hy : y ∈ p.support)
    (hyu : y ≠ u) :
    (p.dropUntil y hy).length < p.length := by
  rw [SimpleGraph.Walk.length_dropUntil]
  have hyidx_lt : p.support.idxOf y < p.support.length :=
    List.idxOf_lt_length_of_mem hy
  rw [SimpleGraph.Walk.length_support] at hyidx_lt
  have hidx_pos : 0 < p.support.idxOf y := by
    have hidx_ne : p.support.idxOf y ≠ 0 := by
      intro hidx_zero
      have hstart : p.support.idxOf u = 0 := Walk.idxOf_start_support p
      have hidx_eq : p.support.idxOf y = p.support.idxOf u := by
        rw [hidx_zero, hstart]
      exact hyu ((List.idxOf_inj hy).mp hidx_eq)
    omega
  omega

theorem Walk.exists_between_support_of_idx_gap
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hy : y ∈ p.support)
    (hgap : p.support.idxOf x + 1 < p.support.idxOf y) :
    Exists fun z : V =>
      z ∈ p.support ∧
        p.support.idxOf x < p.support.idxOf z ∧
          p.support.idxOf z < p.support.idxOf y ∧ z ≠ u := by
  let n := p.support.idxOf x + 1
  have hn_len : n < p.support.length := by
    have hy_len := List.idxOf_lt_length_of_mem hy
    omega
  let z : V := p.support[n]
  have hz_mem : z ∈ p.support := List.getElem_mem hn_len
  have hidx_z : p.support.idxOf z = n := by
    exact hp.support_nodup.idxOf_getElem n hn_len
  refine ⟨z, hz_mem, ?_, ?_, ?_⟩
  · simp [z, n, hidx_z]
  · simp [z, n, hidx_z]
    omega
  · intro hzu
    have hstart : p.support.idxOf u = 0 := Walk.idxOf_start_support p
    have hn0 : n = 0 := by
      rw [← hidx_z, hzu, hstart]
    omega

theorem Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hidx : p.support.idxOf x < p.support.idxOf y) :
    Disjoint
      {z : V | z ∈ (p.takeUntil x hx).support}
      {z : V | z ∈ (p.dropUntil y hy).support} := by
  rw [Set.disjoint_left]
  intro z hz_take hz_drop
  have hz_le_x := Walk.idxOf_le_of_mem_takeUntil hx hz_take
  have hy_le_z := Walk.idxOf_le_of_mem_dropUntil hp hy hz_drop
  omega

theorem Walk.not_mem_takeUntil_of_idxOf_lt
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hidx : p.support.idxOf x < p.support.idxOf y) :
    y ∉ (p.takeUntil x hx).support := by
  intro hy_take
  have hy_le_x := Walk.idxOf_le_of_mem_takeUntil hx hy_take
  omega

theorem Walk.IsPath.earlier_not_mem_dropUntil_of_idx_lt
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hy : y ∈ p.support)
    (hidx : p.support.idxOf x < p.support.idxOf y) :
    x ∉ (p.dropUntil y hy).support := by
  intro hx_drop
  have hy_le_x := Walk.idxOf_le_of_mem_dropUntil hp hy hx_drop
  omega

theorem Walk.IsPath.exists_takeUntil_first_mem
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (A : Set V)
    (hend : v ∈ A) :
    Exists fun x : V =>
      Exists fun hx : x ∈ p.support =>
        x ∈ A ∧
          forall z : V, z ∈ (p.takeUntil x hx).support -> z ∈ A -> z = x := by
  classical
  let l := p.support
  let P : Nat -> Prop := fun n =>
    Exists fun h : n < l.length => l[n] ∈ A
  have hP : Exists P := by
    have hv : v ∈ l := by
      change v ∈ p.support
      exact p.end_mem_support
    have hlt : l.idxOf v < l.length :=
      List.idxOf_lt_length_of_mem hv
    refine ⟨l.idxOf v, hlt, ?_⟩
    have hget : l[l.idxOf v] = v :=
      List.getElem_idxOf hlt
    simpa [P, hget] using hend
  let n := Nat.find hP
  obtain ⟨hn_len, hnA⟩ : P n := Nat.find_spec hP
  let x : V := l[n]
  have hx_support : x ∈ p.support := by
    dsimp [x, l]
    exact List.getElem_mem hn_len
  have hx_idx : p.support.idxOf x = n := by
    dsimp [x, l]
    exact hp.support_nodup.idxOf_getElem n hn_len
  have hxA : x ∈ A := by
    simpa [x, P] using hnA
  refine ⟨x, hx_support, hxA, ?_⟩
  intro z hz hzA
  have hz_support : z ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hx_support hz
  have hz_le_x : p.support.idxOf z <= p.support.idxOf x :=
    Walk.idxOf_le_of_mem_takeUntil hx_support hz
  have hzlt : p.support.idxOf z < p.support.length :=
    List.idxOf_lt_length_of_mem hz_support
  have hgetz : p.support[p.support.idxOf z] = z :=
    List.getElem_idxOf hzlt
  have hPz : P (p.support.idxOf z) := by
    refine ⟨by simpa [l] using hzlt, ?_⟩
    simpa [P, l, hgetz] using hzA
  have hn_le_z : n <= p.support.idxOf z :=
    Nat.find_min' hP hPz
  have hidx_eq : p.support.idxOf z = p.support.idxOf x := by
    rw [hx_idx]
    omega
  exact (List.idxOf_inj hz_support).mp hidx_eq

theorem Walk.IsPath.exists_reverse_takeUntil_first_mem
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (A : Set V)
    (hstart : u ∈ A) :
    Exists fun x : V =>
      Exists fun hx : x ∈ p.reverse.support =>
        x ∈ A ∧
          forall z : V,
            z ∈ (p.reverse.takeUntil x hx).support -> z ∈ A -> z = x := by
  exact Walk.IsPath.exists_takeUntil_first_mem
    (G := G) hp.reverse A (by simpa using hstart)

theorem Walk.IsPath.exists_suffix_from_last_mem
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (A : Set V)
    (hstart : u ∈ A) :
    Exists fun x : V =>
      Exists fun hx : x ∈ p.reverse.support =>
        x ∈ A ∧
          let q : G.Walk x v := (p.reverse.takeUntil x hx).reverse
          q.IsPath ∧
            (forall z : V, z ∈ q.support -> z ∈ A -> z = x) ∧
              forall z : V, z ∈ q.support -> z ∈ p.support := by
  obtain ⟨x, hx, hxA, hfirst⟩ :=
    Walk.IsPath.exists_reverse_takeUntil_first_mem
      (G := G) hp A hstart
  refine ⟨x, hx, hxA, ?_⟩
  dsimp
  constructor
  · exact (hp.reverse.takeUntil hx).reverse
  constructor
  · intro z hz hzA
    rw [SimpleGraph.Walk.support_reverse] at hz
    exact hfirst z (List.mem_reverse.mp hz) hzA
  · intro z hz
    rw [SimpleGraph.Walk.support_reverse] at hz
    have hzrev : z ∈ p.reverse.support :=
      SimpleGraph.Walk.support_takeUntil_subset p.reverse hx
        (List.mem_reverse.mp hz)
    rw [SimpleGraph.Walk.support_reverse] at hzrev
    exact List.mem_reverse.mp hzrev

theorem Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (A : Set V)
    (hstart : u ∈ A) :
    Exists fun x : V =>
      Exists fun hx : x ∈ p.support =>
        x ∈ A ∧
          let q : G.Walk x v := p.dropUntil x hx
          q.IsPath ∧
            (forall z : V, z ∈ q.support -> z ∈ A -> z = x) ∧
              (forall z : V, z ∈ q.support -> z ∈ p.support) ∧
                (forall z : V, z ∈ p.support ->
                  p.support.idxOf x <= p.support.idxOf z ->
                    z ∈ q.support) ∧
                forall z : V, z ∈ q.support ->
                  p.support.idxOf x <= p.support.idxOf z := by
  classical
  let l := p.support
  let P : Nat -> Prop := fun n =>
    Exists fun h : n < l.length => l[n] ∈ A
  have hlen_pos : 0 < l.length := by
    have hstart_support : u ∈ l := by
      simp [l]
    exact List.length_pos_of_mem hstart_support
  have hP0 : P 0 := by
    refine ⟨hlen_pos, ?_⟩
    have hget0 : l[0] = u := by
      dsimp [l]
      simp
    rw [hget0]
    exact hstart
  let n := Nat.findGreatest P (l.length - 1)
  have hnP : P n :=
    Nat.findGreatest_spec (P := P) (m := 0)
      (n := l.length - 1) (Nat.zero_le _) hP0
  obtain ⟨hn_len, hnA⟩ := hnP
  let x : V := l[n]
  have hx_support : x ∈ p.support := by
    dsimp [x, l]
    exact List.getElem_mem hn_len
  have hx_idx : p.support.idxOf x = n := by
    dsimp [x, l]
    exact hp.support_nodup.idxOf_getElem n hn_len
  have hxA : x ∈ A := by
    simpa [x, P] using hnA
  refine ⟨x, hx_support, hxA, ?_⟩
  dsimp
  constructor
  · exact hp.dropUntil hx_support
  constructor
  · intro z hz hzA
    have hz_support : z ∈ p.support :=
      SimpleGraph.Walk.support_dropUntil_subset p hx_support hz
    have hx_le_z : p.support.idxOf x <= p.support.idxOf z :=
      Walk.idxOf_le_of_mem_dropUntil hp hx_support hz
    have hzlt : p.support.idxOf z < p.support.length :=
      List.idxOf_lt_length_of_mem hz_support
    have hz_bound : p.support.idxOf z <= l.length - 1 := by
      have hzlt_l : p.support.idxOf z < l.length := by
        simpa [l] using hzlt
      omega
    have hzP : P (p.support.idxOf z) := by
      refine ⟨by simpa [l] using hzlt, ?_⟩
      have hgetz : l[p.support.idxOf z] = z := by
        dsimp [l]
        exact List.getElem_idxOf hzlt
      simpa [P, hgetz] using hzA
    have hz_le_n : p.support.idxOf z <= n := by
      by_contra hnot
      have hn_lt_z : n < p.support.idxOf z := by omega
      exact
        (Nat.findGreatest_is_greatest (P := P) (n := l.length - 1)
          hn_lt_z hz_bound) hzP
    have hn_le_z : n <= p.support.idxOf z := by
      simpa [hx_idx] using hx_le_z
    have hidx_eq : p.support.idxOf z = p.support.idxOf x := by
      rw [hx_idx]
      omega
    exact (List.idxOf_inj hz_support).mp hidx_eq
  constructor
  · intro z hz
    exact SimpleGraph.Walk.support_dropUntil_subset p hx_support hz
  constructor
  · intro z hz hidx
    exact Walk.mem_support_dropUntil_of_idxOf_le hx_support hz hidx
  · intro z hz
    exact Walk.idxOf_le_of_mem_dropUntil hp hx_support hz

theorem Walk.IsPath.exists_takeUntil_first_mem_left_or_right
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (A B : Set V)
    (hdisjoint : Disjoint A B)
    (hend : v ∈ A ∪ B) :
    (Exists fun x : V =>
      Exists fun hx : x ∈ p.support =>
        x ∈ A ∧
          forall z : V, z ∈ (p.takeUntil x hx).support -> z ∉ B) ∨
      (Exists fun x : V =>
        Exists fun hx : x ∈ p.support =>
          x ∈ B ∧
            forall z : V, z ∈ (p.takeUntil x hx).support -> z ∉ A) := by
  classical
  let l := p.support
  let P : Nat -> Prop := fun n =>
    Exists fun h : n < l.length => l[n] ∈ A ∪ B
  have hP : Exists P := by
    have hv : v ∈ l := by
      change v ∈ p.support
      exact p.end_mem_support
    have hlt : l.idxOf v < l.length :=
      List.idxOf_lt_length_of_mem hv
    refine ⟨l.idxOf v, hlt, ?_⟩
    have hget : l[l.idxOf v] = v :=
      List.getElem_idxOf hlt
    simpa [P, hget] using hend
  let n := Nat.find hP
  obtain ⟨hn_len, hnAB⟩ : P n := Nat.find_spec hP
  let x : V := l[n]
  have hx_support : x ∈ p.support := by
    dsimp [x, l]
    exact List.getElem_mem hn_len
  have hx_idx : p.support.idxOf x = n := by
    dsimp [x, l]
    exact hp.support_nodup.idxOf_getElem n hn_len
  have hxAB : x ∈ A ∪ B := by
    simpa [x, P] using hnAB
  have hfirst :
      forall z : V,
        z ∈ (p.takeUntil x hx_support).support ->
          z ∈ A ∪ B -> z = x := by
    intro z hz hzAB
    have hz_support : z ∈ p.support :=
      SimpleGraph.Walk.support_takeUntil_subset p hx_support hz
    have hz_le_x : p.support.idxOf z <= p.support.idxOf x :=
      Walk.idxOf_le_of_mem_takeUntil hx_support hz
    have hzlt : p.support.idxOf z < p.support.length :=
      List.idxOf_lt_length_of_mem hz_support
    have hgetz : p.support[p.support.idxOf z] = z :=
      List.getElem_idxOf hzlt
    have hPz : P (p.support.idxOf z) := by
      refine ⟨by simpa [l] using hzlt, ?_⟩
      simpa [P, l, hgetz] using hzAB
    have hn_le_z : n <= p.support.idxOf z :=
      Nat.find_min' hP hPz
    have hidx_eq : p.support.idxOf z = p.support.idxOf x := by
      rw [hx_idx]
      omega
    exact (List.idxOf_inj hz_support).mp hidx_eq
  rcases hxAB with hxA | hxB
  · refine Or.inl ⟨x, hx_support, hxA, ?_⟩
    intro z hz hzB
    have hzx : z = x := hfirst z hz (Or.inr hzB)
    have hxB : x ∈ B := by
      simpa [hzx] using hzB
    exact Set.disjoint_left.mp hdisjoint hxA hxB
  · refine Or.inr ⟨x, hx_support, hxB, ?_⟩
    intro z hz hzA
    have hzx : z = x := hfirst z hz (Or.inl hzA)
    have hxA : x ∈ A := by
      simpa [hzx] using hzA
    exact Set.disjoint_left.mp hdisjoint hxA hxB


end Schematic.Math.GraphTheory
