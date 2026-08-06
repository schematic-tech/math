import Schematic.Math.GraphTheory.PathsTrees.Operations.SupportIntervals

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
theorem Subgraph.mapped_punctured_supports_disjoint
    {B : G.Subgraph}
    {a b c d root₁ root₂ : B.verts}
    (p : B.coe.Walk a b)
    (q : B.coe.Walk c d)
    (hdisjoint :
      Disjoint
        {z : B.verts | z ∈ p.support ∧ z ≠ root₁}
        {z : B.verts | z ∈ q.support ∧ z ≠ root₂}) :
    Disjoint
      {z : V | z ∈ (p.map B.hom).support ∧ z ≠ (root₁ : V)}
      {z : V | z ∈ (q.map B.hom).support ∧ z ≠ (root₂ : V)} := by
  rw [Set.disjoint_left]
  rintro z ⟨hzp, hzp_ne_root⟩ ⟨hzq, hzq_ne_root⟩
  rcases (Walk.mem_support_map_subgraph_hom_iff
    (H := B) p).mp hzp with ⟨zp, hzp_support, hzp_eq⟩
  rcases (Walk.mem_support_map_subgraph_hom_iff
    (H := B) q).mp hzq with ⟨zq, hzq_support, hzq_eq⟩
  have hzp_ne : zp ≠ root₁ := by
    intro h
    exact hzp_ne_root (by
      calc
        z = (zp : V) := hzp_eq.symm
        _ = (root₁ : V) := by rw [h])
  have hzq_ne : zq ≠ root₂ := by
    intro h
    exact hzq_ne_root (by
      calc
        z = (zq : V) := hzq_eq.symm
        _ = (root₂ : V) := by rw [h])
  have hzpzq : zp = zq := by
    apply Subtype.ext
    exact hzp_eq.trans hzq_eq.symm
  exact Set.disjoint_left.mp hdisjoint
    ⟨hzp_support, hzp_ne⟩
    ⟨by simpa [hzpzq] using hzq_support, by simpa [hzpzq] using hzq_ne⟩

theorem Subgraph.mapped_internalVertices_disjoint_punctured_support
    {B : G.Subgraph}
    {a b c d root : B.verts}
    (p : B.coe.Walk a b)
    (q : B.coe.Walk c d)
    (hdisjoint :
      Disjoint
        (Walk.InternalVertices p)
        {z : B.verts | z ∈ q.support ∧ z ≠ root}) :
    Disjoint
      (Walk.InternalVertices (p.map B.hom))
      {z : V | z ∈ (q.map B.hom).support ∧ z ≠ (root : V)} := by
  rw [Set.disjoint_left]
  rintro z hz_p ⟨hzq, hzq_ne_root⟩
  rcases (Walk.mem_internalVertices_map_subgraph_hom_iff
    (H := B) p).mp hz_p with ⟨zp, hzp_internal, hzp_eq⟩
  rcases (Walk.mem_support_map_subgraph_hom_iff
    (H := B) q).mp hzq with ⟨zq, hzq_support, hzq_eq⟩
  have hzq_ne : zq ≠ root := by
    intro h
    exact hzq_ne_root (by
      calc
        z = (zq : V) := hzq_eq.symm
        _ = (root : V) := by rw [h])
  have hzpzq : zp = zq := by
    apply Subtype.ext
    exact hzp_eq.trans hzq_eq.symm
  exact Set.disjoint_left.mp hdisjoint hzp_internal
    ⟨by simpa [← hzpzq] using hzq_support,
      by simpa [← hzpzq] using hzq_ne⟩

theorem Subgraph.mapped_punctured_support_disjoint_internalVertices
    {B : G.Subgraph}
    {a b c d root : B.verts}
    (p : B.coe.Walk a b)
    (q : B.coe.Walk c d)
    (hdisjoint :
      Disjoint
        {z : B.verts | z ∈ p.support ∧ z ≠ root}
        (Walk.InternalVertices q)) :
    Disjoint
      {z : V | z ∈ (p.map B.hom).support ∧ z ≠ (root : V)}
      (Walk.InternalVertices (q.map B.hom)) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzp, hzp_ne_root⟩ hz_q
  rcases (Walk.mem_support_map_subgraph_hom_iff
    (H := B) p).mp hzp with ⟨zp, hzp_support, hzp_eq⟩
  rcases (Walk.mem_internalVertices_map_subgraph_hom_iff
    (H := B) q).mp hz_q with ⟨zq, hzq_internal, hzq_eq⟩
  have hzp_ne : zp ≠ root := by
    intro h
    exact hzp_ne_root (by
      calc
        z = (zp : V) := hzp_eq.symm
        _ = (root : V) := by rw [h])
  have hzpzq : zp = zq := by
    apply Subtype.ext
    exact hzp_eq.trans hzq_eq.symm
  exact Set.disjoint_left.mp hdisjoint
    ⟨hzp_support, hzp_ne⟩
    (by simpa [hzpzq] using hzq_internal)

theorem Walk.IsPath.exists_subpath_between_of_idxOf_le
    [DecidableEq V]
    {u v a b : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (ha : a ∈ p.support)
    (hb : b ∈ p.support)
    (hab : p.support.idxOf a <= p.support.idxOf b) :
    Exists fun q : G.Walk a b => q.IsPath ∧ q.toSubgraph ≤ p.toSubgraph := by
  have hb_drop : b ∈ (p.dropUntil a ha).support :=
    Walk.mem_dropUntil_of_idxOf_le ha hb hab
  let q : G.Walk a b := (p.dropUntil a ha).takeUntil b hb_drop
  have hq_path : q.IsPath := by
    simpa [q] using (hp.dropUntil ha).takeUntil hb_drop
  have hq_le : q.toSubgraph ≤ p.toSubgraph := by
    exact le_trans
      (Walk.toSubgraph_takeUntil_le (p.dropUntil a ha) hb_drop)
      (Walk.toSubgraph_dropUntil_le p ha)
  exact ⟨q, hq_path, hq_le⟩

theorem Walk.IsPath.idxOf_fst_lt_idxOf_snd_of_mem_darts
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    {d : G.Dart}
    (hd : d ∈ p.darts) :
    p.support.idxOf d.fst < p.support.idxOf d.snd := by
  obtain ⟨m, hm, hget⟩ := List.getElem_of_mem hd
  have hm_len : m < p.length := by
    simpa [SimpleGraph.Walk.length_darts] using hm
  have hm_support : m < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hms_support : m + 1 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hfst_get : p.getVert m = d.fst := by
    have hdget := p.darts_getElem_eq_getVert m hm
    have hfst : (p.darts[m]'hm).fst = d.fst := by
      rw [hget]
    rw [hdget] at hfst
    exact hfst
  have hsnd_get : p.getVert (m + 1) = d.snd := by
    have hdget := p.darts_getElem_eq_getVert m hm
    have hsnd : (p.darts[m]'hm).snd = d.snd := by
      rw [hget]
    rw [hdget] at hsnd
    exact hsnd
  have hfst_support : p.support[m]'hm_support = d.fst := by
    rw [← p.getVert_eq_support_getElem (n := m) (by omega)]
    exact hfst_get
  have hsnd_support : p.support[m + 1]'hms_support = d.snd := by
    rw [← p.getVert_eq_support_getElem (n := m + 1) (by omega)]
    exact hsnd_get
  have hidx_fst : p.support.idxOf d.fst = m := by
    simpa [hfst_support] using
      hp.support_nodup.idxOf_getElem m hm_support
  have hidx_snd : p.support.idxOf d.snd = m + 1 := by
    simpa [hsnd_support] using
      hp.support_nodup.idxOf_getElem (m + 1) hms_support
  omega

theorem Separation.Walk.IsPath.support_subset_left_of_endpoint_separator_only
    [DecidableEq V]
    (S : Separation G)
    {a b : V}
    {p : G.Walk a b}
    (hp : p.IsPath)
    (ha_left : a ∈ S.left)
    (hsep_only :
      forall s : V, s ∈ S.separator -> s ∈ p.support -> s = b) :
    forall t : V, t ∈ p.support -> t ∈ S.left := by
  intro t ht
  by_contra ht_not_left
  let q : G.Walk a t := p.takeUntil t ht
  obtain ⟨d, hd_mem_q, hd_left, hd_not_left⟩ :=
    q.exists_boundary_dart S.left ha_left ht_not_left
  have hd_mem_p : d ∈ p.darts := by
    simpa [q] using p.darts_takeUntil_subset ht hd_mem_q
  have hd_snd_right : d.snd ∈ S.right :=
    S.mem_right_of_not_mem_left hd_not_left
  have hd_fst_right : d.fst ∈ S.right := by
    by_contra hd_fst_not_right
    exact S.no_cross hd_left hd_fst_not_right hd_snd_right hd_not_left d.2
  have hd_fst_sep : d.fst ∈ S.separator := ⟨hd_left, hd_fst_right⟩
  have hd_fst_support : d.fst ∈ p.support :=
    p.dart_fst_mem_support_of_mem_darts hd_mem_p
  have hd_fst_eq_b : d.fst = b :=
    hsep_only d.fst hd_fst_sep hd_fst_support
  have hd_fst_ne_b : d.fst ≠ b :=
    Walk.IsPath.dart_fst_ne_end_of_mem_darts hp hd_mem_p
  exact hd_fst_ne_b hd_fst_eq_b

theorem Separation.Walk.IsPath.support_subset_left_of_triple_endpoint
    [DecidableEq V]
    (S : Separation G)
    {a x y z : V}
    {p : G.Walk a x}
    (hp : p.IsPath)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (ha_left : a ∈ S.left)
    (hy_not_support : y ∉ p.support)
    (hz_not_support : z ∉ p.support) :
    forall t : V, t ∈ p.support -> t ∈ S.left := by
  exact
    Separation.Walk.IsPath.support_subset_left_of_endpoint_separator_only S
      hp ha_left (by
        intro s hs_sep hs_support
        have hs_cases : s = x ∨ s = y ∨ s = z := by
          have : s ∈ ({x, y, z} : Set V) := by
            simpa [hseparator] using hs_sep
          simpa [Set.mem_insert_iff] using this
        rcases hs_cases with rfl | rfl | rfl
        · rfl
        · exact False.elim (hy_not_support hs_support)
        · exact False.elim (hz_not_support hs_support))


/-!
Additional path/tree comparison lemmas imported from the main worktree to
support the split Near-Hajos proof.  They are reusable background facts, not
paper-specific statements.
-/

theorem Walk.exists_first_common_support
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v)
    (q : G.Walk a b)
    (hcommon : Exists fun z : V => z ∈ p.support ∧ z ∈ q.support) :
    Exists fun z : V =>
      Exists fun hzp : z ∈ p.support =>
        z ∈ q.support ∧
          forall t : V,
            t ∈ q.support ->
              t ∈ (p.takeUntil z hzp).support ->
                t = z := by
  classical
  let S : Finset V := q.support.toFinset
  have hS_nonempty : {x ∈ S | x ∈ p.support}.Nonempty := by
    rcases hcommon with ⟨z, hzp, hzq⟩
    exact ⟨z, by
      simp [S, hzq, hzp]⟩
  obtain ⟨z, hzS, hzp, hfirst⟩ :=
    SimpleGraph.Walk.exists_mem_support_forall_mem_support_imp_eq
      (p := p) S hS_nonempty
  refine ⟨z, hzp, ?_, ?_⟩
  · simpa [S] using hzS
  · intro t htq htprefix
    exact hfirst t (by simpa [S] using htq) htprefix


theorem Walk.exists_last_common_support
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v)
    (q : G.Walk a b)
    (hcommon : Exists fun z : V => z ∈ p.support ∧ z ∈ q.support) :
    Exists fun z : V =>
      Exists fun _hzp : z ∈ p.support =>
        Exists fun hzp_rev : z ∈ p.reverse.support =>
          z ∈ q.support ∧
            forall t : V,
              t ∈ q.support ->
                t ∈ (p.reverse.takeUntil z hzp_rev).support ->
                  t = z := by
  classical
  have hcommon_rev :
      Exists fun z : V => z ∈ p.reverse.support ∧ z ∈ q.support := by
    rcases hcommon with ⟨z, hzp, hzq⟩
    exact ⟨z, by simpa [SimpleGraph.Walk.support_reverse] using hzp, hzq⟩
  rcases Walk.exists_first_common_support p.reverse q hcommon_rev with
    ⟨z, hzp_rev, hzq, hfirst⟩
  have hzp : z ∈ p.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzp_rev
  exact ⟨z, hzp, hzp_rev, hzq, hfirst⟩


theorem Walk.last_common_reverse_takeUntil_punctured_disjoint_support
    [DecidableEq V]
    {u v a b z : V}
    {p : G.Walk u v}
    {q : G.Walk a b}
    (hzp_rev : z ∈ p.reverse.support)
    (hlast :
      forall t : V,
        t ∈ q.support ->
          t ∈ (p.reverse.takeUntil z hzp_rev).support ->
            t = z) :
    Disjoint
      {t : V | t ∈ (p.reverse.takeUntil z hzp_rev).support ∧ t ≠ z}
      {t : V | t ∈ q.support} := by
  rw [Set.disjoint_left]
  rintro t ⟨htprefix, ht_ne_z⟩ htq
  exact ht_ne_z (hlast t htq htprefix)


theorem List.idxOf_reverse_of_nodup [DecidableEq V]
    {l : List V}
    (hn : l.Nodup)
    {a : V}
    (ha : a ∈ l) :
    l.reverse.idxOf a = l.length - 1 - l.idxOf a := by
  let i : ℕ := l.length - 1 - l.idxOf a
  have hidx_lt : l.idxOf a < l.length := List.idxOf_lt_length_iff.mpr ha
  have hi_lt_rev : i < l.reverse.length := by
    simp [i]
    omega
  have hget : l.reverse[i] = a := by
    rw [List.getElem_reverse]
    have hcalc : l.length - 1 - i = l.idxOf a := by
      simp [i]
      omega
    simp [hcalc]
  have hnodup_rev : l.reverse.Nodup := by
    simpa [List.Nodup, eq_comm] using hn.reverse
  have hidx := hnodup_rev.idxOf_getElem i hi_lt_rev
  simpa [hget, i] using hidx



theorem Walk.IsPath.snd_dropUntil_ne_snd_reverse_dropUntil_of_internal
    [DecidableEq V]
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ Walk.InternalVertices p) :
    (p.dropUntil z hz.1).snd ≠
      (p.reverse.dropUntil z (by
        rw [SimpleGraph.Walk.support_reverse]
        exact List.mem_reverse.mpr hz.1)).snd := by
  classical
  let pR : G.Walk z v := p.dropUntil z hz.1
  have hzrev : z ∈ p.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hz.1
  let pL : G.Walk z u := p.reverse.dropUntil z hzrev
  have hpR_not_nil : ¬ pR.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pR) hz.2.2
  have hpL_not_nil : ¬ pL.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pL) hz.2.1
  have hsR_mem_drop : pR.snd ∈ pR.support :=
    List.mem_of_mem_tail (pR.snd_mem_tail_support hpR_not_nil)
  have hsL_mem_drop_rev : pL.snd ∈ pL.support :=
    List.mem_of_mem_tail (pL.snd_mem_tail_support hpL_not_nil)
  have hsR_mem_p : pR.snd ∈ p.support :=
    SimpleGraph.Walk.support_dropUntil_subset p hz.1 hsR_mem_drop
  have hsL_mem_prev : pL.snd ∈ p.reverse.support :=
    SimpleGraph.Walk.support_dropUntil_subset p.reverse hzrev hsL_mem_drop_rev
  have hsL_mem_p : pL.snd ∈ p.support := by
    rw [SimpleGraph.Walk.support_reverse] at hsL_mem_prev
    exact List.mem_reverse.mp hsL_mem_prev
  have hsR_ne_z : pR.snd ≠ z :=
    (pR.adj_snd hpR_not_nil).ne.symm
  have hsL_ne_z : pL.snd ≠ z :=
    (pL.adj_snd hpL_not_nil).ne.symm
  have hleR : p.support.idxOf z <= p.support.idxOf pR.snd :=
    Walk.IsPath.split_idxOf_le_of_mem_dropUntil hp hz.1 hsR_mem_drop
  have hltR : p.support.idxOf z < p.support.idxOf pR.snd := by
    exact lt_of_le_of_ne hleR (by
      intro hidx
      exact hsR_ne_z (((List.idxOf_inj hz.1).mp hidx).symm))
  have hleL_rev : p.reverse.support.idxOf z <= p.reverse.support.idxOf pL.snd :=
    Walk.IsPath.split_idxOf_le_of_mem_dropUntil hp.reverse hzrev
      hsL_mem_drop_rev
  have hidx_rev_z :
      p.reverse.support.idxOf z =
        p.support.length - 1 - p.support.idxOf z := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.idxOf_reverse_of_nodup hp.support_nodup hz.1
  have hidx_rev_s :
      p.reverse.support.idxOf pL.snd =
        p.support.length - 1 - p.support.idxOf pL.snd := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.idxOf_reverse_of_nodup hp.support_nodup hsL_mem_p
  have hleL : p.support.idxOf pL.snd <= p.support.idxOf z := by
    rw [hidx_rev_z, hidx_rev_s] at hleL_rev
    have hz_lt : p.support.idxOf z < p.support.length :=
      List.idxOf_lt_length_iff.mpr hz.1
    have hs_lt : p.support.idxOf pL.snd < p.support.length :=
      List.idxOf_lt_length_iff.mpr hsL_mem_p
    omega
  have hltL : p.support.idxOf pL.snd < p.support.idxOf z := by
    exact lt_of_le_of_ne hleL (by
      intro hidx
      exact hsL_ne_z ((List.idxOf_inj hsL_mem_p).mp hidx))
  intro heq
  have hidx_eq : p.support.idxOf pL.snd = p.support.idxOf pR.snd := by
    rw [heq]
  omega

theorem List.mem_reverse_take_of_nodup_imp_idx_le [DecidableEq V]
    {l : List V}
    (hn : l.Nodup)
    {x z : V}
    (hx : x ∈ l)
    (hz : z ∈ l)
    (hmem : x ∈ (l.reverse.take (l.reverse.idxOf z + 1)).reverse) :
    l.idxOf z <= l.idxOf x := by
  have hx_rev_take : x ∈ l.reverse.take (l.reverse.idxOf z + 1) := by
    simpa using List.mem_reverse.mp hmem
  have hx_rev : x ∈ l.reverse :=
    List.mem_of_mem_take hx_rev_take
  have hlt : l.reverse.idxOf x < l.reverse.idxOf z + 1 :=
    (List.mem_take_iff_idxOf_lt (by simpa using hx_rev)).mp hx_rev_take
  have hle_rev : l.reverse.idxOf x <= l.reverse.idxOf z := by
    omega
  rw [List.idxOf_reverse_of_nodup hn hx,
    List.idxOf_reverse_of_nodup hn hz] at hle_rev
  have hidxx_lt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  have hidxz_lt : l.idxOf z < l.length := List.idxOf_lt_length_iff.mpr hz
  omega


theorem List.eq_of_mem_take_and_reverse_take_of_nodup [DecidableEq V]
    {l : List V}
    (hn : l.Nodup)
    {x z : V}
    (hz : z ∈ l)
    (hx_take : x ∈ l.take (l.idxOf z + 1))
    (hx_rev_take : x ∈ (l.reverse.take (l.reverse.idxOf z + 1)).reverse) :
    x = z := by
  have hx : x ∈ l := List.mem_of_mem_take hx_take
  have hx_le_z : l.idxOf x <= l.idxOf z := by
    have hlt : l.idxOf x < l.idxOf z + 1 :=
      (List.mem_take_iff_idxOf_lt hx).mp hx_take
    omega
  have hz_le_x : l.idxOf z <= l.idxOf x :=
    List.mem_reverse_take_of_nodup_imp_idx_le hn hx hz hx_rev_take
  have hidx : l.idxOf x = l.idxOf z := le_antisymm hx_le_z hz_le_x
  exact (List.idxOf_inj hx).mp hidx


theorem List.idxOf_ge_of_mem_drop_of_nodup [DecidableEq V]
    {l : List V}
    (hn : l.Nodup)
    {x : V}
    {n : ℕ}
    (hx_drop : x ∈ l.drop n) :
    n <= l.idxOf x := by
  by_contra hnot
  have hlt : l.idxOf x < n := Nat.lt_of_not_ge hnot
  have hx : x ∈ l := List.mem_of_mem_drop hx_drop
  have hx_take : x ∈ l.take n :=
    (List.mem_take_iff_idxOf_lt hx).mpr hlt
  have hdisj : (l.take n).Disjoint (l.drop n) :=
    List.disjoint_take_drop hn le_rfl
  exact (List.disjoint_left.mp hdisj hx_take) hx_drop


theorem List.mem_reverse_take_of_nodup_of_idx_le [DecidableEq V]
    {l : List V}
    (hn : l.Nodup)
    {x z : V}
    (hx : x ∈ l)
    (hz : z ∈ l)
    (hle : l.idxOf z <= l.idxOf x) :
    x ∈ l.reverse.take (l.reverse.idxOf z + 1) := by
  have hx_rev : x ∈ l.reverse := by
    simpa using List.mem_reverse.mpr hx
  rw [List.mem_take_iff_idxOf_lt hx_rev]
  rw [List.idxOf_reverse_of_nodup hn hx,
    List.idxOf_reverse_of_nodup hn hz]
  have hx_lt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  have hz_lt : l.idxOf z < l.length := List.idxOf_lt_length_iff.mpr hz
  omega


theorem Walk.IsPath.eq_of_mem_takeUntil_and_reverse_takeUntil
    [DecidableEq V]
    {u v z x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ p.support)
    (hzrev : z ∈ p.reverse.support)
    (hx_take : x ∈ (p.takeUntil z hz).support)
    (hx_rev_take : x ∈ (p.reverse.takeUntil z hzrev).reverse.support) :
    x = z := by
  have hx_take_list :
      x ∈ p.support.take (p.support.idxOf z + 1) := by
    simpa [SimpleGraph.Walk.takeUntil_eq_take,
      SimpleGraph.Walk.take_support_eq_support_take_succ] using hx_take
  have hx_rev_take_list :
      x ∈ (p.support.reverse.take (p.support.reverse.idxOf z + 1)).reverse := by
    simpa [SimpleGraph.Walk.takeUntil_eq_take,
      SimpleGraph.Walk.take_support_eq_support_take_succ,
      SimpleGraph.Walk.support_reverse] using hx_rev_take
  exact
    List.eq_of_mem_take_and_reverse_take_of_nodup hp.support_nodup hz
      hx_take_list hx_rev_take_list


theorem Walk.IsPath.takeUntil_punctured_support_disjoint_reverse_takeUntil
    [DecidableEq V]
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ p.support)
    (hzrev : z ∈ p.reverse.support) :
    Disjoint
      {x : V | x ∈ (p.takeUntil z hz).support ∧ x ≠ z}
      {x : V | x ∈ (p.reverse.takeUntil z hzrev).reverse.support} := by
  rw [Set.disjoint_left]
  rintro x ⟨hx_take, hx_ne⟩ hx_rev_take
  exact hx_ne
    (Walk.IsPath.eq_of_mem_takeUntil_and_reverse_takeUntil
      hp hz hzrev hx_take hx_rev_take)


theorem Walk.first_common_takeUntil_punctured_disjoint_support
    [DecidableEq V]
    {u v a b z : V}
    {p : G.Walk u v}
    {q : G.Walk a b}
    (hzp : z ∈ p.support)
    (hfirst :
      forall t : V,
        t ∈ q.support ->
          t ∈ (p.takeUntil z hzp).support ->
            t = z) :
    Disjoint
      {t : V | t ∈ (p.takeUntil z hzp).support ∧ t ≠ z}
      {t : V | t ∈ q.support} := by
  rw [Set.disjoint_left]
  rintro t ⟨htprefix, ht_ne_z⟩ htq
  exact ht_ne_z (hfirst t htq htprefix)


theorem Walk.first_common_takeUntil_punctured_disjoint_takeUntil
    [DecidableEq V]
    {u v a b z : V}
    {p : G.Walk u v}
    {q : G.Walk a b}
    (hzp : z ∈ p.support)
    (hzq : z ∈ q.support)
    (hfirst :
      forall t : V,
        t ∈ q.support ->
          t ∈ (p.takeUntil z hzp).support ->
            t = z) :
    Disjoint
      {t : V | t ∈ (p.takeUntil z hzp).support ∧ t ≠ z}
      {t : V | t ∈ (q.takeUntil z hzq).support ∧ t ≠ z} := by
  rw [Set.disjoint_left]
  rintro t htprefix ⟨htqprefix, _ht_ne_z'⟩
  exact Set.disjoint_left.mp
    (Walk.first_common_takeUntil_punctured_disjoint_support
      (p := p) (q := q) hzp hfirst)
    htprefix
      (SimpleGraph.Walk.support_takeUntil_subset q hzq htqprefix)


theorem Walk.IsPath.end_not_mem_takeUntil_support_of_internal
    [DecidableEq V]
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ Walk.InternalVertices p) :
    v ∉ (p.takeUntil z hz.1).support := by
  exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hz.1 hz.2.2.symm


theorem Walk.IsPath.start_not_mem_dropUntil_support_of_internal
    [DecidableEq V]
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ Walk.InternalVertices p) :
    u ∉ (p.dropUntil z hz.1).support :=
  Walk.IsPath.start_not_mem_dropUntil_support_of_ne hp hz.1 hz.2.1


theorem Walk.IsPath.end_not_mem_reverse_takeUntil_support_of_internal
    [DecidableEq V]
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ Walk.InternalVertices p) :
    v ∉ (p.takeUntil z hz.1).reverse.support := by
  intro hv
  exact Walk.IsPath.end_not_mem_takeUntil_support_of_internal hp hz (by
    simpa [SimpleGraph.Walk.support_reverse] using hv)


theorem List.idxOf_getLast_of_nodup [DecidableEq V]
    {l : List V}
    (hn : l.Nodup)
    (hl : l ≠ []) :
    l.idxOf (l.getLast hl) = l.length - 1 := by
  exact List.idxOf_getLast hl (by
    have hnd_append : (l.dropLast ++ [l.getLast hl]).Nodup := by
      simpa [List.dropLast_append_getLast hl] using hn
    have hdisj : List.Disjoint l.dropLast [l.getLast hl] :=
      List.disjoint_of_nodup_append hnd_append
    intro hmem
    exact hdisj hmem (by simp))


theorem Walk.IsPath.mem_support_takeUntil_end
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support) :
    x ∈ (p.takeUntil v p.end_mem_support).support := by
  have hend_idx :
      p.support.idxOf v = p.support.length - 1 := by
    have hlast : p.support.getLast p.support_ne_nil = v := by
      simp
    simpa [hlast] using
      (List.idxOf_getLast_of_nodup hp.support_nodup p.support_ne_nil)
  have hx_take :
      x ∈ p.support.take (p.support.idxOf v + 1) := by
    have htake_len : p.support.idxOf v + 1 = p.support.length := by
      rw [hend_idx]
      exact Nat.sub_one_add_one_eq_of_pos
        (List.length_pos_iff.mpr p.support_ne_nil)
    exact (List.mem_take_iff_idxOf_lt hx).mpr (by
      rw [htake_len]
      exact List.idxOf_lt_length_iff.mpr hx)
  simpa [SimpleGraph.Walk.takeUntil_eq_take,
    SimpleGraph.Walk.take_support_eq_support_take_succ] using hx_take


theorem Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
    [DecidableEq V]
    {u v z x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ p.support)
    (hzrev : z ∈ p.reverse.support)
    (hx_drop : x ∈ (p.dropUntil z hz).support) :
    x ∈ (p.reverse.takeUntil z hzrev).support := by
  have hx : x ∈ p.support :=
    SimpleGraph.Walk.support_dropUntil_subset p hz hx_drop
  have hidx_le_len : p.support.idxOf z <= p.length := by
    have hidx_lt : p.support.idxOf z < p.support.length :=
      List.idxOf_lt_length_iff.mpr hz
    simpa [SimpleGraph.Walk.length_support] using hidx_lt
  have hx_drop_list :
      x ∈ p.support.drop (p.support.idxOf z) := by
    simpa [SimpleGraph.Walk.dropUntil_eq_drop,
      SimpleGraph.Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left hidx_le_len] using hx_drop
  have hidx :
      p.support.idxOf z <= p.support.idxOf x :=
    List.idxOf_ge_of_mem_drop_of_nodup hp.support_nodup hx_drop_list
  have hx_rev_take :
      x ∈ p.support.reverse.take (p.support.reverse.idxOf z + 1) :=
    List.mem_reverse_take_of_nodup_of_idx_le hp.support_nodup hx hz hidx
  simpa [SimpleGraph.Walk.takeUntil_eq_take,
    SimpleGraph.Walk.take_support_eq_support_take_succ,
    SimpleGraph.Walk.support_reverse] using hx_rev_take

/-- Membership counterpart in the other direction: the prefix ending at a
split vertex becomes the suffix starting there after reversing a simple
path. -/
theorem Walk.IsPath.mem_reverse_dropUntil_of_mem_takeUntil
    [DecidableEq V]
    {u v z x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ p.support)
    (hzrev : z ∈ p.reverse.support)
    (hx_take : x ∈ (p.takeUntil z hz).support) :
    x ∈ (p.reverse.dropUntil z hzrev).support := by
  have hx : x ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hz hx_take
  have hxrev : x ∈ p.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hx
  apply Walk.mem_dropUntil_of_idxOf_le hzrev hxrev
  have hle : p.support.idxOf x <= p.support.idxOf z :=
    Walk.idxOf_le_split_of_mem_takeUntil hz hx_take
  have hidx_rev_z :
      p.reverse.support.idxOf z =
        p.support.length - 1 - p.support.idxOf z := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.idxOf_reverse_of_nodup hp.support_nodup hz
  have hidx_rev_x :
      p.reverse.support.idxOf x =
        p.support.length - 1 - p.support.idxOf x := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.idxOf_reverse_of_nodup hp.support_nodup hx
  rw [hidx_rev_z, hidx_rev_x]
  have hz_lt : p.support.idxOf z < p.support.length :=
    List.idxOf_lt_length_iff.mpr hz
  have hx_lt : p.support.idxOf x < p.support.length :=
    List.idxOf_lt_length_iff.mpr hx
  omega


theorem Walk.IsPath.start_not_mem_reverse_dropUntil_support_of_internal
    [DecidableEq V]
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ Walk.InternalVertices p) :
    u ∉ (p.dropUntil z hz.1).reverse.support := by
  intro hu
  exact Walk.IsPath.start_not_mem_dropUntil_support_of_internal hp hz (by
    simpa [SimpleGraph.Walk.support_reverse] using hu)

theorem Walk.IsPath.dropUntil_tail_support_disjoint_reverse_dropUntil_tail_support_of_internal
    [DecidableEq V]
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ Walk.InternalVertices p) :
    Disjoint
      {x : V | x ∈ (p.dropUntil z hz.1).tail.support}
      {x : V | x ∈ (p.reverse.dropUntil z (by
        rw [SimpleGraph.Walk.support_reverse]
        exact List.mem_reverse.mpr hz.1)).tail.support} := by
  classical
  let pR : G.Walk z v := p.dropUntil z hz.1
  have hzrev : z ∈ p.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hz.1
  let pL : G.Walk z u := p.reverse.dropUntil z hzrev
  have hpR : pR.IsPath := by
    simpa [pR] using hp.dropUntil hz.1
  have hpL : pL.IsPath := by
    simpa [pL] using hp.reverse.dropUntil hzrev
  have hpR_not_nil : ¬ pR.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pR) hz.2.2
  have hpL_not_nil : ¬ pL.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pL) hz.2.1
  rw [Set.disjoint_left]
  intro x hxR hxL
  have hxR_tail : x ∈ pR.support.tail := by
    rwa [← pR.support_tail_of_not_nil hpR_not_nil]
  have hxR_support : x ∈ pR.support := List.mem_of_mem_tail hxR_tail
  have hxR_ne_z : x ≠ z := by
    intro hxz
    exact Walk.IsPath.start_notMem_tail_support hpR
      (by simpa [hxz] using hxR_tail)
  have hxL_tail : x ∈ pL.support.tail := by
    rwa [← pL.support_tail_of_not_nil hpL_not_nil]
  have hxL_support : x ∈ pL.support := List.mem_of_mem_tail hxL_tail
  have hx_take : x ∈ (p.takeUntil z hz.1).support := by
    have hx_take0 :
        x ∈ ((p.reverse).reverse.takeUntil z (by
          rw [SimpleGraph.Walk.support_reverse]
          exact List.mem_reverse.mpr hzrev)).support := by
      exact Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
        (p := p.reverse) hp.reverse hzrev
        (by
          rw [SimpleGraph.Walk.support_reverse]
          exact List.mem_reverse.mpr hzrev)
        hxL_support
    simpa using hx_take0
  have hx_drop : x ∈ (p.dropUntil z hz.1).support := by
    simpa [pR] using hxR_support
  exact Set.disjoint_left.mp
    (Walk.IsPath.punctured_takeUntil_support_disjoint_dropUntil_support hp hz.1)
    ⟨hx_take, hxR_ne_z⟩ hx_drop


theorem Walk.mem_support_takeUntil_or_mem_support_takeUntil
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support) :
    x ∈ (p.takeUntil y hy).support ∨
      y ∈ (p.takeUntil x hx).support := by
  classical
  have hxy_total :
      p.support.idxOf x <= p.support.idxOf y ∨
        p.support.idxOf y <= p.support.idxOf x :=
    le_total (p.support.idxOf x) (p.support.idxOf y)
  rcases hxy_total with hxy | hyx
  · left
    rw [SimpleGraph.Walk.takeUntil_eq_take p hy]
    simp [SimpleGraph.Walk.take_support_eq_support_take_succ]
    rw [List.mem_iff_getElem]
    refine ⟨p.support.idxOf x, ?_, ?_⟩
    · rw [List.length_take]
      have hxlt : p.support.idxOf x < p.support.length :=
        List.idxOf_lt_length_of_mem hx
      omega
    · rw [List.getElem_take]
      exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)
  · right
    rw [SimpleGraph.Walk.takeUntil_eq_take p hx]
    simp [SimpleGraph.Walk.take_support_eq_support_take_succ]
    rw [List.mem_iff_getElem]
    refine ⟨p.support.idxOf y, ?_, ?_⟩
    · rw [List.length_take]
      have hylt : p.support.idxOf y < p.support.length :=
        List.idxOf_lt_length_of_mem hy
      omega
    · rw [List.getElem_take]
      exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)



end Schematic.Math.GraphTheory
