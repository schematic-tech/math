import Schematic.Math.GraphTheory.PathsTrees.Operations.MinimalTrees

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
/-!
MI integration extras: exact path API names used by the completed main-induction
rerouting proof.  These are background walk facts, appended here rather than
overwriting the RST-specific path/tree development above.
-/

def Walk.SupportInterval [DecidableEq V]
    {u v : V} (p : G.Walk u v) (a b : V) : Set V :=
  {x : V | x ∈ p.support ∧
    p.support.idxOf a <= p.support.idxOf x ∧
      p.support.idxOf x <= p.support.idxOf b}

def Walk.OpenSupportInterval [DecidableEq V]
    {u v : V} (p : G.Walk u v) (a b : V) : Set V :=
  {x : V | x ∈ p.support ∧
    p.support.idxOf a < p.support.idxOf x ∧
      p.support.idxOf x < p.support.idxOf b}

theorem Walk.supportInterval_subset_support
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v) :
    Walk.SupportInterval p a b ⊆ {x : V | x ∈ p.support} := by
  intro x hx
  exact hx.1

theorem Walk.openSupportInterval_subset_support
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v) :
    Walk.OpenSupportInterval p a b ⊆ {x : V | x ∈ p.support} := by
  intro x hx
  exact hx.1

theorem Walk.left_mem_supportInterval
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v)
    (ha : a ∈ p.support)
    (hab : p.support.idxOf a <= p.support.idxOf b) :
    a ∈ Walk.SupportInterval p a b := by
  exact ⟨ha, le_rfl, hab⟩

theorem Walk.right_mem_supportInterval
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v)
    (hb : b ∈ p.support)
    (hab : p.support.idxOf a <= p.support.idxOf b) :
    b ∈ Walk.SupportInterval p a b := by
  exact ⟨hb, hab, le_rfl⟩

theorem Walk.openSupportInterval_subset_supportInterval
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v) :
    Walk.OpenSupportInterval p a b ⊆ Walk.SupportInterval p a b := by
  intro x hx
  exact ⟨hx.1, le_of_lt hx.2.1, le_of_lt hx.2.2⟩

theorem Walk.exists_min_idx_mem_of_set_nonempty
    [Fintype V] [DecidableEq V]
    {u v : V}
    (p : G.Walk u v)
    {B : Set V}
    (hB : B.Nonempty) :
    Exists fun m : V =>
      m ∈ B ∧
        forall b : V, b ∈ B -> p.support.idxOf m <= p.support.idxOf b := by
  classical
  let Hit : Nat -> Prop := fun n =>
    Exists fun b : V => b ∈ B ∧ p.support.idxOf b = n
  have hHit : Exists Hit := by
    rcases hB with ⟨b, hb⟩
    exact ⟨p.support.idxOf b, b, hb, rfl⟩
  let n0 : Nat := Nat.find hHit
  rcases Nat.find_spec hHit with ⟨m, hmB, hmidx⟩
  refine ⟨m, hmB, ?_⟩
  intro b hbB
  have hfind : n0 <= p.support.idxOf b :=
    Nat.find_min' hHit ⟨b, hbB, rfl⟩
  simpa [n0, hmidx] using hfind

theorem Walk.exists_max_idx_mem_of_set_nonempty_of_subset_support
    [Fintype V] [DecidableEq V]
    {u v : V}
    (p : G.Walk u v)
    {B : Set V}
    (hB : B.Nonempty)
    (hB_support : B ⊆ {b : V | b ∈ p.support}) :
    Exists fun m : V =>
      m ∈ B ∧
        forall b : V, b ∈ B -> p.support.idxOf b <= p.support.idxOf m := by
  classical
  let D : Nat := p.length
  let Hit : Nat -> Prop := fun n =>
    Exists fun b : V => b ∈ B ∧ D - p.support.idxOf b = n
  have hHit : Exists Hit := by
    rcases hB with ⟨b, hb⟩
    exact ⟨D - p.support.idxOf b, b, hb, rfl⟩
  let n0 : Nat := Nat.find hHit
  rcases Nat.find_spec hHit with ⟨m, hmB, hmdef⟩
  have hm_le_D : p.support.idxOf m <= D := by
    have hm_lt : p.support.idxOf m < p.support.length :=
      List.idxOf_lt_length_of_mem (hB_support hmB)
    rw [SimpleGraph.Walk.length_support] at hm_lt
    omega
  refine ⟨m, hmB, ?_⟩
  intro b hbB
  have hb_le_D : p.support.idxOf b <= D := by
    have hb_lt : p.support.idxOf b < p.support.length :=
      List.idxOf_lt_length_of_mem (hB_support hbB)
    rw [SimpleGraph.Walk.length_support] at hb_lt
    omega
  have hfind : n0 <= D - p.support.idxOf b :=
    Nat.find_min' hHit ⟨b, hbB, rfl⟩
  have hmdef' : D - p.support.idxOf m = n0 := by
    simpa [n0] using hmdef
  omega

theorem Walk.left_not_mem_openSupportInterval
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v) :
    a ∉ Walk.OpenSupportInterval p a b := by
  intro ha
  exact (Nat.lt_irrefl (p.support.idxOf a)) ha.2.1

theorem Walk.right_not_mem_openSupportInterval
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v) :
    b ∉ Walk.OpenSupportInterval p a b := by
  intro hb
  exact (Nat.lt_irrefl (p.support.idxOf b)) hb.2.2

theorem Walk.mem_supportInterval_eq_endpoint_or_mem_open
    [DecidableEq V]
    {u v a b x : V}
    (p : G.Walk u v)
    (hx : x ∈ Walk.SupportInterval p a b) :
    x = a ∨ x = b ∨ x ∈ Walk.OpenSupportInterval p a b := by
  by_cases hxa_idx : p.support.idxOf x = p.support.idxOf a
  · have hxa : x = a := (List.idxOf_inj hx.1).mp hxa_idx
    exact Or.inl hxa
  · by_cases hxb_idx : p.support.idxOf x = p.support.idxOf b
    · have hxb : x = b := (List.idxOf_inj hx.1).mp hxb_idx
      exact Or.inr (Or.inl hxb)
    · have hax : p.support.idxOf a < p.support.idxOf x := by
        exact lt_of_le_of_ne hx.2.1 (Ne.symm hxa_idx)
      have hxb : p.support.idxOf x < p.support.idxOf b := by
        exact lt_of_le_of_ne hx.2.2 hxb_idx
      exact Or.inr (Or.inr ⟨hx.1, hax, hxb⟩)

theorem Walk.IsPath.exists_consecutive_attachment_interval
    [DecidableEq V]
    {y z b : V}
    {p : G.Walk y z}
    (hp : p.IsPath)
    (A : Set V)
    (hyA : y ∈ A)
    (hzA : z ∈ A)
    (hb_support : b ∈ p.support)
    (hb_not_A : b ∉ A) :
    Exists fun u : V =>
      Exists fun v : V =>
        u ∈ p.support ∧ u ∈ A ∧
          v ∈ p.support ∧ v ∈ A ∧
            b ∈ Walk.OpenSupportInterval p u v ∧
              forall a : V,
                a ∈ Walk.OpenSupportInterval p u v -> a ∉ A := by
  classical
  have hsupport_len_pos : 0 < p.support.length :=
    List.length_pos_of_mem hb_support
  have hy_support : y ∈ p.support := p.start_mem_support
  have hz_support : z ∈ p.support := p.end_mem_support
  have hy_idx : p.support.idxOf y = 0 := by
    have hget : p.support[0]'hsupport_len_pos = y := by
      simp
    simpa [hget] using
      hp.support_nodup.idxOf_getElem 0 hsupport_len_pos
  have hb_idx_pos : 0 < p.support.idxOf b := by
    by_contra hnot
    have hb_idx_zero : p.support.idxOf b = 0 := by omega
    have hby : b = y := by
      exact (List.idxOf_inj hb_support).mp (hb_idx_zero.trans hy_idx.symm)
    exact hb_not_A (by simpa [hby] using hyA)
  let LeftHit : Nat -> Prop := fun d =>
    Exists fun u : V =>
      u ∈ p.support ∧ u ∈ A ∧
        p.support.idxOf u + d + 1 = p.support.idxOf b
  have hLeftHit : Exists LeftHit := by
    refine ⟨p.support.idxOf b - 1, y, hy_support, hyA, ?_⟩
    rw [hy_idx]
    omega
  let dl : Nat := Nat.find hLeftHit
  rcases Nat.find_spec hLeftHit with
    ⟨u, hu_support, huA, hu_eq⟩
  have hu_lt_b : p.support.idxOf u < p.support.idxOf b := by
    omega
  have hleft_max :
      forall a : V, a ∈ p.support -> a ∈ A ->
        p.support.idxOf a < p.support.idxOf b ->
          p.support.idxOf a <= p.support.idxOf u := by
    intro a ha_support haA ha_lt_b
    by_contra hnot_le
    have hu_lt_a : p.support.idxOf u < p.support.idxOf a := by
      omega
    let d : Nat := p.support.idxOf b - p.support.idxOf a - 1
    have hd_eq :
        p.support.idxOf a + d + 1 = p.support.idxOf b := by
      dsimp [d]
      omega
    have hhit : LeftHit d := ⟨a, ha_support, haA, hd_eq⟩
    have hfind_le : dl <= d := Nat.find_min' hLeftHit hhit
    have hd_lt_find : d < dl := by
      dsimp [d, dl] at hfind_le ⊢
      omega
    exact (not_lt_of_ge hfind_le) hd_lt_find
  have hz_idx : p.support.idxOf z = p.length := by
    have hlast_support : p.length < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hget : p.support[p.length]'hlast_support = z := by
      simp
    simpa [hget] using
      hp.support_nodup.idxOf_getElem p.length hlast_support
  have hb_idx_le_z : p.support.idxOf b <= p.support.idxOf z := by
    rw [hz_idx]
    have hb_lt_len : p.support.idxOf b < p.support.length :=
      List.idxOf_lt_length_of_mem hb_support
    rw [SimpleGraph.Walk.length_support] at hb_lt_len
    omega
  have hb_lt_z : p.support.idxOf b < p.support.idxOf z := by
    by_contra hnot_lt
    have hb_eq_z_idx : p.support.idxOf b = p.support.idxOf z := by
      omega
    have hbz : b = z := (List.idxOf_inj hb_support).mp hb_eq_z_idx
    exact hb_not_A (by simpa [hbz] using hzA)
  let RightHit : Nat -> Prop := fun d =>
    Exists fun v : V =>
      v ∈ p.support ∧ v ∈ A ∧
        p.support.idxOf b + d + 1 = p.support.idxOf v
  have hRightHit : Exists RightHit := by
    refine ⟨p.support.idxOf z - p.support.idxOf b - 1, z,
      hz_support, hzA, ?_⟩
    omega
  let dr : Nat := Nat.find hRightHit
  rcases Nat.find_spec hRightHit with
    ⟨v, hv_support, hvA, hv_eq⟩
  have hb_lt_v : p.support.idxOf b < p.support.idxOf v := by
    omega
  have hright_min :
      forall a : V, a ∈ p.support -> a ∈ A ->
        p.support.idxOf b < p.support.idxOf a ->
          p.support.idxOf v <= p.support.idxOf a := by
    intro a ha_support haA hb_lt_a
    by_contra hnot_le
    have ha_lt_v : p.support.idxOf a < p.support.idxOf v := by
      omega
    let d : Nat := p.support.idxOf a - p.support.idxOf b - 1
    have hd_eq :
        p.support.idxOf b + d + 1 = p.support.idxOf a := by
      dsimp [d]
      omega
    have hhit : RightHit d := ⟨a, ha_support, haA, hd_eq⟩
    have hfind_le : dr <= d := Nat.find_min' hRightHit hhit
    have hd_lt_find : d < dr := by
      dsimp [d, dr] at hfind_le ⊢
      omega
    exact (not_lt_of_ge hfind_le) hd_lt_find
  refine ⟨u, v, hu_support, huA, hv_support, hvA,
    ⟨hb_support, hu_lt_b, hb_lt_v⟩, ?_⟩
  intro a ha_open haA
  have ha_support : a ∈ p.support := ha_open.1
  have hu_lt_a : p.support.idxOf u < p.support.idxOf a := ha_open.2.1
  have ha_lt_v : p.support.idxOf a < p.support.idxOf v := ha_open.2.2
  by_cases ha_idx_eq_b : p.support.idxOf a = p.support.idxOf b
  · have hab : a = b := (List.idxOf_inj ha_support).mp ha_idx_eq_b
    exact hb_not_A (by simpa [hab] using haA)
  · have hlt_or_gt :
        p.support.idxOf a < p.support.idxOf b ∨
          p.support.idxOf b < p.support.idxOf a := by
      exact Nat.lt_or_gt_of_ne ha_idx_eq_b
    rcases hlt_or_gt with ha_lt_b | hb_lt_a
    · have ha_le_u := hleft_max a ha_support haA ha_lt_b
      omega
    · have hv_le_a := hright_min a ha_support haA hb_lt_a
      omega

theorem Walk.map_isPath_of_injOn_support
    {W : Type*} {H : SimpleGraph W}
    (f : G →g H)
    {u v : V}
    {p : G.Walk u v}
    (hinj : Set.InjOn f {x : V | x ∈ p.support})
    (hp : p.IsPath) :
    (p.map f).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map]
  exact hp.support_nodup.map_on (by
    intro x hx y hy hxy
    exact hinj hx hy hxy)

theorem Walk.mem_takeUntil_of_idxOf_le
    [DecidableEq V]
    {u v w z : V}
    {p : G.Walk u v}
    (hw : w ∈ p.support)
    (hz : z ∈ p.support)
    (hle : p.support.idxOf z <= p.support.idxOf w) :
    z ∈ (p.takeUntil w hw).support := by
  have hz_take :
      z ∈ p.support.take (p.support.idxOf w + 1) := by
    exact (List.mem_take_iff_idxOf_lt hz).mpr (Nat.lt_succ_of_le hle)
  simpa [SimpleGraph.Walk.takeUntil_eq_take,
    SimpleGraph.Walk.take_support_eq_support_take_succ] using hz_take

theorem Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
    [DecidableEq V]
    {u v w z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support)
    (hz : z ∈ p.support)
    (hlt : p.support.idxOf z < p.support.idxOf w) :
    z ∉ (p.dropUntil w hw).support := by
  intro hz_drop
  have hz_take :
      z ∈ (p.takeUntil w hw).support :=
    Walk.mem_takeUntil_of_idxOf_le hw hz (le_of_lt hlt)
  have hzw :
      z = w :=
    Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      hp hw hz_take hz_drop
  have hidx_eq : p.support.idxOf z = p.support.idxOf w := by
    simp [hzw]
  omega

theorem Walk.idxOf_le_split_of_mem_takeUntil
    [DecidableEq V]
    {u v w z : V}
    {p : G.Walk u v}
    (hw : w ∈ p.support)
    (hz_take : z ∈ (p.takeUntil w hw).support) :
    p.support.idxOf z <= p.support.idxOf w := by
  by_contra hnot
  have hz : z ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hw hz_take
  exact (Walk.not_mem_takeUntil_of_idxOf_lt hw
    (Nat.lt_of_not_ge hnot)) hz_take

theorem Walk.IsPath.split_idxOf_le_of_mem_dropUntil
    [DecidableEq V]
    {u v w z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support)
    (hz_drop : z ∈ (p.dropUntil w hw).support) :
    p.support.idxOf w <= p.support.idxOf z := by
  by_contra hnot
  have hz : z ∈ p.support :=
    SimpleGraph.Walk.support_dropUntil_subset p hw hz_drop
  exact (Walk.IsPath.not_mem_dropUntil_of_idxOf_lt hp hw hz
    (Nat.lt_of_not_ge hnot)) hz_drop

theorem Walk.mem_dropUntil_of_idxOf_le
    [DecidableEq V]
    {u v w z : V}
    {p : G.Walk u v}
    (hw : w ∈ p.support)
    (hz : z ∈ p.support)
    (hle : p.support.idxOf w <= p.support.idxOf z) :
    z ∈ (p.dropUntil w hw).support := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hz_append :
        z ∈ ((p.takeUntil w hw).append (p.dropUntil w hw)).support := by
      simpa [SimpleGraph.Walk.take_spec p hw] using hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz_append
    rcases hz_append with hz_take | hz_drop
    · exact False.elim
        ((Walk.not_mem_takeUntil_of_idxOf_lt hw hlt) hz_take)
    · exact hz_drop
  · have hzw : z = w := by
      exact (List.idxOf_inj hz).mp heq.symm
    simp [hzw]

theorem Walk.IsPath.exists_last_common_vertex
    [DecidableEq V]
    [Fintype V]
    {u v a b : V}
    {p : G.Walk u v}
    {q : G.Walk a b}
    (hq : q.IsPath)
    (hcommon : Exists fun z : V => z ∈ p.support ∧ z ∈ q.support) :
    Exists fun z : V =>
      Exists fun hzq : z ∈ q.support =>
        z ∈ p.support ∧
          forall {y : V},
            y ∈ p.support ->
              y ∈ (q.dropUntil z hzq).support ->
                y = z := by
  classical
  let B : Set V := {z : V | z ∈ p.support ∧ z ∈ q.support}
  have hB_nonempty : B.Nonempty := by
    rcases hcommon with ⟨z, hz_p, hz_q⟩
    exact ⟨z, hz_p, hz_q⟩
  have hB_support : B ⊆ {z : V | z ∈ q.support} := by
    intro z hz
    exact hz.2
  obtain ⟨z, hzB, hmax⟩ :=
    Walk.exists_max_idx_mem_of_set_nonempty_of_subset_support q hB_nonempty hB_support
  refine ⟨z, hzB.2, hzB.1, ?_⟩
  intro y hy_p hy_drop
  have hy_q : y ∈ q.support :=
    SimpleGraph.Walk.support_dropUntil_subset q hzB.2 hy_drop
  have hyB : y ∈ B := ⟨hy_p, hy_q⟩
  have hz_le_y : q.support.idxOf z <= q.support.idxOf y :=
    Walk.IsPath.split_idxOf_le_of_mem_dropUntil hq hzB.2 hy_drop
  have hy_le_z : q.support.idxOf y <= q.support.idxOf z :=
    hmax y hyB
  have hidx : q.support.idxOf y = q.support.idxOf z := by
    omega
  exact (List.idxOf_inj hy_q).mp hidx

theorem Walk.start_idxOf_support
    [DecidableEq V]
    {u v : V}
    (p : G.Walk u v) :
    p.support.idxOf u = 0 := by
  cases p <;> simp

theorem Walk.IsPath.end_idxOf_support
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath) :
    p.support.idxOf v = p.length := by
  have hlast_support : p.length < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hget : p.support[p.length]'hlast_support = v := by
    simp
  simpa [hget] using
    hp.support_nodup.idxOf_getElem p.length hlast_support

theorem Walk.not_start_mem_openSupportInterval
    [DecidableEq V]
    {u v a b : V}
    (p : G.Walk u v) :
    u ∉ Walk.OpenSupportInterval p a b := by
  intro hu
  have hstart : p.support.idxOf u = 0 := Walk.start_idxOf_support p
  have hlt : p.support.idxOf a < 0 := by
    simpa [hstart] using hu.2.1
  omega

theorem Walk.IsPath.not_end_mem_openSupportInterval_of_right_mem
    [DecidableEq V]
    {u v a b : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hb : b ∈ p.support) :
    v ∉ Walk.OpenSupportInterval p a b := by
  intro hv
  have hend : p.support.idxOf v = p.length :=
    Schematic.Math.GraphTheory.Walk.IsPath.end_idxOf_support hp
  have hb_len : p.support.idxOf b <= p.length := by
    have hb_lt : p.support.idxOf b < p.support.length :=
      List.idxOf_lt_length_of_mem hb
    rw [SimpleGraph.Walk.length_support] at hb_lt
    omega
  have hlt : p.length < p.support.idxOf b := by
    simpa [hend] using hv.2.2
  omega

theorem Walk.IsPath.reverse_takeUntil_punctured_support_disjoint_dropUntil
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support) :
    Disjoint
      {z : V | z ∈ (p.takeUntil w hw).reverse.support ∧ z ≠ w}
      {z : V | z ∈ (p.dropUntil w hw).support} := by
  rw [Set.disjoint_left]
  rintro z ⟨hz_take_rev, hz_ne_w⟩ hz_drop
  have hz_take : z ∈ (p.takeUntil w hw).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_take_rev
    exact List.mem_reverse.mp hz_take_rev
  exact Set.disjoint_left.mp
    (Schematic.Math.GraphTheory.Walk.IsPath.punctured_takeUntil_support_disjoint_dropUntil_support hp hw)
    ⟨hz_take, hz_ne_w⟩ hz_drop

theorem Walk.IsPath.reverse_takeUntil_punctured_support_disjoint_punctured_dropUntil
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support) :
    Disjoint
      {z : V | z ∈ (p.takeUntil w hw).reverse.support ∧ z ≠ w}
      {z : V | z ∈ (p.dropUntil w hw).support ∧ z ≠ w} := by
  rw [Set.disjoint_left]
  rintro z hz_take hz_drop
  exact Set.disjoint_left.mp
    (Schematic.Math.GraphTheory.Walk.IsPath.reverse_takeUntil_punctured_support_disjoint_dropUntil hp hw)
    hz_take hz_drop.1

theorem Walk.IsPath.takeUntil_punctured_support_disjoint_reverse_dropUntil
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support) :
    Disjoint
      {z : V | z ∈ (p.takeUntil w hw).support ∧ z ≠ w}
      {z : V | z ∈ (p.dropUntil w hw).reverse.support} := by
  rw [Set.disjoint_left]
  rintro z hz_take hz_drop_rev
  have hz_drop : z ∈ (p.dropUntil w hw).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_drop_rev
    exact List.mem_reverse.mp hz_drop_rev
  exact Set.disjoint_left.mp
    (Schematic.Math.GraphTheory.Walk.IsPath.punctured_takeUntil_support_disjoint_dropUntil_support hp hw)
    hz_take hz_drop

theorem Walk.IsPath.takeUntil_punctured_support_disjoint_reverse_dropUntil_punctured
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support) :
    Disjoint
      {z : V | z ∈ (p.takeUntil w hw).support ∧ z ≠ w}
      {z : V | z ∈ (p.dropUntil w hw).reverse.support ∧ z ≠ w} := by
  rw [Set.disjoint_left]
  rintro z hz_take hz_drop
  exact Set.disjoint_left.mp
    (Schematic.Math.GraphTheory.Walk.IsPath.takeUntil_punctured_support_disjoint_reverse_dropUntil hp hw)
    hz_take hz_drop.1

theorem Walk.IsChordless.toSubgraph_isInduced
    {u v : V}
    {p : G.Walk u v}
    (hchordless : p.IsChordless) :
    p.toSubgraph.IsInduced := by
  intro x hx y hy hxy
  exact Walk.IsChordless.toSubgraph_adj_of_adj hchordless
    (by simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hx)
    (by simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hy)
    hxy

theorem Walk.IsPath.IsChordless.neighborSet_inter_support_ncard_le_two_of_mem_internalVertices
    {u v a : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hchordless : p.IsChordless)
    (ha : a ∈ Walk.InternalVertices p) :
    (G.neighborSet a ∩ {b : V | b ∈ p.support}).ncard <= 2 := by
  have hsub :
      G.neighborSet a ∩ {b : V | b ∈ p.support} ⊆
        p.toSubgraph.neighborSet a :=
    Walk.IsChordless.neighborSet_inter_support_subset_toSubgraph_neighborSet
      hchordless ha.1
  have hpath_card :
      (p.toSubgraph.neighborSet a).ncard = 2 :=
    Walk.IsPath.ncard_neighborSet_toSubgraph_eq_two_of_mem_internalVertices hp ha
  exact (Set.ncard_le_ncard hsub p.finite_neighborSet_toSubgraph).trans_eq hpath_card

theorem Walk.toSubgraph_adj_of_idxOf_succ
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hidx : p.support.idxOf y = p.support.idxOf x + 1) :
    p.toSubgraph.Adj x y := by
  rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  have hidx_x_lt : p.support.idxOf x < p.length := by
    have hy_lt : p.support.idxOf y < p.support.length :=
      List.idxOf_lt_length_of_mem hy
    rw [hidx, SimpleGraph.Walk.length_support] at hy_lt
    omega
  have hidx_x_darts : p.support.idxOf x < p.darts.length := by
    simpa [SimpleGraph.Walk.length_darts] using hidx_x_lt
  have hd_eq :
      (p.darts[p.support.idxOf x]'hidx_x_darts) =
        ⟨⟨p.getVert (p.support.idxOf x),
            p.getVert (p.support.idxOf x + 1)⟩,
          p.adj_getVert_succ hidx_x_lt⟩ := by
    exact SimpleGraph.Walk.darts_getElem_eq_getVert
      (p := p) (p.support.idxOf x) hidx_x_darts
  have hx_get : p.getVert (p.support.idxOf x) = x :=
    SimpleGraph.Walk.getVert_support_idxOf p hx
  have hy_get : p.getVert (p.support.idxOf x + 1) = y := by
    rw [← hidx]
    exact SimpleGraph.Walk.getVert_support_idxOf p hy
  have hedge_eq : (p.darts[p.support.idxOf x]'hidx_x_darts).edge = s(x, y) := by
    rw [hd_eq]
    simp [hx_get, hy_get]
  have hedge_mem :
      (p.darts[p.support.idxOf x]'hidx_x_darts).edge ∈ p.edges := by
    exact List.mem_map.mpr
      ⟨p.darts[p.support.idxOf x]'hidx_x_darts,
        List.getElem_mem hidx_x_darts, rfl⟩
  simpa [hedge_eq] using hedge_mem

theorem Walk.IsPath.toSubgraph_adj_idxOf_eq_succ_or
    [DecidableEq V]
    {u v a b : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hadj : p.toSubgraph.Adj a b) :
    p.support.idxOf b = p.support.idxOf a + 1 ∨
      p.support.idxOf a = p.support.idxOf b + 1 := by
  rcases (SimpleGraph.Walk.toSubgraph_adj_iff p).mp hadj with
    ⟨i, hedge, hi⟩
  have hi_support : i < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hi_succ_support : i + 1 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hidx_i :
      p.support.idxOf (p.getVert i) = i := by
    have hget :
        p.support[i]'hi_support = p.getVert i :=
      SimpleGraph.Walk.support_getElem_eq_getVert p hi_support
    rw [← hget]
    exact hp.support_nodup.idxOf_getElem i hi_support
  have hidx_succ :
      p.support.idxOf (p.getVert (i + 1)) = i + 1 := by
    have hget :
        p.support[i + 1]'hi_succ_support = p.getVert (i + 1) :=
      SimpleGraph.Walk.support_getElem_eq_getVert p hi_succ_support
    rw [← hget]
    exact hp.support_nodup.idxOf_getElem (i + 1) hi_succ_support
  rw [Sym2.eq_iff] at hedge
  rcases hedge with h | h
  · rcases h with ⟨hia, hsb⟩
    left
    rw [← hsb, ← hia, hidx_i, hidx_succ]
  · rcases h with ⟨hib, hsa⟩
    right
    rw [← hsa, ← hib, hidx_i, hidx_succ]

/-- A path prefix contains every edge of the larger path whose two endpoints
already belong to the prefix. -/
theorem Walk.IsPath.toSubgraph_adj_of_support_prefix
    [DecidableEq V]
    {u v u' v' x y : V}
    {p : G.Walk u v} {q : G.Walk u' v'}
    (hq : q.IsPath)
    (hprefix : p.support <+: q.support)
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : q.toSubgraph.spanningCoe.Adj x y) :
    p.toSubgraph.spanningCoe.Adj x y := by
  have hxq : x ∈ q.support := hprefix.subset hx
  have hyq : y ∈ q.support := hprefix.subset hy
  have hidxX : p.support.idxOf x = q.support.idxOf x :=
    hprefix.idxOf_eq_of_mem hx
  have hidxY : p.support.idxOf y = q.support.idxOf y :=
    hprefix.idxOf_eq_of_mem hy
  rcases Walk.IsPath.toSubgraph_adj_idxOf_eq_succ_or
      hq hxy with hxyIdx | hyxIdx
  · apply Walk.toSubgraph_adj_of_idxOf_succ hx hy
    simpa [hidxX, hidxY] using hxyIdx
  · exact (Walk.toSubgraph_adj_of_idxOf_succ hy hx (by
      simpa [hidxX, hidxY] using hyxIdx)).symm

/-- A strict path prefix of the tail of a simple cycle contains every cycle
edge whose endpoints both lie in that prefix.  The omitted tail endpoint is
exactly what rules out the closing edge of the cycle. -/
theorem Walk.IsCycle.toSubgraph_adj_of_tail_support_prefix
    [DecidableEq V]
    {v u w x y : V}
    {c : G.Walk v v} {p : G.Walk u w}
    (hc : c.IsCycle)
    (hprefix : p.support <+: c.tail.support)
    (hend : v ∉ p.support)
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : c.toSubgraph.spanningCoe.Adj x y) :
    p.toSubgraph.spanningCoe.Adj x y := by
  cases c with
  | nil => simp at hc
  | cons hadj q =>
      have hq : q.IsPath := by
        simpa using hc.isPath_tail
      have hedge : s(x, y) ∈ (SimpleGraph.Walk.cons hadj q).edges :=
        SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hxy
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hedge
      rcases hedge with hclosing | htail
      · rw [Sym2.eq_iff] at hclosing
        rcases hclosing with hxy | hyx
        · exact False.elim (hend (by simpa [hxy.1] using hx))
        · exact False.elim (hend (by simpa [hyx.2] using hy))
      · exact Walk.IsPath.toSubgraph_adj_of_support_prefix hq
          (by simpa using hprefix) hx hy
          (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr htail)

/-- Length form of `toSubgraph_adj_of_tail_support_prefix`.  A prefix shorter
than the cycle tail cannot contain the tail endpoint, so the closing edge is
automatically excluded. -/
theorem Walk.IsCycle.toSubgraph_adj_of_tail_support_prefix_of_length_lt
    [DecidableEq V]
    {v u w x y : V}
    {c : G.Walk v v} {p : G.Walk u w}
    (hc : c.IsCycle)
    (hprefix : p.support <+: c.tail.support)
    (hlength : p.length < c.tail.length)
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : c.toSubgraph.spanningCoe.Adj x y) :
    p.toSubgraph.spanningCoe.Adj x y := by
  have htailPath : c.tail.IsPath := hc.isPath_tail
  have hend : v ∉ p.support := by
    intro hv
    have hidxPrefix := hprefix.idxOf_eq_of_mem hv
    have hidxLt : p.support.idxOf v < p.support.length :=
      List.idxOf_lt_length_of_mem hv
    have htailEnd : c.tail.support.idxOf v = c.tail.length :=
      Walk.IsPath.end_idxOf_support htailPath
    rw [hidxPrefix, htailEnd, SimpleGraph.Walk.length_support] at hidxLt
    omega
  exact Walk.IsCycle.toSubgraph_adj_of_tail_support_prefix
    hc hprefix hend hx hy hxy

/-- A copied strict `drop 1`/`take k` segment of a simple cycle contains every
cycle edge whose endpoints lie on the copied segment. -/
theorem Walk.IsCycle.toSubgraph_adj_of_drop_one_take_copy
    [DecidableEq V]
    {v u w x y : V}
    {c : G.Walk v v} {p : G.Walk u w} {k : Nat}
    (hc : c.IsCycle)
    (hsupport : p.support = ((c.drop 1).take k).support)
    (hproper : k + 1 < c.length)
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : c.toSubgraph.spanningCoe.Adj x y) :
    p.toSubgraph.spanningCoe.Adj x y := by
  have hsegmentPrefix : ((c.drop 1).take k).support <+: c.tail.support := by
    change (c.tail.take k).support <+: c.tail.support
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ]
    exact List.take_prefix _ _
  have hprefix : p.support <+: c.tail.support := by
    rw [hsupport]
    exact hsegmentPrefix
  have hsupportLength := congrArg List.length hsupport
  have htailLength : c.tail.length + 1 = c.length :=
    SimpleGraph.Walk.length_tail_add_one hc.not_nil
  have hpLength : p.length = k := by
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.take_length,
      SimpleGraph.Walk.drop_length] at hsupportLength
    omega
  have hlength : p.length < c.tail.length := by
    omega
  exact
    Walk.IsCycle.toSubgraph_adj_of_tail_support_prefix_of_length_lt
      hc hprefix hlength hx hy hxy

/-- If a source edge occurs in a simple path, its two endpoints occur
consecutively in the path support, in one of the two possible orientations. -/
theorem Walk.IsPath.idxOf_eq_succ_or_of_mem_edges
    [DecidableEq V]
    {u v a b : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hedge : s(a, b) ∈ p.edges) :
    p.support.idxOf b = p.support.idxOf a + 1 ∨
      p.support.idxOf a = p.support.idxOf b + 1 := by
  have hadj : p.toSubgraph.Adj a b := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    exact hedge
  exact Walk.IsPath.toSubgraph_adj_idxOf_eq_succ_or hp hadj

theorem Walk.IsPath.IsChordless.adj_openSupportInterval_path_outside_eq_endpoint
    [DecidableEq V]
    {u v y z a b : V}
    {p : G.Walk y z}
    (hp : p.IsPath)
    (hchordless : p.IsChordless)
    (ha_open : a ∈ Walk.OpenSupportInterval p u v)
    (hb_path : b ∈ p.support)
    (hb_not_open : b ∉ Walk.OpenSupportInterval p u v)
    (hab : G.Adj a b) :
    b = u ∨ b = v := by
  have hpath_adj : p.toSubgraph.Adj a b :=
    Walk.IsChordless.toSubgraph_adj_of_adj
      hchordless ha_open.1 hb_path hab
  have hu_lt_a : p.support.idxOf u < p.support.idxOf a := ha_open.2.1
  have ha_lt_v : p.support.idxOf a < p.support.idxOf v := ha_open.2.2
  rcases Walk.IsPath.toSubgraph_adj_idxOf_eq_succ_or
      hp hpath_adj with hsucc | hpred
  · have hb_not_between :
        ¬ (p.support.idxOf u < p.support.idxOf b ∧
            p.support.idxOf b < p.support.idxOf v) := by
      intro hb_between
      exact hb_not_open ⟨hb_path, hb_between.1, hb_between.2⟩
    have hb_le_u_or_v_le_b :
        p.support.idxOf b <= p.support.idxOf u ∨
          p.support.idxOf v <= p.support.idxOf b := by
      omega
    rcases hb_le_u_or_v_le_b with hb_le_u | hv_le_b
    · have hfalse : False := by
        omega
      exact False.elim hfalse
    · have hidx_av : p.support.idxOf a + 1 = p.support.idxOf v := by
        omega
      have hidx_bv : p.support.idxOf b = p.support.idxOf v := by
        rw [hsucc]
        exact hidx_av
      exact Or.inr ((List.idxOf_inj hb_path).mp hidx_bv)
  · have hb_not_between :
        ¬ (p.support.idxOf u < p.support.idxOf b ∧
            p.support.idxOf b < p.support.idxOf v) := by
      intro hb_between
      exact hb_not_open ⟨hb_path, hb_between.1, hb_between.2⟩
    have hb_le_u_or_v_le_b :
        p.support.idxOf b <= p.support.idxOf u ∨
          p.support.idxOf v <= p.support.idxOf b := by
      omega
    rcases hb_le_u_or_v_le_b with hb_le_u | hv_le_b
    · have hidx_bu : p.support.idxOf b = p.support.idxOf u := by
        omega
      exact Or.inl ((List.idxOf_inj hb_path).mp hidx_bu)
    · have hfalse : False := by
        omega
      exact False.elim hfalse

theorem Walk.exists_shorter_path_of_not_chordless
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hnot : ¬ p.IsChordless) :
    Exists fun q : G.Walk u v =>
      q.IsPath ∧ q.length < p.length ∧
        forall z : V, z ∈ q.support -> z ∈ p.support := by
  rcases (Walk.not_isChordless_iff_exists_adj_not_toSubgraph_adj p).mp hnot with
    ⟨x, hx, y, hy, hxy, hnot_toSubgraph⟩
  have hidx_ne : p.support.idxOf x ≠ p.support.idxOf y := by
    intro hidx_eq
    exact hxy.ne (by
      have := (List.idxOf_inj hx).mp hidx_eq
      exact this)
  have hordered :
      p.support.idxOf x < p.support.idxOf y ∨
        p.support.idxOf y < p.support.idxOf x := by
    exact Nat.lt_or_gt_of_ne hidx_ne
  have hshortcut
      {a b : V}
      (ha : a ∈ p.support)
      (hb : b ∈ p.support)
      (hab : G.Adj a b)
      (hnot_ab : ¬ p.toSubgraph.Adj a b)
      (hlt : p.support.idxOf a < p.support.idxOf b) :
      Exists fun q : G.Walk u v =>
        q.IsPath ∧ q.length < p.length ∧
          forall z : V, z ∈ q.support -> z ∈ p.support := by
    have hnot_succ :
        p.support.idxOf b ≠ p.support.idxOf a + 1 := by
      intro hsucc
      exact hnot_ab
        (Walk.toSubgraph_adj_of_idxOf_succ (p := p) ha hb hsucc)
    have hgap : p.support.idxOf a + 1 < p.support.idxOf b := by
      omega
    have hb_idx_le : p.support.idxOf b <= p.length := by
      have hb_lt : p.support.idxOf b < p.support.length :=
        List.idxOf_lt_length_of_mem hb
      rw [SimpleGraph.Walk.length_support] at hb_lt
      omega
    let r : G.Walk u v :=
      ((p.takeUntil a ha).append hab.toWalk).append (p.dropUntil b hb)
    have hr_len : r.length < p.length := by
      dsimp [r]
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_takeUntil, SimpleGraph.Walk.length_dropUntil]
      simp
      omega
    refine ⟨(r.toPath : G.Walk u v), ?_, ?_, ?_⟩
    · exact SimpleGraph.Path.isPath r.toPath
    · exact lt_of_le_of_lt (SimpleGraph.Walk.length_bypass_le r) hr_len
    · intro z hz
      have hz_r : z ∈ r.support :=
        SimpleGraph.Walk.support_toPath_subset r hz
      simp only [r, SimpleGraph.Walk.mem_support_append_iff] at hz_r
      rcases hz_r with hz_left | hz_drop
      · rcases hz_left with hz_take | hz_edge
        · exact SimpleGraph.Walk.support_takeUntil_subset p ha hz_take
        · have hz_ab : z = a ∨ z = b := by
            simpa using hz_edge
          exact hz_ab.elim (fun hza => hza.symm ▸ ha) (fun hzb => hzb.symm ▸ hb)
      · exact SimpleGraph.Walk.support_dropUntil_subset p hb hz_drop
  rcases hordered with hxy_order | hyx_order
  · exact hshortcut hx hy hxy hnot_toSubgraph hxy_order
  · exact hshortcut hy hx hxy.symm (by
      intro hyx
      exact hnot_toSubgraph hyx.symm) hyx_order


end Schematic.Math.GraphTheory
