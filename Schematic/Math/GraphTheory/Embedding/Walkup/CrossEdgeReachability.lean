import Schematic.Math.GraphTheory.Embedding.Walkup.EdgeDomains

/-! Reachability in the cross-edge branch of Walkup deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

theorem walkupE_edgePermReachable_edge_to_node_of_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    PermReachable (G.walkupE z).edge
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  classical
  let σ : Equiv.Perm G.Dart := G.edge
  let xk : Nat → G.Dart := fun k => (σ : G.Dart → G.Dart)^[k + 1] z
  have hzne : z ≠ G.node z := by
    intro h
    exact G.node_ne_self_of_not_link_self hz h.symm
  rcases permReachable_exists_first_positive_iterate σ hcross hzne with
    ⟨m, hmpos, hm, hmin⟩
  rcases Nat.exists_eq_add_of_lt hmpos with ⟨n, rfl⟩
  have htarget_iter :
      (σ : G.Dart → G.Dart)^[n + 1] z = G.node z := by
    simpa [Nat.zero_add, Nat.add_assoc] using hm
  have hperiod_no :
      ∀ p : Nat, 0 < p → p < n + 1 →
        (σ : G.Dart → G.Dart)^[p] z ≠ z := by
    intro p hp hplt hpz
    have hle : p ≤ n + 1 := Nat.le_of_lt hplt
    have hearly :
        (σ : G.Dart → G.Dart)^[n + 1 - p] z = G.node z := by
      calc
        (σ : G.Dart → G.Dart)^[n + 1 - p] z =
            (σ : G.Dart → G.Dart)^[n + 1 - p]
              ((σ : G.Dart → G.Dart)^[p] z) := by rw [hpz]
        _ = (σ : G.Dart → G.Dart)^[n + 1 - p + p] z := by
          rw [Function.iterate_add_apply]
        _ = (σ : G.Dart → G.Dart)^[n + 1] z := by
          rw [Nat.sub_add_cancel hle]
        _ = G.node z := htarget_iter
    have hlt : n + 1 - p < n + 1 := by omega
    exact hmin (n + 1 - p) (by
      simpa [Nat.zero_add, Nat.add_assoc] using hlt) hearly
  have hx_ne_z : ∀ k : Nat, k ≤ n → xk k ≠ z := by
    intro k hk hxz
    have hiter :
        (σ : G.Dart → G.Dart)^[k + 1] z = z := by
      simpa [xk] using hxz
    have hle : k + 1 ≤ n + 1 := Nat.succ_le_succ hk
    by_cases heq : k + 1 = n + 1
    · have hnode_z : G.node z = z := by
        rw [← htarget_iter, ← heq]
        exact hiter
      exact G.node_ne_self_of_not_link_self hz hnode_z
    · have hlt : k + 1 < n + 1 := Nat.lt_of_le_of_ne hle heq
      exact hperiod_no (k + 1) (Nat.succ_pos k) hlt hiter
  let dart (k : Nat) (hk : k ≤ n) : (G.walkupE z).Dart :=
    ⟨xk k, hx_ne_z k hk⟩
  have hpath :
      ∀ k : Nat, ∀ hk : k ≤ n,
        PermReachable (G.walkupE z).edge
          (dart 0 (Nat.zero_le n)) (dart k hk) := by
    intro k hk
    induction k with
    | zero =>
        exact PermReachable.refl (G.walkupE z).edge
          (dart 0 (Nat.zero_le n))
    | succ k ih =>
        have hk_le : k ≤ n := Nat.le_of_succ_le hk
        have hk_lt : k < n := Nat.lt_of_succ_le hk
        have ihpath := ih hk_le
        have hxnode : xk k ≠ G.node z := by
          intro hxnode
          have hiter :
              (σ : G.Dart → G.Dart)^[k + 1] z = G.node z := by
            simpa [xk] using hxnode
          exact hmin (k + 1) (by
            have : k + 1 < n + 1 := Nat.succ_lt_succ hk_lt
            simpa [Nat.zero_add, Nat.add_assoc] using this) hiter
        have hxpred : xk k ≠ G.edge.symm z := by
          intro hxpred
          have hiter_pred :
              (σ : G.Dart → G.Dart)^[k + 1] z = G.edge.symm z := by
            simpa [xk, σ] using hxpred
          have hperiod :
              (σ : G.Dart → G.Dart)^[k + 2] z = z := by
            have hcongr := congrArg (fun x => σ x) hiter_pred
            simpa [σ, Function.iterate_succ_apply', Nat.add_comm,
              Nat.add_left_comm, Nat.add_assoc] using hcongr
          have hp_le : k + 2 ≤ n + 1 := by omega
          by_cases hp_eq : k + 2 = n + 1
          · have hnode_z : G.node z = z := by
              rw [← htarget_iter, ← hp_eq]
              exact hperiod
            exact G.node_ne_self_of_not_link_self hz hnode_z
          · have hp_lt : k + 2 < n + 1 := Nat.lt_of_le_of_ne hp_le hp_eq
            exact hperiod_no (k + 2) (by omega) hp_lt hperiod
        have hstep :
            PermReachable (G.walkupE z).edge
              (dart k hk_le) (dart k.succ hk) := by
          exact G.walkupE_edgePermReachable_of_original_edge_regular
            hz (by
              simp [dart, xk, σ, Function.iterate_succ_apply'])
            hxnode hxpred
        exact PermReachable.trans (G.walkupE z).edge ihpath hstep
  have hsource :
      dart 0 (Nat.zero_le n) =
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
    apply Subtype.ext
    simp [dart, xk, σ]
  have htarget :
      dart n le_rfl =
        (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
    apply Subtype.ext
    simpa [dart, xk] using htarget_iter
  simpa [hsource, htarget] using hpath n le_rfl

theorem walkupE_edgePermReachable_edge_node_to_edge_symm_of_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    PermReachable (G.walkupE z).edge
        (⟨G.edge (G.node z), G.edge_node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  classical
  let σ : Equiv.Perm G.Dart := G.edge
  let xk : Nat → G.Dart := fun k => (σ : G.Dart → G.Dart)^[k + 1] (G.node z)
  have hnz : G.node z ≠ z :=
    G.node_ne_self_of_not_link_self hz
  rcases permReachable_exists_first_positive_iterate σ
      (PermReachable.symm σ hcross) hnz with
    ⟨m, hmpos, hm, hmin⟩
  have hm_ne_one : m ≠ 1 := by
    intro hmone
    have hedge_node : G.edge (G.node z) = z := by
      simpa [hmone, σ] using hm
    exact G.edge_node_ne_self_of_not_link_self hz hedge_node
  have hmgt1 : 1 < m := by omega
  rcases Nat.exists_eq_add_of_lt hmgt1 with ⟨n, rfl⟩
  have htarget_full :
      (σ : G.Dart → G.Dart)^[n + 2] (G.node z) = z := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
  have htarget_iter :
      (σ : G.Dart → G.Dart)^[n + 1] (G.node z) = G.edge.symm z := by
    apply G.edge.injective
    calc
      G.edge ((σ : G.Dart → G.Dart)^[n + 1] (G.node z)) =
          (σ : G.Dart → G.Dart)^[n + 2] (G.node z) := by
        simp [σ, Function.iterate_succ_apply']
      _ = z := htarget_full
      _ = G.edge (G.edge.symm z) := by simp
  have hperiod_no :
      ∀ p : Nat, 0 < p → p < n + 2 →
        (σ : G.Dart → G.Dart)^[p] (G.node z) ≠ G.node z := by
    intro p hp hplt hpnode
    have hle : p ≤ n + 2 := Nat.le_of_lt hplt
    have hearly :
        (σ : G.Dart → G.Dart)^[n + 2 - p] (G.node z) = z := by
      calc
        (σ : G.Dart → G.Dart)^[n + 2 - p] (G.node z) =
            (σ : G.Dart → G.Dart)^[n + 2 - p]
              ((σ : G.Dart → G.Dart)^[p] (G.node z)) := by rw [hpnode]
        _ = (σ : G.Dart → G.Dart)^[n + 2 - p + p] (G.node z) := by
          rw [Function.iterate_add_apply]
        _ = (σ : G.Dart → G.Dart)^[n + 2] (G.node z) := by
          rw [Nat.sub_add_cancel hle]
        _ = z := htarget_full
    have hlt : n + 2 - p < n + 2 := by omega
    exact hmin (n + 2 - p) (by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt) hearly
  have hx_ne_z : ∀ k : Nat, k ≤ n → xk k ≠ z := by
    intro k hk hxz
    have hiter :
        (σ : G.Dart → G.Dart)^[k + 1] (G.node z) = z := by
      simpa [xk] using hxz
    exact hmin (k + 1) (by
      have : k + 1 < n + 2 := by omega
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this) hiter
  let dart (k : Nat) (hk : k ≤ n) : (G.walkupE z).Dart :=
    ⟨xk k, hx_ne_z k hk⟩
  have hpath :
      ∀ k : Nat, ∀ hk : k ≤ n,
        PermReachable (G.walkupE z).edge
          (dart 0 (Nat.zero_le n)) (dart k hk) := by
    intro k hk
    induction k with
    | zero =>
        exact PermReachable.refl (G.walkupE z).edge
          (dart 0 (Nat.zero_le n))
    | succ k ih =>
        have hk_le : k ≤ n := Nat.le_of_succ_le hk
        have hk_lt : k < n := Nat.lt_of_succ_le hk
        have ihpath := ih hk_le
        have hxnode : xk k ≠ G.node z := by
          intro hxnode
          have hiter :
              (σ : G.Dart → G.Dart)^[k + 1] (G.node z) =
                G.node z := by
            simpa [xk] using hxnode
          have hlt : k + 1 < n + 2 := by omega
          exact hperiod_no (k + 1) (Nat.succ_pos k) hlt hiter
        have hxpred : xk k ≠ G.edge.symm z := by
          intro hxpred
          have hiter_pred :
              (σ : G.Dart → G.Dart)^[k + 1] (G.node z) =
                G.edge.symm z := by
            simpa [xk, σ] using hxpred
          have hhit :
              (σ : G.Dart → G.Dart)^[k + 2] (G.node z) = z := by
            have hcongr := congrArg (fun x => σ x) hiter_pred
            simpa [σ, Function.iterate_succ_apply', Nat.add_comm,
              Nat.add_left_comm, Nat.add_assoc] using hcongr
          exact hmin (k + 2) (by
            have : k + 2 < n + 2 := by omega
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this)
            hhit
        have hstep :
            PermReachable (G.walkupE z).edge
              (dart k hk_le) (dart k.succ hk) := by
          exact G.walkupE_edgePermReachable_of_original_edge_regular
            hz (by
              simp [dart, xk, σ, Function.iterate_succ_apply'])
            hxnode hxpred
        exact PermReachable.trans (G.walkupE z).edge ihpath hstep
  have hsource :
      dart 0 (Nat.zero_le n) =
        (⟨G.edge (G.node z), G.edge_node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
    apply Subtype.ext
    simp [dart, xk, σ]
  have htarget :
      dart n le_rfl =
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
    apply Subtype.ext
    simpa [dart, xk] using htarget_iter
  simpa [hsource, htarget] using hpath n le_rfl

theorem walkupE_edgeOrbit_edge_z_eq_node_of_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    PermOrbit.of (G.walkupE z).edge
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) =
      PermOrbit.of (G.walkupE z).edge
        (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) :=
  PermOrbit.of_eq_of (G.walkupE z).edge
    (G.walkupE_edgePermReachable_edge_to_node_of_cross hz hcross)

theorem walkupE_edgeOrbit_edge_node_eq_edge_symm_of_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    PermOrbit.of (G.walkupE z).edge
        (⟨G.edge (G.node z), G.edge_node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) =
      PermOrbit.of (G.walkupE z).edge
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) :=
  PermOrbit.of_eq_of (G.walkupE z).edge
    (G.walkupE_edgePermReachable_edge_node_to_edge_symm_of_cross hz hcross)

theorem not_walkupE_edgePermReachable_edge_to_edge_symm_of_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    ¬ PermReachable (G.walkupE z).edge
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  classical
  let σ : Equiv.Perm G.Dart := G.edge
  have hzne : z ≠ G.node z := by
    intro h
    exact G.node_ne_self_of_not_link_self hz h.symm
  rcases permReachable_exists_first_positive_iterate σ hcross hzne with
    ⟨m, hmpos, hm, hmin⟩
  rcases Nat.exists_eq_add_of_lt hmpos with ⟨n, rfl⟩
  have htarget_iter :
      (σ : G.Dart → G.Dart)^[n + 1] z = G.node z := by
    simpa [Nat.zero_add, Nat.add_assoc] using hm
  have hperiod_no :
      ∀ p : Nat, 0 < p → p < n + 1 →
        (σ : G.Dart → G.Dart)^[p] z ≠ z := by
    intro p hp hplt hpz
    have hle : p ≤ n + 1 := Nat.le_of_lt hplt
    have hearly :
        (σ : G.Dart → G.Dart)^[n + 1 - p] z = G.node z := by
      calc
        (σ : G.Dart → G.Dart)^[n + 1 - p] z =
            (σ : G.Dart → G.Dart)^[n + 1 - p]
              ((σ : G.Dart → G.Dart)^[p] z) := by rw [hpz]
        _ = (σ : G.Dart → G.Dart)^[n + 1 - p + p] z := by
          rw [Function.iterate_add_apply]
        _ = (σ : G.Dart → G.Dart)^[n + 1] z := by
          rw [Nat.sub_add_cancel hle]
        _ = G.node z := htarget_iter
    have hlt : n + 1 - p < n + 1 := by omega
    exact hmin (n + 1 - p) (by
      simpa [Nat.zero_add, Nat.add_assoc] using hlt) hearly
  let Segment (x : (G.walkupE z).Dart) : Prop :=
    ∃ k : Nat, k ≤ n ∧ x.1 = (σ : G.Dart → G.Dart)^[k + 1] z
  have hsegment_ne_pred :
      ∀ k : Nat, k ≤ n →
        (σ : G.Dart → G.Dart)^[k + 1] z ≠ G.edge.symm z := by
    intro k hk hpred
    have hperiod :
        (σ : G.Dart → G.Dart)^[k + 2] z = z := by
      have hcongr := congrArg (fun x => σ x) hpred
      simpa [σ, Function.iterate_succ_apply', Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hcongr
    by_cases hk_last : k = n
    · subst k
      have hnode_pred : G.node z = G.edge.symm z := by
        rw [← htarget_iter]
        exact hpred
      have hedge_node_z : G.edge (G.node z) = z := by
        rw [hnode_pred]
        simp
      exact G.edge_node_ne_self_of_not_link_self hz hedge_node_z
    · have hklt : k < n := Nat.lt_of_le_of_ne hk hk_last
      have hp_le : k + 2 ≤ n + 1 := by omega
      by_cases hp_eq : k + 2 = n + 1
      · have hnode_z : G.node z = z := by
          rw [← htarget_iter, ← hp_eq]
          exact hperiod
        exact G.node_ne_self_of_not_link_self hz hnode_z
      · have hp_lt : k + 2 < n + 1 := Nat.lt_of_le_of_ne hp_le hp_eq
        exact hperiod_no (k + 2) (by omega) hp_lt hperiod
  have hsegment_ne_node_of_lt :
      ∀ k : Nat, k < n →
        (σ : G.Dart → G.Dart)^[k + 1] z ≠ G.node z := by
    intro k hk hnode
    exact hmin (k + 1) (by
      have : k + 1 < n + 1 := Nat.succ_lt_succ hk
      simpa [Nat.zero_add, Nat.add_assoc] using this) hnode
  have hsegment_pre_ne_z :
      ∀ k : Nat, 0 < k → k ≤ n →
        (σ : G.Dart → G.Dart)^[k] z ≠ z := by
    intro k hkpos hk hret
    have hklt : k < n + 1 := Nat.lt_succ_of_le hk
    exact hperiod_no k hkpos hklt hret
  have hsegment_pre_ne_node :
      ∀ k : Nat, 0 < k → k ≤ n →
        (σ : G.Dart → G.Dart)^[k] z ≠ G.node z := by
    intro k _hkpos hk hnode
    exact hmin k (by
      have : k < n + 1 := Nat.lt_succ_of_le hk
      simpa [Nat.zero_add, Nat.add_assoc] using this) hnode
  have hsegment_pre_ne_pred :
      ∀ k : Nat, 0 < k → k ≤ n →
        (σ : G.Dart → G.Dart)^[k] z ≠ G.edge.symm z := by
    intro k hkpos hk hpred
    have hret :
        (σ : G.Dart → G.Dart)^[k + 1] z = z := by
      have hcongr := congrArg (fun x => σ x) hpred
      simpa [σ, Function.iterate_succ_apply', Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hcongr
    have hp_le : k + 1 ≤ n + 1 := Nat.succ_le_succ hk
    by_cases hp_eq : k + 1 = n + 1
    · have hnode_z : G.node z = z := by
        rw [← htarget_iter, ← hp_eq]
        exact hret
      exact G.node_ne_self_of_not_link_self hz hnode_z
    · have hp_lt : k + 1 < n + 1 := Nat.lt_of_le_of_ne hp_le hp_eq
      exact hperiod_no (k + 1) (Nat.succ_pos k) hp_lt hret
  have hsegment_link :
      ∀ {x y : (G.walkupE z).Dart},
        Segment x → PermLink (G.walkupE z).edge x y → Segment y := by
    intro x y hxseg hxy
    rcases hxseg with ⟨k, hk, hxval⟩
    cases hxy with
    | forward =>
        by_cases hkn : k = n
        · subst k
          refine ⟨0, Nat.zero_le n, ?_⟩
          have hxnode : x.1 = G.node z := by
            rw [hxval, htarget_iter]
          calc
            (((G.walkupE z).edge x).1 : G.Dart) = G.edge z := by
              rw [G.walkupE_edge_apply_coe, hxnode]
              exact G.walkupSkipEdgeAux_node_of_not_link_self hz
            _ = (σ : G.Dart → G.Dart)^[0 + 1] z := by simp [σ]
        · have hklt : k < n := Nat.lt_of_le_of_ne hk hkn
          refine ⟨k + 1, Nat.succ_le_of_lt hklt, ?_⟩
          have hxnode : x.1 ≠ G.node z := by
            rw [hxval]
            exact hsegment_ne_node_of_lt k hklt
          have hxpred : x.1 ≠ G.edge.symm z := by
            rw [hxval]
            exact hsegment_ne_pred k hk
          calc
            (((G.walkupE z).edge x).1 : G.Dart) = G.edge x.1 :=
              G.walkupE_edge_apply_of_not_link_self_of_regular
                hz x hxnode hxpred
            _ = (σ : G.Dart → G.Dart)^[k + 1 + 1] z := by
              rw [hxval]
              simp [σ, Function.iterate_succ_apply']
    | backward =>
        by_cases hkzero : k = 0
        · subst k
          refine ⟨n, le_rfl, ?_⟩
          have hxedge : x =
              (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
                (G.walkupE z).Dart) := by
            apply Subtype.ext
            simpa [σ] using hxval
          have hpre :
              (G.walkupE z).edge
                  (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
                    (G.walkupE z).Dart) = x := by
            rw [hxedge]
            exact G.walkupE_edge_apply_node_of_not_link_self hz
          have hsymm :
              (G.walkupE z).edge.symm x =
                (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
                  (G.walkupE z).Dart) := by
            rw [← hpre]
            simp
          rw [hsymm]
          exact htarget_iter.symm
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
          rcases Nat.exists_eq_add_of_lt hkpos with ⟨j, rfl⟩
          have hjle : j ≤ n := by omega
          refine ⟨j, hjle, ?_⟩
          have hpre_ne_z :
              (σ : G.Dart → G.Dart)^[j + 1] z ≠ z :=
            hsegment_pre_ne_z (j + 1) (Nat.succ_pos j) (by omega)
          let y0 : (G.walkupE z).Dart :=
            ⟨(σ : G.Dart → G.Dart)^[j + 1] z, hpre_ne_z⟩
          have hy0node : y0.1 ≠ G.node z :=
            hsegment_pre_ne_node (j + 1) (Nat.succ_pos j) (by omega)
          have hy0pred : y0.1 ≠ G.edge.symm z :=
            hsegment_pre_ne_pred (j + 1) (Nat.succ_pos j) (by omega)
          have hy0_edge : (G.walkupE z).edge y0 = x := by
            apply Subtype.ext
            calc
              (((G.walkupE z).edge y0).1 : G.Dart) = G.edge y0.1 :=
                G.walkupE_edge_apply_of_not_link_self_of_regular
                  hz y0 hy0node hy0pred
              _ = (σ : G.Dart → G.Dart)^[j + 1 + 1] z := by
                simp [y0, σ, Function.iterate_succ_apply']
              _ = x.1 := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                  using hxval.symm
          have hsymm : (G.walkupE z).edge.symm x = y0 := by
            rw [← hy0_edge]
            simp
          rw [hsymm]
  have hsegment_reachable :
      ∀ {y : (G.walkupE z).Dart},
        PermReachable (G.walkupE z).edge
          (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
            (G.walkupE z).Dart) y → Segment y := by
    intro y hy
    induction hy with
    | refl =>
        exact ⟨0, Nat.zero_le n, by simp [σ]⟩
    | @tail b c hxb hbc ih =>
        exact hsegment_link ih hbc
  intro hreach
  have htarget_seg := hsegment_reachable hreach
  rcases htarget_seg with ⟨k, hk, hpred⟩
  exact hsegment_ne_pred k hk hpred.symm

theorem walkupE_edgeOrbit_edge_z_ne_edge_symm_of_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    PermOrbit.of (G.walkupE z).edge
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) ≠
      PermOrbit.of (G.walkupE z).edge
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  intro h
  exact G.not_walkupE_edgePermReachable_edge_to_edge_symm_of_cross
    hz hcross (Quotient.exact h)

theorem walkupE_edgePermReachable_edge_to_edge_symm_of_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    PermReachable (G.walkupE z).edge
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  classical
  let σ : Equiv.Perm G.Dart := G.edge
  let xk : Nat → G.Dart := fun k => (σ : G.Dart → G.Dart)^[k] (G.edge z)
  have hstart_ne : G.edge z ≠ z := G.edge_ne_self_of_not_link_self hz
  have hreach_z : PermReachable σ (G.edge z) z :=
    PermReachable.symm σ (PermReachable.forward σ z)
  rcases permReachable_exists_first_positive_iterate σ hreach_z hstart_ne with
    ⟨m, hmpos, hm, hmin⟩
  rcases Nat.exists_eq_add_of_lt hmpos with ⟨n, rfl⟩
  have hx_ne_z : ∀ k : Nat, k < n + 1 → xk k ≠ z := by
    intro k hk
    exact hmin k (by simpa [Nat.zero_add, Nat.add_assoc] using hk)
  have hxpred : xk n = G.edge.symm z := by
    apply G.edge.injective
    calc
      G.edge (xk n) = xk (n + 1) := by
        simp [xk, σ, Function.iterate_succ_apply']
      _ = z := by simpa [xk, σ, Nat.zero_add, Nat.add_assoc] using hm
      _ = G.edge (G.edge.symm z) := by simp
  let dart (k : Nat) (hk : k < n + 1) : (G.walkupE z).Dart :=
    ⟨xk k, hx_ne_z k hk⟩
  have hpath :
      ∀ k : Nat, ∀ hk : k ≤ n,
        PermReachable (G.walkupE z).edge
          (dart 0 (Nat.succ_pos n))
          (dart k (Nat.lt_succ_of_le hk)) := by
    intro k hk
    induction k with
    | zero =>
        exact PermReachable.refl (G.walkupE z).edge
          (dart 0 (Nat.succ_pos n))
    | succ k ih =>
        have hk_le : k ≤ n := Nat.le_of_succ_le hk
        have hk_lt : k < n + 1 := Nat.lt_succ_of_le hk_le
        have hks_lt : k.succ < n + 1 := Nat.lt_succ_of_le hk
        have ihpath := ih hk_le
        have hxnode : xk k ≠ G.node z := by
          intro hxnode
          apply hncross
          exact PermReachable.trans G.edge
            (PermReachable.forward G.edge z)
            (permReachable_of_iterate_eq G.edge (by
              simpa [xk, σ] using hxnode))
        have hxedgepred : xk k ≠ G.edge.symm z := by
          intro hxedgepred
          exact hx_ne_z k.succ hks_lt (by
            calc
              xk k.succ = G.edge (xk k) := by
                simp [xk, σ, Function.iterate_succ_apply']
              _ = z := by rw [hxedgepred]; simp)
        have hstep :
            PermReachable (G.walkupE z).edge
              (dart k hk_lt) (dart k.succ hks_lt) := by
          exact G.walkupE_edgePermReachable_of_original_edge_regular
            hz (by simp [dart, xk, σ, Function.iterate_succ_apply'])
            hxnode hxedgepred
        exact PermReachable.trans (G.walkupE z).edge ihpath hstep
  have htarget :
      dart n (Nat.lt_succ_self n) =
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
    apply Subtype.ext
    exact hxpred
  have hsource :
      dart 0 (Nat.succ_pos n) =
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
    rfl
  simpa [hsource, htarget] using hpath n le_rfl

theorem walkupE_edgePermReachable_of_not_cross_of_edge_nodeFace
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    {u v : (G.walkupE z).Dart}
    (hu : u.1 = G.edge z) (hv : v.1 = G.node (G.face z)) :
    PermReachable (G.walkupE z).edge u v := by
  have hu' :
      u =
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
    apply Subtype.ext
    exact hu
  have hv' :
      v =
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
    apply Subtype.ext
    calc
      v.1 = G.node (G.face z) := hv
      _ = G.edge.symm z := G.node_face_eq_edge_symm z
  rw [hu', hv']
  exact G.walkupE_edgePermReachable_edge_to_edge_symm_of_not_cross hz hncross


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
