import Schematic.Math.GraphTheory.PathsTrees.Foundations.Cycles

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
theorem Walk.map_subgraph_toSubgraph_le
    {H : G.Subgraph} {u v : H.verts} (p : H.coe.Walk u v) :
    (p.map H.hom).toSubgraph ≤ H := by
  rw [SimpleGraph.Walk.toSubgraph_map]
  exact le_trans
    (SimpleGraph.Subgraph.map_mono
      (show p.toSubgraph ≤ (⊤ : H.coe.Subgraph) from le_top))
    (by simp)

theorem Walk.mem_support_map_subgraph_hom_iff
    {H : G.Subgraph} {u v : H.verts} (p : H.coe.Walk u v) {z : V} :
    z ∈ (p.map H.hom).support ↔
      Exists fun zH : H.verts => zH ∈ p.support ∧ (zH : V) = z := by
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hz
    rcases List.mem_map.mp hz with ⟨zH, hzH_support, hzH_eq⟩
    exact ⟨zH, hzH_support, by simpa using hzH_eq⟩
  · rintro ⟨zH, hzH_support, rfl⟩
    exact List.mem_map.mpr ⟨zH, hzH_support, by simp⟩

theorem Walk.support_map_subgraph_hom_subset
    {H : G.Subgraph} {u v : H.verts} (p : H.coe.Walk u v) :
    {z : V | z ∈ (p.map H.hom).support} ⊆ H.verts := by
  intro z hz
  rcases (Walk.mem_support_map_subgraph_hom_iff p).mp hz with ⟨zH, _hzH, rfl⟩
  exact zH.2

theorem Walk.mem_internalVertices_map_subgraph_hom_iff
    {H : G.Subgraph} {u v : H.verts} (p : H.coe.Walk u v) {z : V} :
    z ∈ Walk.InternalVertices (p.map H.hom) ↔
      Exists fun zH : H.verts => zH ∈ Walk.InternalVertices p ∧ (zH : V) = z := by
  constructor
  · intro hz
    rcases (Walk.mem_support_map_subgraph_hom_iff p).mp hz.1 with
      ⟨zH, hzH_support, hzH_eq⟩
    refine ⟨zH, ⟨hzH_support, ?_, ?_⟩, hzH_eq⟩
    · intro hzu
      exact hz.2.1 (hzH_eq.symm.trans (congrArg Subtype.val hzu))
    · intro hzv
      exact hz.2.2 (hzH_eq.symm.trans (congrArg Subtype.val hzv))
  · rintro ⟨zH, hzH, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (Walk.mem_support_map_subgraph_hom_iff p).mpr
        ⟨zH, hzH.1, rfl⟩
    · intro hzu
      exact hzH.2.1 (Subtype.ext hzu)
    · intro hzv
      exact hzH.2.2 (Subtype.ext hzv)

theorem Walk.internalVertices_map_subgraph_hom_subset
    {H : G.Subgraph} {u v : H.verts} (p : H.coe.Walk u v) :
    Walk.InternalVertices (p.map H.hom) ⊆ H.verts := by
  intro z hz
  rcases (Walk.mem_internalVertices_map_subgraph_hom_iff p).mp hz with
    ⟨zH, _hzH, rfl⟩
  exact zH.2

theorem Subgraph.walk_family_mapped_punctured_supports_disjoint
    {B : G.Subgraph}
    {ι : Type*}
    {root : B.verts}
    {terminal : ι -> B.verts}
    (stem : forall i : ι, B.coe.Walk root (terminal i))
    (hdisjoint :
      forall {i j : ι}, i ≠ j ->
        Disjoint
          {z : B.verts | z ∈ (stem i).support ∧ z ≠ root}
          {z : B.verts | z ∈ (stem j).support ∧ z ≠ root}) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ ((stem i).map B.hom).support ∧ z ≠ (root : V)}
        {z : V | z ∈ ((stem j).map B.hom).support ∧ z ≠ (root : V)} := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro z ⟨hzi, hzi_ne_root⟩ ⟨hzj, hzj_ne_root⟩
  rcases (Walk.mem_support_map_subgraph_hom_iff
    (H := B) (stem i)).mp hzi with ⟨zi, hzi_support, hzi_eq⟩
  rcases (Walk.mem_support_map_subgraph_hom_iff
    (H := B) (stem j)).mp hzj with ⟨zj, hzj_support, hzj_eq⟩
  have hzi_ne : zi ≠ root := by
    intro h
    exact hzi_ne_root (by
      calc
        z = (zi : V) := hzi_eq.symm
        _ = (root : V) := by rw [h])
  have hzj_ne : zj ≠ root := by
    intro h
    exact hzj_ne_root (by
      calc
        z = (zj : V) := hzj_eq.symm
        _ = (root : V) := by rw [h])
  have hzij : zi = zj := by
    apply Subtype.ext
    exact hzi_eq.trans hzj_eq.symm
  exact Set.disjoint_left.mp (hdisjoint hij)
    ⟨hzi_support, hzi_ne⟩
    ⟨by simpa [hzij] using hzj_support, by simpa [hzij] using hzj_ne⟩

theorem Subgraph.walk_family_mapped_punctured_supports_disjoint_of_delete_root_unreachable
    {B : G.Subgraph}
    [DecidableEq B.verts]
    {ι : Type*}
    {root : B.verts}
    {terminal : ι -> B.verts}
    (stem : forall i : ι, B.coe.Walk root (terminal i))
    (hterminal_ne : forall i : ι, terminal i ≠ root)
    (hstem_path : forall i : ι, (stem i).IsPath)
    (hunreachable :
      forall {i j : ι}, i ≠ j ->
        ¬ (B.coe.induce ({root} : Set B.verts)ᶜ).Reachable
            ⟨terminal i, by exact hterminal_ne i⟩
            ⟨terminal j, by exact hterminal_ne j⟩) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ ((stem i).map B.hom).support ∧ z ≠ (root : V)}
        {z : V | z ∈ ((stem j).map B.hom).support ∧ z ≠ (root : V)} :=
  Subgraph.walk_family_mapped_punctured_supports_disjoint
    (G := G) (B := B) stem
    (walk_family_punctured_supports_disjoint_of_delete_root_unreachable
      (G := B.coe) (root := root) (terminal := terminal)
      stem hterminal_ne hstem_path hunreachable)

theorem Walk.mem_internalVertices_map_iff_of_injective
    {W : Type*} {G' : SimpleGraph W}
    (f : G →g G')
    (hf : Function.Injective f)
    {u v : V}
    (p : G.Walk u v)
    {z : W} :
    z ∈ Walk.InternalVertices (p.map f) ↔
      Exists fun z₀ : V => z₀ ∈ Walk.InternalVertices p ∧ f z₀ = z := by
  constructor
  · intro hz
    rw [Walk.InternalVertices, SimpleGraph.Walk.support_map] at hz
    rcases hz with ⟨hz_support, hz_ne_u, hz_ne_v⟩
    rcases List.mem_map.mp hz_support with ⟨z₀, hz₀_support, hz₀_eq⟩
    refine ⟨z₀, ⟨hz₀_support, ?_, ?_⟩, hz₀_eq⟩
    · intro hz₀u
      exact hz_ne_u (hz₀_eq.symm.trans (congrArg f hz₀u))
    · intro hz₀v
      exact hz_ne_v (hz₀_eq.symm.trans (congrArg f hz₀v))
  · rintro ⟨z₀, hz₀, hz₀_eq⟩
    rw [Walk.InternalVertices, SimpleGraph.Walk.support_map]
    refine ⟨?_, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨z₀, hz₀.1, hz₀_eq⟩
    · intro hzu
      exact hz₀.2.1 (hf (hz₀_eq.trans hzu))
    · intro hzv
      exact hz₀.2.2 (hf (hz₀_eq.trans hzv))

theorem Walk.internalVertices_mapLe
    {G' : SimpleGraph V}
    (h : G ≤ G')
    {u v : V}
    (p : G.Walk u v) :
    Walk.InternalVertices (p.mapLe h) = Walk.InternalVertices p := by
  ext z
  change z ∈ Walk.InternalVertices (p.map (SimpleGraph.Hom.ofLE h)) ↔
    z ∈ Walk.InternalVertices p
  rw [Walk.mem_internalVertices_map_iff_of_injective
    (SimpleGraph.Hom.ofLE h) Function.injective_id p]
  constructor
  · rintro ⟨z₀, hz₀, hz₀_eq⟩
    simpa [SimpleGraph.Hom.ofLE_apply] using hz₀_eq ▸ hz₀
  · intro hz
    exact ⟨z, hz, by simp [SimpleGraph.Hom.ofLE_apply]⟩

theorem Walk.internalVertices_transfer
    {H : SimpleGraph V}
    {u v : V}
    (p : G.Walk u v)
    (hp : forall e : Sym2 V, e ∈ p.edges -> e ∈ H.edgeSet) :
    Walk.InternalVertices (p.transfer H hp) = Walk.InternalVertices p := by
  ext z
  simp [Walk.InternalVertices]

theorem Walk.toSubgraph_le_of_isSubwalk
    {u v u' v' : V}
    {p : G.Walk u v}
    {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) :
    p.toSubgraph ≤ q.toSubgraph := by
  rcases hpq with ⟨ru, rv, rfl⟩
  rw [SimpleGraph.Walk.toSubgraph_append, SimpleGraph.Walk.toSubgraph_append]
  exact le_trans
    (show p.toSubgraph ≤ ru.toSubgraph ⊔ p.toSubgraph from le_sup_right)
    (show ru.toSubgraph ⊔ p.toSubgraph ≤ (ru.toSubgraph ⊔ p.toSubgraph) ⊔ rv.toSubgraph
      from le_sup_left)

theorem Walk.toSubgraph_takeUntil_le
    [DecidableEq V]
    {u v w : V}
    (p : G.Walk u v)
    (hw : w ∈ p.support) :
    (p.takeUntil w hw).toSubgraph ≤ p.toSubgraph :=
  Walk.toSubgraph_le_of_isSubwalk (SimpleGraph.Walk.isSubwalk_takeUntil p hw)

theorem Walk.toSubgraph_dropUntil_le
    [DecidableEq V]
    {u v w : V}
    (p : G.Walk u v)
    (hw : w ∈ p.support) :
    (p.dropUntil w hw).toSubgraph ≤ p.toSubgraph :=
  Walk.toSubgraph_le_of_isSubwalk (SimpleGraph.Walk.isSubwalk_dropUntil p hw)

theorem Walk.toSubgraph_takeUntil_sup_dropUntil_eq
    [DecidableEq V]
    {u v w : V}
    (p : G.Walk u v)
    (hw : w ∈ p.support) :
    (p.takeUntil w hw).toSubgraph ⊔ (p.dropUntil w hw).toSubgraph =
      p.toSubgraph := by
  rw [← SimpleGraph.Walk.toSubgraph_append]
  rw [SimpleGraph.Walk.take_spec p hw]

theorem Walk.mem_support_takeUntil_or_dropUntil_of_mem_support
    [DecidableEq V]
    {u v w z : V}
    (p : G.Walk u v)
    (hw : w ∈ p.support)
    (hz : z ∈ p.support) :
    z ∈ (p.takeUntil w hw).support ∨
      z ∈ (p.dropUntil w hw).support := by
  have hz_split :
      z ∈ ((p.takeUntil w hw).append (p.dropUntil w hw)).support := by
    simpa [SimpleGraph.Walk.take_spec p hw] using hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz_split
  exact hz_split

theorem Walk.toSubgraph_takeUntil_le_of_le
    [DecidableEq V]
    {H : G.Subgraph}
    {u v w : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H)
    (hw : w ∈ p.support) :
    (p.takeUntil w hw).toSubgraph ≤ H :=
  le_trans (Walk.toSubgraph_takeUntil_le p hw) hp_le

theorem Walk.toSubgraph_dropUntil_le_of_le
    [DecidableEq V]
    {H : G.Subgraph}
    {u v w : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H)
    (hw : w ∈ p.support) :
    (p.dropUntil w hw).toSubgraph ≤ H :=
  le_trans (Walk.toSubgraph_dropUntil_le p hw) hp_le

theorem Walk.segmentBetween_toSubgraph_le
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y) :
    (Walk.segmentBetween p hx hy hxy).toSubgraph ≤ p.toSubgraph := by
  unfold Walk.segmentBetween
  exact le_trans
    (Walk.toSubgraph_takeUntil_le _ _)
    (Walk.toSubgraph_dropUntil_le p hx)

theorem Walk.support_subset_of_toSubgraph_le
    {H : G.Subgraph}
    {u v : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H) :
    {z : V | z ∈ p.support} ⊆ H.verts := by
  intro z hz
  exact hp_le.left (by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    exact hz)

theorem Walk.internalVertices_subset_of_toSubgraph_le
    {H : G.Subgraph}
    {u v : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H) :
    Walk.InternalVertices p ⊆ H.verts := by
  intro z hz
  exact Walk.support_subset_of_toSubgraph_le hp_le hz.1

def Walk.liftToSubgraph
    {H : G.Subgraph}
    {u v : V}
    (p : G.Walk u v)
    (hp_le : p.toSubgraph ≤ H) :
    H.coe.Walk
      ⟨u, Walk.support_subset_of_toSubgraph_le hp_le p.start_mem_support⟩
      ⟨v, Walk.support_subset_of_toSubgraph_le hp_le p.end_mem_support⟩ :=
  p.mapToSubgraph.map (SimpleGraph.Subgraph.inclusion hp_le)

theorem Walk.map_liftToSubgraph_hom
    {H : G.Subgraph}
    {u v : V}
    (p : G.Walk u v)
    (hp_le : p.toSubgraph ≤ H) :
    (Walk.liftToSubgraph p hp_le).map H.hom = p := by
  change ((p.mapToSubgraph.map (SimpleGraph.Subgraph.inclusion hp_le)).map H.hom) = p
  rw [SimpleGraph.Walk.map_map]
  convert p.map_mapToSubgraph_hom using 1

theorem Walk.liftToSubgraph_isPath
    {H : G.Subgraph}
    {u v : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H)
    (hp : p.IsPath) :
    (Walk.liftToSubgraph p hp_le).IsPath := by
  apply SimpleGraph.Walk.IsPath.of_map (f := H.hom)
  simpa [Walk.map_liftToSubgraph_hom p hp_le] using hp

theorem Walk.mem_support_liftToSubgraph_iff
    {H : G.Subgraph}
    {u v : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H)
    {z : H.verts} :
    z ∈ (Walk.liftToSubgraph p hp_le).support ↔ (z : V) ∈ p.support := by
  constructor
  · intro hz
    have hz_map :
        (z : V) ∈ ((Walk.liftToSubgraph p hp_le).map H.hom).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    simpa [Walk.map_liftToSubgraph_hom p hp_le] using hz_map
  · intro hz
    have hz_map :
        (z : V) ∈ ((Walk.liftToSubgraph p hp_le).map H.hom).support := by
      simpa [Walk.map_liftToSubgraph_hom p hp_le] using hz
    rw [SimpleGraph.Walk.support_map] at hz_map
    rcases List.mem_map.mp hz_map with ⟨z', hz', hz'_eq⟩
    have hzz' : z' = z := Subtype.ext hz'_eq
    simpa [hzz'] using hz'

theorem Subgraph.Connected.exists_path_between
    {H : G.Subgraph}
    (hH : H.coe.Connected)
    {u v : V}
    (hu : u ∈ H.verts)
    (hv : v ∈ H.verts) :
    Exists fun p : G.Walk u v =>
      p.IsPath ∧ p.toSubgraph ≤ H := by
  let uH : H.verts := ⟨u, hu⟩
  let vH : H.verts := ⟨v, hv⟩
  obtain ⟨pH, hpH⟩ := hH.exists_isPath uH vH
  let p : G.Walk u v := pH.map H.hom
  refine ⟨p, ?_, ?_⟩
  · exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hpH
  · simpa [p] using Walk.map_subgraph_toSubgraph_le pH

theorem Subgraph.Connected.exists_path_between_support_subset
    {H : G.Subgraph}
    (hH : H.coe.Connected)
    {u v : V}
    (hu : u ∈ H.verts)
    (hv : v ∈ H.verts) :
    Exists fun p : G.Walk u v =>
      p.IsPath ∧ (forall x : V, x ∈ p.support -> x ∈ H.verts) := by
  obtain ⟨p, hp, hp_le⟩ :=
    Subgraph.Connected.exists_path_between hH hu hv
  exact ⟨p, hp, by
    intro x hx
    exact hp_le.left (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph])⟩

theorem Subgraph.Connected.adj_of_verts_subset_pair
    {H : G.Subgraph}
    (hH : H.coe.Connected)
    {u v : V}
    (hu : u ∈ H.verts)
    (hv : v ∈ H.verts)
    (huv : u ≠ v)
    (hverts : H.verts ⊆ ({u, v} : Set V)) :
    G.Adj u v := by
  classical
  let uH : H.verts := ⟨u, hu⟩
  let vH : H.verts := ⟨v, hv⟩
  let p : H.coe.Walk uH vH := Classical.choice (hH uH vH)
  have hp : G.Adj (uH : V) (vH : V) := by
    have huH_ne_vH : uH ≠ vH := by
      intro h
      exact huv (congrArg Subtype.val h)
    obtain ⟨w, huw, _tail, _hp_eq⟩ :=
      SimpleGraph.Walk.exists_eq_cons_of_ne (G := H.coe) huH_ne_vH p
    have hw_cases : (w : V) = u ∨ (w : V) = v := by
      have hw_mem : (w : V) ∈ H.verts := w.property
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hverts hw_mem
    rcases hw_cases with hwu | hwv
    · have hw_eq : w = uH := Subtype.ext hwu
      exact False.elim (huw.ne hw_eq.symm)
    · have hG : G.Adj (uH : V) (w : V) := H.adj_sub huw
      simpa [hwv] using hG
  simpa [uH, vH] using hp

theorem fin4_map_into_set_ncard_le_two_has_two_values
    [Fintype V]
    {A : Set V}
    (a : Fin 4 -> V)
    (ha : forall i : Fin 4, a i ∈ A)
    (hcard : A.ncard <= 2) :
    Exists fun u : V =>
      Exists fun v : V =>
        u ∈ A ∧ v ∈ A ∧ forall i : Fin 4, a i = u ∨ a i = v := by
  classical
  have hcases : A.ncard = 0 ∨ A.ncard = 1 ∨ A.ncard = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hA_empty : A = ∅ := by
      simpa [h0] using (Set.ncard_eq_zero (s := A))
    exact False.elim (by simpa [hA_empty] using ha (0 : Fin 4))
  · rcases Set.ncard_eq_one.mp h1 with ⟨u, hA⟩
    refine ⟨u, u, ?_, ?_, ?_⟩
    · rw [hA]
      simp
    · rw [hA]
      simp
    · intro i
      left
      exact Set.mem_singleton_iff.mp (by simpa [hA] using ha i)
  · rcases Set.ncard_eq_two.mp h2 with ⟨u, v, _huv, hA⟩
    refine ⟨u, v, ?_, ?_, ?_⟩
    · rw [hA]
      simp
    · rw [hA]
      simp
    · intro i
      have hai : a i ∈ ({u, v} : Set V) := by
        simpa [hA] using ha i
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hai

theorem fin4_range_ncard_ge_three_of_not_two_values
    [Fintype V]
    (a : Fin 4 -> V)
    (hnot_two :
      Not (Exists fun u : V =>
        Exists fun v : V => forall i : Fin 4, a i = u ∨ a i = v)) :
    3 <= (Set.range a).ncard := by
  classical
  by_contra hlt
  have hle : (Set.range a).ncard <= 2 := by omega
  obtain ⟨u, v, _hu, _hv, hvalues⟩ :=
    fin4_map_into_set_ncard_le_two_has_two_values
      (V := V) (A := Set.range a) a (fun i => ⟨i, rfl⟩) hle
  exact hnot_two ⟨u, v, hvalues⟩

theorem fin4_range_ncard_ge_three_of_not_two_values_in_set
    [Fintype V]
    {A : Set V}
    (a : Fin 4 -> V)
    (ha : forall i : Fin 4, a i ∈ A)
    (hnot_two :
      Not (Exists fun u : V =>
        Exists fun v : V =>
          u ∈ A ∧ v ∈ A ∧ forall i : Fin 4, a i = u ∨ a i = v)) :
    3 <= (Set.range a).ncard := by
  classical
  by_contra hlt
  have hle : (Set.range a).ncard <= 2 := by omega
  obtain ⟨u, v, hu_range, hv_range, hvalues⟩ :=
    fin4_map_into_set_ncard_le_two_has_two_values
      (V := V) (A := Set.range a) a (fun i => ⟨i, rfl⟩) hle
  have huA : u ∈ A := by
    rcases hu_range with ⟨i, rfl⟩
    exact ha i
  have hvA : v ∈ A := by
    rcases hv_range with ⟨i, rfl⟩
    exact ha i
  exact hnot_two ⟨u, v, huA, hvA, hvalues⟩

theorem fin4_exists_three_pairwise_distinct_values_of_range_ncard_ge_three
    [Fintype V]
    (a : Fin 4 -> V)
    (hcard : 3 <= (Set.range a).ncard) :
    Exists fun i : Fin 4 =>
      Exists fun j : Fin 4 =>
        Exists fun k : Fin 4 =>
          a i ≠ a j ∧ a i ≠ a k ∧ a j ≠ a k := by
  classical
  have htwo : 2 < (Set.range a).ncard := by omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    (Set.two_lt_ncard (s := Set.range a)).mp htwo
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  rcases hz with ⟨k, rfl⟩
  exact ⟨i, j, k, hxy, hxz, hyz⟩

theorem Walk.IsPath.start_notMem_tail_support
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have hnodup : (u :: p.support.tail).Nodup := by
    rw [SimpleGraph.Walk.cons_tail_support]
    exact hp.support_nodup
  exact (List.nodup_cons.mp hnodup).1

theorem Walk.IsPath.append_of_support_inter_eq_endpoint
    {u v w : V}
    {p : G.Walk u v}
    {q : G.Walk v w}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hinter : forall x : V, x ∈ p.support -> x ∈ q.support -> x = v) :
    (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
  exact hp.support_nodup.append hq.support_nodup.tail (by
    intro x hx_p hx_q_tail
    have hx_q : x ∈ q.support := List.mem_of_mem_tail hx_q_tail
    have hx_eq : x = v := hinter x hx_p hx_q
    have hv_tail : v ∈ q.support.tail := by
      simpa [hx_eq] using hx_q_tail
    exact Walk.IsPath.start_notMem_tail_support hq hv_tail)


end Schematic.Math.GraphTheory
