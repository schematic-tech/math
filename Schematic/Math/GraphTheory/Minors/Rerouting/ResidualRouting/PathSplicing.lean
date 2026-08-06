import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualRouting.ResidualCuts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
theorem PartialThreeVertexLinkage.hasPartial_succ_of_path_avoids_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pNew : G.Walk (left iNew) (right jNew))
    (hpNew : pNew.IsPath)
    (havoid :
      forall v : V, v ∈ pNew.support -> v ∉ L.usedVertices) :
    HasPartialThreeVertexLinkage G left right (n + 1) := by
  refine ⟨L.snocPath hiNew hjNew pNew hpNew ?_⟩
  intro k
  rw [Set.disjoint_left]
  intro v hvL hvp
  exact havoid v hvp ⟨k, hvL⟩

noncomputable def PartialThreeVertexLinkage.spliceOnePath
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOldToNew : G.Walk (left (L.leftIndex 0)) (right jNew))
    (hpOldToNew : pOldToNew.IsPath)
    (pNewToOld : G.Walk (left iNew) (right (L.rightIndex 0)))
    (hpNewToOld : pNewToOld.IsPath)
    (hdisj : Disjoint {v : V | v ∈ pOldToNew.support}
      {v : V | v ∈ pNewToOld.support}) :
    PartialThreeVertexLinkage G left right 2 where
  leftIndex k := if k = (0 : Fin 2) then L.leftIndex 0 else iNew
  rightIndex k := if k = (0 : Fin 2) then jNew else L.rightIndex 0
  leftIndex_injective := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢
    · exfalso
      exact hiNew ⟨0, by simpa using h⟩
    · exfalso
      exact hiNew ⟨0, by simpa using h.symm⟩
  rightIndex_injective := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢
    · exfalso
      exact hjNew ⟨0, by simpa using h.symm⟩
    · exfalso
      exact hjNew ⟨0, by simpa using h⟩
  path k := by
    by_cases hk : k = (0 : Fin 2)
    · exact pOldToNew.copy (by simp [hk]) (by simp [hk])
    · exact pNewToOld.copy (by simp [hk]) (by simp [hk])
  isPath k := by
    by_cases hk : k = (0 : Fin 2)
    · simpa [hk]
    · simpa [hk]
  pairwise_vertex_disjoint := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · exact hdisj
    · rw [disjoint_comm]
      exact hdisj

theorem Walk.toPath_support_disjoint
    [DecidableEq V]
    {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (hdisj : Disjoint {v : V | v ∈ p.support}
      {v : V | v ∈ q.support}) :
    Disjoint {v : V | v ∈ ((p.toPath : G.Walk a b).support)}
      {v : V | v ∈ ((q.toPath : G.Walk c d).support)} := by
  rw [Set.disjoint_left]
  intro v hvp hvq
  exact Set.disjoint_left.mp hdisj
    (SimpleGraph.Walk.support_toPath_subset p hvp)
    (SimpleGraph.Walk.support_toPath_subset q hvq)

theorem Walk.toPath_support_disjoint_left
    [DecidableEq V]
    {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (hdisj : Disjoint {v : V | v ∈ p.support}
      {v : V | v ∈ q.support}) :
    Disjoint {v : V | v ∈ ((p.toPath : G.Walk a b).support)}
      {v : V | v ∈ q.support} := by
  rw [Set.disjoint_left]
  intro v hvp hvq
  exact Set.disjoint_left.mp hdisj
    (SimpleGraph.Walk.support_toPath_subset p hvp) hvq

theorem Walk.toPath_support_disjoint_right
    [DecidableEq V]
    {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (hdisj : Disjoint {v : V | v ∈ p.support}
      {v : V | v ∈ q.support}) :
    Disjoint {v : V | v ∈ p.support}
      {v : V | v ∈ ((q.toPath : G.Walk c d).support)} := by
  rw [Set.disjoint_left]
  intro v hvp hvq
  exact Set.disjoint_left.mp hdisj hvp
    (SimpleGraph.Walk.support_toPath_subset q hvq)

theorem Walk.support_append_disjoint_append
    {a b c d e f : V}
    {p : G.Walk a b} {p' : G.Walk b c}
    {q : G.Walk d e} {q' : G.Walk e f}
    (h11 : Disjoint {v : V | v ∈ p.support}
      {v : V | v ∈ q.support})
    (h12 : Disjoint {v : V | v ∈ p.support}
      {v : V | v ∈ q'.support})
    (h21 : Disjoint {v : V | v ∈ p'.support}
      {v : V | v ∈ q.support})
    (h22 : Disjoint {v : V | v ∈ p'.support}
      {v : V | v ∈ q'.support}) :
    Disjoint {v : V | v ∈ (p.append p').support}
      {v : V | v ∈ (q.append q').support} := by
  rw [Set.disjoint_left]
  intro v hv hw
  simp only [Set.mem_setOf_eq] at hv hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact Set.disjoint_left.mp h11 hv hw
  · exact Set.disjoint_left.mp h12 hv hw
  · exact Set.disjoint_left.mp h21 hv hw
  · exact Set.disjoint_left.mp h22 hv hw

theorem Walk.support_append_disjoint
    {a b c d e : V}
    {p : G.Walk a b} {p' : G.Walk b c} {q : G.Walk d e}
    (h1 : Disjoint {v : V | v ∈ p.support} {v : V | v ∈ q.support})
    (h2 : Disjoint {v : V | v ∈ p'.support} {v : V | v ∈ q.support}) :
    Disjoint {v : V | v ∈ (p.append p').support}
      {v : V | v ∈ q.support} := by
  rw [Set.disjoint_left]
  intro v hv hq
  simp only [Set.mem_setOf_eq] at hv hq
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · exact Set.disjoint_left.mp h1 hv hq
  · exact Set.disjoint_left.mp h2 hv hq

theorem Walk.support_disjoint_append
    {a b c d e : V}
    {p : G.Walk a b} {q : G.Walk c d} {q' : G.Walk d e}
    (h1 : Disjoint {v : V | v ∈ p.support} {v : V | v ∈ q.support})
    (h2 : Disjoint {v : V | v ∈ p.support} {v : V | v ∈ q'.support}) :
    Disjoint {v : V | v ∈ p.support}
      {v : V | v ∈ (q.append q').support} := by
  rw [Set.disjoint_left]
  intro v hp hv
  simp only [Set.mem_setOf_eq] at hp hv
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · exact Set.disjoint_left.mp h1 hp hv
  · exact Set.disjoint_left.mp h2 hp hv

theorem Walk.support_append_append_disjoint_append_append
    {a b c d e f g h : V}
    {p₁ : G.Walk a b} {p₂ : G.Walk b c} {p₃ : G.Walk c d}
    {q₁ : G.Walk e f} {q₂ : G.Walk f g} {q₃ : G.Walk g h}
    (h11 : Disjoint {x : V | x ∈ p₁.support}
      {x : V | x ∈ q₁.support})
    (h12 : Disjoint {x : V | x ∈ p₁.support}
      {x : V | x ∈ q₂.support})
    (h13 : Disjoint {x : V | x ∈ p₁.support}
      {x : V | x ∈ q₃.support})
    (h21 : Disjoint {x : V | x ∈ p₂.support}
      {x : V | x ∈ q₁.support})
    (h22 : Disjoint {x : V | x ∈ p₂.support}
      {x : V | x ∈ q₂.support})
    (h23 : Disjoint {x : V | x ∈ p₂.support}
      {x : V | x ∈ q₃.support})
    (h31 : Disjoint {x : V | x ∈ p₃.support}
      {x : V | x ∈ q₁.support})
    (h32 : Disjoint {x : V | x ∈ p₃.support}
      {x : V | x ∈ q₂.support})
    (h33 : Disjoint {x : V | x ∈ p₃.support}
      {x : V | x ∈ q₃.support}) :
    Disjoint {x : V | x ∈ ((p₁.append p₂).append p₃).support}
      {x : V | x ∈ ((q₁.append q₂).append q₃).support} := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [Set.mem_setOf_eq] at hx hy
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx
  rw [SimpleGraph.Walk.mem_support_append_iff] at hy
  rcases hx with hx12 | hx3
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hx12
    rcases hx12 with hx1 | hx2
    · rcases hy with hy12 | hy3
      · rw [SimpleGraph.Walk.mem_support_append_iff] at hy12
        rcases hy12 with hy1 | hy2
        · exact Set.disjoint_left.mp h11 hx1 hy1
        · exact Set.disjoint_left.mp h12 hx1 hy2
      · exact Set.disjoint_left.mp h13 hx1 hy3
    · rcases hy with hy12 | hy3
      · rw [SimpleGraph.Walk.mem_support_append_iff] at hy12
        rcases hy12 with hy1 | hy2
        · exact Set.disjoint_left.mp h21 hx2 hy1
        · exact Set.disjoint_left.mp h22 hx2 hy2
      · exact Set.disjoint_left.mp h23 hx2 hy3
  · rcases hy with hy12 | hy3
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hy12
      rcases hy12 with hy1 | hy2
      · exact Set.disjoint_left.mp h31 hx3 hy1
      · exact Set.disjoint_left.mp h32 hx3 hy2
    · exact Set.disjoint_left.mp h33 hx3 hy3

theorem Walk.idxOf_lt_idxOf_of_ne_of_le
    [DecidableEq V]
    {a b x y : V} {p : G.Walk a b}
    (hx : x ∈ p.support)
    (hxy : x ≠ y)
    (hle : p.support.idxOf x <= p.support.idxOf y) :
    p.support.idxOf x < p.support.idxOf y := by
  by_contra hnot
  have heq_idx : p.support.idxOf x = p.support.idxOf y := by omega
  exact hxy ((List.idxOf_inj hx).mp heq_idx)

def Walk.segment
    [DecidableEq V]
    {a b u v : V} (p : G.Walk a b)
    (hu : u ∈ p.support)
    (hv : v ∈ p.support)
    (hle : p.support.idxOf u <= p.support.idxOf v) :
    G.Walk u v :=
  (p.dropUntil u hu).takeUntil v
    (Walk.mem_dropUntil_of_idxOf_le (G := G) hu hv hle)

theorem Walk.IsPath.segment
    [DecidableEq V]
    {a b u v : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hu : u ∈ p.support)
    (hv : v ∈ p.support)
    (hle : p.support.idxOf u <= p.support.idxOf v) :
    (Walk.segment (G := G) p hu hv hle).IsPath := by
  dsimp [Walk.segment]
  exact (hp.dropUntil hu).takeUntil
    (Walk.mem_dropUntil_of_idxOf_le (G := G) hu hv hle)

theorem Walk.segment_support_subset
    [DecidableEq V]
    {a b u v : V} (p : G.Walk a b)
    (hu : u ∈ p.support)
    (hv : v ∈ p.support)
    (hle : p.support.idxOf u <= p.support.idxOf v) :
    (Walk.segment (G := G) p hu hv hle).support ⊆ p.support := by
  intro x hx
  exact SimpleGraph.Walk.support_dropUntil_subset p hu
    (SimpleGraph.Walk.support_takeUntil_subset
      (p.dropUntil u hu)
      (Walk.mem_dropUntil_of_idxOf_le (G := G) hu hv hle)
      hx)

theorem List.idxOf_le_idxOf_of_mem_drop_idxOf_le
    {α : Type u} [DecidableEq α]
    {l : List α} (hnodup : l.Nodup) {n : Nat} {x y : α}
    (hx : x ∈ l.drop n) (hy : y ∈ l.drop n)
    (hxy : (l.drop n).idxOf x <= (l.drop n).idxOf y) :
    l.idxOf x <= l.idxOf y := by
  let ix : Nat := (l.drop n).idxOf x
  let iy : Nat := (l.drop n).idxOf y
  have hix_len : ix < (l.drop n).length := by
    simpa [ix] using List.idxOf_lt_length_of_mem hx
  have hiy_len : iy < (l.drop n).length := by
    simpa [iy] using List.idxOf_lt_length_of_mem hy
  have hix_orig : n + ix < l.length := by
    rw [List.length_drop] at hix_len
    omega
  have hiy_orig : n + iy < l.length := by
    rw [List.length_drop] at hiy_len
    omega
  have hx_get : l[n + ix]'hix_orig = x := by
    have hx_drop : (l.drop n)[ix]'hix_len = x := by
      simp [ix]
    simpa only [List.getElem_drop] using hx_drop
  have hy_get : l[n + iy]'hiy_orig = y := by
    have hy_drop : (l.drop n)[iy]'hiy_len = y := by
      simp [iy]
    simpa only [List.getElem_drop] using hy_drop
  have hx_idx : l.idxOf x = n + ix := by
    rw [← hx_get]
    exact hnodup.idxOf_getElem (n + ix) hix_orig
  have hy_idx : l.idxOf y = n + iy := by
    rw [← hy_get]
    exact hnodup.idxOf_getElem (n + iy) hiy_orig
  rw [hx_idx, hy_idx]
  have hxy' : ix <= iy := by
    simpa [ix, iy] using hxy
  omega

theorem Walk.IsPath.idxOf_le_of_mem_segment
    [DecidableEq V]
    {a b u v x : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hu : u ∈ p.support)
    (hv : v ∈ p.support)
    (hle : p.support.idxOf u <= p.support.idxOf v)
    (hx : x ∈ (Walk.segment (G := G) p hu hv hle).support) :
    p.support.idxOf x <= p.support.idxOf v := by
  let q : G.Walk u b := p.dropUntil u hu
  have hvq : v ∈ q.support := by
    simpa [q] using Walk.mem_dropUntil_of_idxOf_le (G := G) hu hv hle
  have hxq : x ∈ q.support := by
    simpa [Walk.segment, q] using
      SimpleGraph.Walk.support_takeUntil_subset q hvq hx
  have hx_le_v_q : q.support.idxOf x <= q.support.idxOf v := by
    simpa [Walk.segment, q] using
      Walk.idxOf_le_of_mem_takeUntil (G := G) hvq hx
  change x ∈ (p.dropUntil u hu).support at hxq
  change v ∈ (p.dropUntil u hu).support at hvq
  change (p.dropUntil u hu).support.idxOf x <=
    (p.dropUntil u hu).support.idxOf v at hx_le_v_q
  rw [SimpleGraph.Walk.dropUntil_eq_drop,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min] at hxq hvq hx_le_v_q
  exact
    List.idxOf_le_idxOf_of_mem_drop_idxOf_le
      hp.support_nodup hxq hvq hx_le_v_q

theorem Walk.IsPath.idxOf_left_le_of_mem_segment
    [DecidableEq V]
    {a b u v x : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hu : u ∈ p.support)
    (hv : v ∈ p.support)
    (hle : p.support.idxOf u <= p.support.idxOf v)
    (hx : x ∈ (Walk.segment (G := G) p hu hv hle).support) :
    p.support.idxOf u <= p.support.idxOf x := by
  have hx_support : x ∈ p.support :=
    Walk.segment_support_subset (G := G) p hu hv hle hx
  have hx_drop : x ∈ (p.dropUntil u hu).support := by
    dsimp [Walk.segment] at hx
    exact
      SimpleGraph.Walk.support_takeUntil_subset
        (p.dropUntil u hu)
        (Walk.mem_dropUntil_of_idxOf_le (G := G) hu hv hle)
        hx
  by_contra hnot
  have hlt : p.support.idxOf x < p.support.idxOf u := by omega
  exact
    (Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
      (G := G) hp hu hx_support hlt) hx_drop

theorem Walk.IsPath.not_mem_segment_of_idxOf_right_lt
    [DecidableEq V]
    {a b u v x : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hu : u ∈ p.support)
    (hv : v ∈ p.support)
    (hle : p.support.idxOf u <= p.support.idxOf v)
    (hlt : p.support.idxOf v < p.support.idxOf x) :
    x ∉ (Walk.segment (G := G) p hu hv hle).support := by
  intro hxseg
  have hx_le_v :
      p.support.idxOf x <= p.support.idxOf v :=
    Walk.IsPath.idxOf_le_of_mem_segment
      (G := G) hp hu hv hle hxseg
  omega

theorem Walk.IsPath.segment_support_disjoint_of_right_lt_left
    [DecidableEq V]
    {a b u₁ v₁ u₂ v₂ : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hu₁ : u₁ ∈ p.support)
    (hv₁ : v₁ ∈ p.support)
    (hu₂ : u₂ ∈ p.support)
    (hv₂ : v₂ ∈ p.support)
    (hle₁ : p.support.idxOf u₁ <= p.support.idxOf v₁)
    (hle₂ : p.support.idxOf u₂ <= p.support.idxOf v₂)
    (hsep : p.support.idxOf v₁ < p.support.idxOf u₂) :
    Disjoint
      {x : V | x ∈ (Walk.segment (G := G) p hu₁ hv₁ hle₁).support}
      {x : V | x ∈ (Walk.segment (G := G) p hu₂ hv₂ hle₂).support} := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hx_le_v₁ :
      p.support.idxOf x <= p.support.idxOf v₁ :=
    Walk.IsPath.idxOf_le_of_mem_segment
      (G := G) hp hu₁ hv₁ hle₁ hx₁
  have hu₂_le_x :
      p.support.idxOf u₂ <= p.support.idxOf x :=
    Walk.IsPath.idxOf_left_le_of_mem_segment
      (G := G) hp hu₂ hv₂ hle₂ hx₂
  omega

theorem Walk.IsPath.takeUntil_support_disjoint_segment_of_idxOf_lt
    [DecidableEq V]
    {a b w u v : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hw : w ∈ p.support)
    (hu : u ∈ p.support)
    (hv : v ∈ p.support)
    (huv : p.support.idxOf u <= p.support.idxOf v)
    (hsep : p.support.idxOf w < p.support.idxOf u) :
    Disjoint {x : V | x ∈ (p.takeUntil w hw).support}
      {x : V | x ∈ (Walk.segment (G := G) p hu hv huv).support} := by
  rw [Set.disjoint_left]
  intro x hxTake hxSeg
  have hx_support : x ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hw hxTake
  have hx_le_w : p.support.idxOf x <= p.support.idxOf w :=
    Walk.idxOf_le_of_mem_takeUntil (G := G) hw hxTake
  have hu_le_x : p.support.idxOf u <= p.support.idxOf x :=
    Walk.IsPath.idxOf_left_le_of_mem_segment
      (G := G) hp hu hv huv hxSeg
  omega

theorem Walk.IsPath.segment_support_disjoint_dropUntil_of_idxOf_lt
    [DecidableEq V]
    {a b u v w : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hu : u ∈ p.support)
    (hv : v ∈ p.support)
    (hw : w ∈ p.support)
    (huv : p.support.idxOf u <= p.support.idxOf v)
    (hsep : p.support.idxOf v < p.support.idxOf w) :
    Disjoint {x : V | x ∈ (Walk.segment (G := G) p hu hv huv).support}
      {x : V | x ∈ (p.dropUntil w hw).support} := by
  rw [Set.disjoint_left]
  intro x hxSeg hxDrop
  have hx_support : x ∈ p.support :=
    Walk.segment_support_subset (G := G) p hu hv huv hxSeg
  have hx_le_v : p.support.idxOf x <= p.support.idxOf v :=
    Walk.IsPath.idxOf_le_of_mem_segment
      (G := G) hp hu hv huv hxSeg
  exact
    (Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
      (G := G) hp hw hx_support (lt_of_le_of_lt hx_le_v hsep))
      hxDrop

theorem Walk.IsPath.takeUntil_support_disjoint_dropUntil_of_idxOf_lt
    [DecidableEq V]
    {a b w v : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hw : w ∈ p.support)
    (hv : v ∈ p.support)
    (hlt : p.support.idxOf w < p.support.idxOf v) :
    Disjoint {x : V | x ∈ (p.takeUntil w hw).support}
      {x : V | x ∈ (p.dropUntil v hv).support} := by
  rw [Set.disjoint_left]
  intro x hx_take hx_drop
  have hx_support : x ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hw hx_take
  have hx_le_w : p.support.idxOf x <= p.support.idxOf w :=
    Walk.idxOf_le_of_mem_takeUntil (G := G) hw hx_take
  exact (Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
    (G := G) hp hv hx_support (lt_of_le_of_lt hx_le_w hlt)) hx_drop

theorem PartialThreeVertexLinkage.walk_support_disjoint_of_avoids_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {a b c d hit : V} {p : G.Walk a b} {q : G.Walk c d}
    (havoid :
      forall x : V, x ∈ p.support -> x ∉ L.usedVertices ∨ x = hit)
    (hq_used : forall x : V, x ∈ q.support -> x ∈ L.usedVertices)
    (hhit_q : hit ∉ q.support) :
    Disjoint {x : V | x ∈ p.support} {x : V | x ∈ q.support} := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  rcases havoid x hxp with hx_not_used | rfl
  · exact hx_not_used (hq_used x hxq)
  · exact hhit_q hxq

theorem PartialThreeVertexLinkage.walk_support_disjoint_of_avoids_usedVertices_two
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {a b c d hit₁ hit₂ : V} {p : G.Walk a b} {q : G.Walk c d}
    (havoid :
      forall x : V, x ∈ p.support ->
        x ∉ L.usedVertices ∨ x = hit₁ ∨ x = hit₂)
    (hq_used : forall x : V, x ∈ q.support -> x ∈ L.usedVertices)
    (hhit₁_q : hit₁ ∉ q.support)
    (hhit₂_q : hit₂ ∉ q.support) :
    Disjoint {x : V | x ∈ p.support} {x : V | x ∈ q.support} := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  rcases havoid x hxp with hx_not_used | hx_hit
  · exact hx_not_used (hq_used x hxq)
  · rcases hx_hit with rfl | rfl
    · exact hhit₁_q hxq
    · exact hhit₂_q hxq

theorem PartialThreeVertexLinkage.hasPartial_succ_of_arms_meet_unused
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    {vHit wHit x : V}
    (hvHitUsed : vHit ∈ L.usedVertices)
    (hwHitUsed : wHit ∈ L.usedVertices)
    (pIn : G.Walk (left iNew) vHit)
    (hpIn : pIn.IsPath)
    (hInAvoid :
      forall y : V, y ∈ pIn.support -> y ∉ L.usedVertices ∨ y = vHit)
    (pOut : G.Walk wHit (right jNew))
    (hpOut : pOut.IsPath)
    (hOutAvoid :
      forall y : V, y ∈ pOut.support -> y ∉ L.usedVertices ∨ y = wHit)
    (hxIn : x ∈ pIn.support)
    (hxOut : x ∈ pOut.support)
    (hxUnused : x ∉ L.usedVertices) :
    HasPartialThreeVertexLinkage G left right (n + 1) := by
  classical
  have hx_ne_v : x ≠ vHit := by
    intro hxv
    exact hxUnused (by simpa [hxv] using hvHitUsed)
  have hx_ne_w : x ≠ wHit := by
    intro hxw
    exact hxUnused (by simpa [hxw] using hwHitUsed)
  let pDirect : G.Walk (left iNew) (right jNew) :=
    (pIn.takeUntil x hxIn).append (pOut.dropUntil x hxOut)
  have hdirect_avoid :
      forall y : V, y ∈ pDirect.support -> y ∉ L.usedVertices := by
    intro y hy
    dsimp [pDirect] at hy
    rw [SimpleGraph.Walk.mem_support_append_iff] at hy
    rcases hy with hyIn | hyOut
    · have hyFull : y ∈ pIn.support :=
        SimpleGraph.Walk.support_takeUntil_subset pIn hxIn hyIn
      rcases hInAvoid y hyFull with hyNot | hyv
      · exact hyNot
      · subst y
        exact False.elim
          ((SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            hpIn hxIn hx_ne_v.symm) hyIn)
    · have hyFull : y ∈ pOut.support :=
        SimpleGraph.Walk.support_dropUntil_subset pOut hxOut hyOut
      rcases hOutAvoid y hyFull with hyNot | hyw
      · exact hyNot
      · subst y
        exact False.elim
          ((Walk.IsPath.start_not_mem_dropUntil_support_of_ne
            hpOut hxOut hx_ne_w) hyOut)
  exact
    L.hasPartial_succ_of_path_avoids_usedVertices hiNew hjNew
      (pDirect.toPath : G.Walk (left iNew) (right jNew))
      pDirect.toPath.property (by
        intro y hy
        exact hdirect_avoid y
          (SimpleGraph.Walk.support_toPath_subset pDirect hy))

theorem PartialThreeVertexLinkage.disjoint_of_arms_no_unused_meet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {vHit wHit : V}
    (hne : vHit ≠ wHit)
    {a b c d : V}
    (pIn : G.Walk a b)
    (hInAvoid :
      forall x : V, x ∈ pIn.support -> x ∉ L.usedVertices ∨ x = vHit)
    (pOut : G.Walk c d)
    (hOutAvoid :
      forall x : V, x ∈ pOut.support -> x ∉ L.usedVertices ∨ x = wHit)
    (hNoUnusedMeet :
      Not (Exists fun x : V =>
        x ∈ pIn.support ∧ x ∈ pOut.support ∧ x ∉ L.usedVertices)) :
    Disjoint {x : V | x ∈ pIn.support} {x : V | x ∈ pOut.support} := by
  rw [Set.disjoint_left]
  intro x hxIn hxOut
  simp only [Set.mem_setOf_eq] at hxIn hxOut
  rcases hInAvoid x hxIn with hxInUnused | hxv
  · exact hNoUnusedMeet ⟨x, hxIn, hxOut, hxInUnused⟩
  · rcases hOutAvoid x hxOut with hxOutUnused | hxw
    · exact hNoUnusedMeet ⟨x, hxIn, hxOut, hxOutUnused⟩
    · subst x
      exact hne hxw

theorem PartialThreeVertexLinkage.hasPartial_two_of_one_path_splice_walks
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOldToNew : G.Walk (left (L.leftIndex 0)) (right jNew))
    (pNewToOld : G.Walk (left iNew) (right (L.rightIndex 0)))
    (hdisj : Disjoint {v : V | v ∈ pOldToNew.support}
      {v : V | v ∈ pNewToOld.support}) :
    HasPartialThreeVertexLinkage G left right 2 := by
  refine ⟨L.spliceOnePath hiNew hjNew
    (pOldToNew.toPath : G.Walk (left (L.leftIndex 0)) (right jNew))
    pOldToNew.toPath.property
    (pNewToOld.toPath : G.Walk (left iNew) (right (L.rightIndex 0)))
    pNewToOld.toPath.property ?_⟩
  exact Walk.toPath_support_disjoint (G := G) hdisj

theorem PartialThreeVertexLinkage.hasPartial_two_of_replaced_one_path_and_new_path_walks
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOld : G.Walk (left (L.leftIndex 0)) (right (L.rightIndex 0)))
    (pNew : G.Walk (left iNew) (right jNew))
    (hdisj : Disjoint {v : V | v ∈ pOld.support}
      {v : V | v ∈ pNew.support}) :
    HasPartialThreeVertexLinkage G left right 2 := by
  classical
  let Lold : PartialThreeVertexLinkage G left right 1 :=
    PartialThreeVertexLinkage.ofOnePath (G := G)
      (left := left) (right := right)
      (i := L.leftIndex 0) (j := L.rightIndex 0)
      (pOld.toPath : G.Walk (left (L.leftIndex 0)) (right (L.rightIndex 0)))
      pOld.toPath.property
  have hiNewOld : iNew ∉ Set.range Lold.leftIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    exact hiNew ⟨0, by
      simpa [Lold, PartialThreeVertexLinkage.ofOnePath, hk0] using hk⟩
  have hjNewOld : jNew ∉ Set.range Lold.rightIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    exact hjNew ⟨0, by
      simpa [Lold, PartialThreeVertexLinkage.ofOnePath, hk0] using hk⟩
  refine ⟨Lold.snocPath hiNewOld hjNewOld
    (pNew.toPath : G.Walk (left iNew) (right jNew))
    pNew.toPath.property ?_⟩
  intro k
  have hk0 : k = 0 := Subsingleton.elim k 0
  simpa [Lold, PartialThreeVertexLinkage.ofOnePath, hk0] using
    Walk.toPath_support_disjoint (G := G) hdisj

theorem PartialThreeVertexLinkage.hasPartial_two_of_one_path_forward_bridge_splice_walks
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    {wExit vHit wHit vNext : V}
    (hwExit : wExit ∈ (L.path 0).support)
    (hvHit : vHit ∈ (L.path 0).support)
    (hwHit : wHit ∈ (L.path 0).support)
    (hvNext : vNext ∈ (L.path 0).support)
    (hmid : (L.path 0).support.idxOf vHit <=
      (L.path 0).support.idxOf wHit)
    (pIn : G.Walk (left iNew) vHit)
    (pBridge : G.Walk wExit vNext)
    (pOut : G.Walk wHit (right jNew))
    (hdisj :
      Disjoint
        {x : V |
          x ∈ (((L.path 0).takeUntil wExit hwExit).append pBridge |>.append
            ((L.path 0).dropUntil vNext hvNext)).support}
        {x : V |
          x ∈ ((pIn.append
            (Walk.segment (G := G) (L.path 0) hvHit hwHit hmid)).append
              pOut).support}) :
    HasPartialThreeVertexLinkage G left right 2 := by
  classical
  let pOld : G.Walk (left (L.leftIndex 0)) (right (L.rightIndex 0)) :=
    (((L.path 0).takeUntil wExit hwExit).append pBridge).append
      ((L.path 0).dropUntil vNext hvNext)
  let pMid : G.Walk vHit wHit :=
    Walk.segment (G := G) (L.path 0) hvHit hwHit hmid
  let pNew : G.Walk (left iNew) (right jNew) :=
    (pIn.append pMid).append pOut
  exact
    L.hasPartial_two_of_replaced_one_path_and_new_path_walks
      hiNew hjNew pOld pNew (by
        simpa [pOld, pNew, pMid] using hdisj)

theorem PartialThreeVertexLinkage.hasPartial_two_of_one_path_forward_bridge_splice
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    {wExit vHit wHit vNext : V}
    (hwExit : wExit ∈ (L.path 0).support)
    (hvHit : vHit ∈ (L.path 0).support)
    (hwHit : wHit ∈ (L.path 0).support)
    (hvNext : vNext ∈ (L.path 0).support)
    (hExitBefore : (L.path 0).support.idxOf wExit <
      (L.path 0).support.idxOf vHit)
    (hmid : (L.path 0).support.idxOf vHit <=
      (L.path 0).support.idxOf wHit)
    (hNextAfter : (L.path 0).support.idxOf wHit <
      (L.path 0).support.idxOf vNext)
    (pIn : G.Walk (left iNew) vHit)
    (pBridge : G.Walk wExit vNext)
    (pOut : G.Walk wHit (right jNew))
    (hInAvoid :
      forall x : V, x ∈ pIn.support -> x ∉ L.usedVertices ∨ x = vHit)
    (hBridgeAvoid :
      forall x : V, x ∈ pBridge.support ->
        x ∉ L.usedVertices ∨ x = wExit ∨ x = vNext)
    (hOutAvoid :
      forall x : V, x ∈ pOut.support -> x ∉ L.usedVertices ∨ x = wHit)
    (hInBridge :
      Disjoint {x : V | x ∈ pIn.support}
        {x : V | x ∈ pBridge.support})
    (hBridgeOut :
      Disjoint {x : V | x ∈ pBridge.support}
        {x : V | x ∈ pOut.support}) :
    HasPartialThreeVertexLinkage G left right 2 := by
  classical
  have hdisj :
      Disjoint
        {x : V |
          x ∈ (((L.path 0).takeUntil wExit hwExit).append pBridge |>.append
            ((L.path 0).dropUntil vNext hvNext)).support}
        {x : V |
          x ∈ ((pIn.append
            (Walk.segment (G := G) (L.path 0) hvHit hwHit hmid)).append
              pOut).support} := by
    let q : G.Walk (left (L.leftIndex 0)) (right (L.rightIndex 0)) :=
      L.path 0
    have hqpath : q.IsPath := by
      simpa [q] using L.isPath 0
    have hvq : vHit ∈ q.support := by
      simpa [q] using hvHit
    have hwq : wHit ∈ q.support := by
      simpa [q] using hwHit
    have hwExitq : wExit ∈ q.support := by
      simpa [q] using hwExit
    have hvNextq : vNext ∈ q.support := by
      simpa [q] using hvNext
    have hmid_q : q.support.idxOf vHit <= q.support.idxOf wHit := by
      simpa [q] using hmid
    have hNextAfter_q : q.support.idxOf wHit < q.support.idxOf vNext := by
      simpa [q] using hNextAfter
    let pTake : G.Walk (left (L.leftIndex 0)) wExit :=
      q.takeUntil wExit hwExitq
    let pMid : G.Walk vHit wHit :=
      Walk.segment (G := G) q hvq hwq hmid_q
    let pDrop : G.Walk vNext (right (L.rightIndex 0)) :=
      q.dropUntil vNext hvNextq
    have htake_used :
        forall x : V, x ∈ pTake.support -> x ∈ L.usedVertices := by
      intro x hx
      exact ⟨0, by
        simpa [q, pTake] using
          SimpleGraph.Walk.support_takeUntil_subset q hwExitq hx⟩
    have hmid_used :
        forall x : V, x ∈ pMid.support -> x ∈ L.usedVertices := by
      intro x hx
      exact ⟨0, by
        simpa [q, pMid] using
          Walk.segment_support_subset (G := G) q hvq hwq hmid_q hx⟩
    have hdrop_used :
        forall x : V, x ∈ pDrop.support -> x ∈ L.usedVertices := by
      intro x hx
      exact ⟨0, by
        simpa [q, pDrop] using
          SimpleGraph.Walk.support_dropUntil_subset q hvNextq hx⟩
    have hvHit_not_take : vHit ∉ pTake.support := by
      dsimp [pTake]
      exact Walk.not_mem_takeUntil_of_idxOf_lt
        (G := G) hwExitq (by simpa [q] using hExitBefore)
    have hwHit_not_take : wHit ∉ pTake.support := by
      dsimp [pTake]
      exact Walk.not_mem_takeUntil_of_idxOf_lt
        (G := G) hwExitq (by
          have hExit_lt_wHit :
              q.support.idxOf wExit < q.support.idxOf wHit := by
            have hExit_lt_vHit :
                q.support.idxOf wExit < q.support.idxOf vHit := by
              simpa [q] using hExitBefore
            omega
          exact hExit_lt_wHit)
    have hwExit_not_mid : wExit ∉ pMid.support := by
      intro hxmid
      have hxdrop :
          wExit ∈ (q.dropUntil vHit hvq).support := by
        dsimp [pMid, Walk.segment] at hxmid
        exact
          SimpleGraph.Walk.support_takeUntil_subset
            (q.dropUntil vHit hvq)
            (Walk.mem_dropUntil_of_idxOf_le (G := G) hvq hwq hmid_q)
            hxmid
      exact
        (Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
          (G := G) hqpath hvq hwExitq
          (by simpa [q] using hExitBefore)) hxdrop
    have hvNext_not_mid : vNext ∉ pMid.support := by
      dsimp [pMid]
      exact
        Walk.IsPath.not_mem_segment_of_idxOf_right_lt
          (G := G) hqpath hvq hwq hmid_q hNextAfter_q
    have hvHit_not_drop : vHit ∉ pDrop.support := by
      dsimp [pDrop]
      exact
        Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
          (G := G) hqpath hvNextq hvq (by omega)
    have hwHit_not_drop : wHit ∉ pDrop.support := by
      dsimp [pDrop]
      exact
        Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
          (G := G) hqpath hvNextq hwq hNextAfter_q
    have hTakeIn :
        Disjoint {x : V | x ∈ pTake.support}
          {x : V | x ∈ pIn.support} := by
      rw [disjoint_comm]
      exact
        L.walk_support_disjoint_of_avoids_usedVertices
          hInAvoid htake_used hvHit_not_take
    have hTakeMid :
        Disjoint {x : V | x ∈ pTake.support}
          {x : V | x ∈ pMid.support} := by
      have hTakeDropHit :
          Disjoint {x : V | x ∈ pTake.support}
            {x : V | x ∈ (q.dropUntil vHit hvq).support} := by
        dsimp [pTake]
        exact
          Walk.IsPath.takeUntil_support_disjoint_dropUntil_of_idxOf_lt
            (G := G) hqpath hwExitq hvq
            (by simpa [q] using hExitBefore)
      rw [Set.disjoint_left]
      intro x hxTake hxMid
      have hxDropHit :
          x ∈ (q.dropUntil vHit hvq).support := by
        dsimp [pMid, Walk.segment] at hxMid
        exact
          SimpleGraph.Walk.support_takeUntil_subset
            (q.dropUntil vHit hvq)
            (Walk.mem_dropUntil_of_idxOf_le (G := G) hvq hwq hmid_q)
            hxMid
      exact Set.disjoint_left.mp hTakeDropHit hxTake hxDropHit
    have hTakeOut :
        Disjoint {x : V | x ∈ pTake.support}
          {x : V | x ∈ pOut.support} := by
      rw [disjoint_comm]
      exact
        L.walk_support_disjoint_of_avoids_usedVertices
          hOutAvoid htake_used hwHit_not_take
    have hBridgeIn :
        Disjoint {x : V | x ∈ pBridge.support}
          {x : V | x ∈ pIn.support} := by
      rw [disjoint_comm]
      exact hInBridge
    have hBridgeMid :
        Disjoint {x : V | x ∈ pBridge.support}
          {x : V | x ∈ pMid.support} := by
      exact
        L.walk_support_disjoint_of_avoids_usedVertices_two
          hBridgeAvoid hmid_used hwExit_not_mid hvNext_not_mid
    have hDropIn :
        Disjoint {x : V | x ∈ pDrop.support}
          {x : V | x ∈ pIn.support} := by
      rw [disjoint_comm]
      exact
        L.walk_support_disjoint_of_avoids_usedVertices
          hInAvoid hdrop_used hvHit_not_drop
    have hDropMid :
        Disjoint {x : V | x ∈ pDrop.support}
          {x : V | x ∈ pMid.support} := by
      rw [Set.disjoint_left]
      intro x hxDrop hxMid
      have hxq : x ∈ q.support :=
        Walk.segment_support_subset (G := G) q hvq hwq hmid_q hxMid
      have hx_le_w :
          q.support.idxOf x <= q.support.idxOf wHit :=
        Walk.IsPath.idxOf_le_of_mem_segment
          (G := G) hqpath hvq hwq hmid_q hxMid
      exact
        (Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
          (G := G) hqpath hvNextq hxq
          (lt_of_le_of_lt hx_le_w hNextAfter_q)) hxDrop
    have hDropOut :
        Disjoint {x : V | x ∈ pDrop.support}
          {x : V | x ∈ pOut.support} := by
      rw [disjoint_comm]
      exact
        L.walk_support_disjoint_of_avoids_usedVertices
          hOutAvoid hdrop_used hwHit_not_drop
    have hconcat :
        Disjoint {x : V | x ∈ ((pTake.append pBridge).append pDrop).support}
          {x : V | x ∈ ((pIn.append pMid).append pOut).support} :=
      Walk.support_append_append_disjoint_append_append
        (G := G) hTakeIn hTakeMid hTakeOut hBridgeIn hBridgeMid
        hBridgeOut hDropIn hDropMid hDropOut
    simpa [q, pTake, pMid, pDrop] using hconcat
  exact
    L.hasPartial_two_of_one_path_forward_bridge_splice_walks
      hiNew hjNew hwExit hvHit hwHit hvNext hmid pIn pBridge pOut hdisj


end Schematic.Math.GraphTheory
