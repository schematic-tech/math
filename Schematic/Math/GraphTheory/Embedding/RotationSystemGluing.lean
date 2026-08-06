import Schematic.Math.GraphTheory.Embedding.HypermapGluing
import Schematic.Math.GraphTheory.Embedding.RotationSystem

/-!
Cut-vertex gluing for graph rotation systems.

Two edge-disjoint spanning subgraphs whose supports meet only at `a` have a
disjoint-sum oriented-edge type.  If both subgraphs have a dart leaving `a`,
their local rotations can be spliced there.  The resulting rotation system on
the graph union induces the one-point hypermap sum.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

variable {V : Type u}

/-- The canonical map from summand darts to darts of a graph union. -/
def orientedEdgeSupMap
    {G₁ G₂ : SimpleGraph V} :
    Sum (OrientedEdge G₁) (OrientedEdge G₂) → OrientedEdge (G₁ ⊔ G₂)
  | Sum.inl e =>
      ⟨(e.tail, e.head),
        (sup_adj G₁ G₂ e.tail e.head).mpr (Or.inl e.adj)⟩
  | Sum.inr e =>
      ⟨(e.tail, e.head),
        (sup_adj G₁ G₂ e.tail e.head).mpr (Or.inr e.adj)⟩

theorem orientedEdgeSupMap_bijective
    {G₁ G₂ : SimpleGraph V}
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y) :
    Function.Bijective
      (orientedEdgeSupMap :
        Sum (OrientedEdge G₁) (OrientedEdge G₂) →
          OrientedEdge (G₁ ⊔ G₂)) := by
  constructor
  · intro e f hef
    cases e with
    | inl e =>
        cases f with
        | inl f =>
            have hp : e.1 = f.1 :=
              congrArg
                (fun z : OrientedEdge (G₁ ⊔ G₂) => z.1) hef
            apply congrArg Sum.inl
            apply Subtype.ext
            exact hp
        | inr f =>
            rcases e with ⟨⟨x, y⟩, hxy⟩
            rcases f with ⟨⟨x', y'⟩, hx'y'⟩
            have hp : (x, y) = (x', y') :=
              congrArg Subtype.val hef
            cases hp
            exact False.elim (hdisj hxy hx'y')
    | inr e =>
        cases f with
        | inl f =>
            rcases e with ⟨⟨x, y⟩, hxy⟩
            rcases f with ⟨⟨x', y'⟩, hx'y'⟩
            have hp : (x, y) = (x', y') :=
              congrArg Subtype.val hef
            cases hp
            exact False.elim (hdisj hx'y' hxy)
        | inr f =>
            have hp : e.1 = f.1 :=
              congrArg
                (fun z : OrientedEdge (G₁ ⊔ G₂) => z.1) hef
            apply congrArg Sum.inr
            apply Subtype.ext
            exact hp
  · intro e
    rcases (sup_adj G₁ G₂ e.tail e.head).mp e.adj with h₁ | h₂
    · refine ⟨Sum.inl ⟨(e.tail, e.head), h₁⟩, ?_⟩
      apply Subtype.ext
      rfl
    · refine ⟨Sum.inr ⟨(e.tail, e.head), h₂⟩, ?_⟩
      apply Subtype.ext
      rfl

/-- Oriented edges of an edge-disjoint graph union are the disjoint sum of the
oriented-edge types of its two summands. -/
noncomputable def orientedEdgeSupEquiv
    {G₁ G₂ : SimpleGraph V}
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y) :
    Sum (OrientedEdge G₁) (OrientedEdge G₂) ≃ OrientedEdge (G₁ ⊔ G₂) :=
  Equiv.ofBijective orientedEdgeSupMap
    (orientedEdgeSupMap_bijective hdisj)

@[simp]
theorem orientedEdgeSupEquiv_inl
    {G₁ G₂ : SimpleGraph V}
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y)
    (e : OrientedEdge G₁) :
    orientedEdgeSupEquiv hdisj (Sum.inl e) =
      ⟨(e.tail, e.head),
        (sup_adj G₁ G₂ e.tail e.head).mpr (Or.inl e.adj)⟩ :=
  rfl

@[simp]
theorem orientedEdgeSupEquiv_inr
    {G₁ G₂ : SimpleGraph V}
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y)
    (e : OrientedEdge G₂) :
    orientedEdgeSupEquiv hdisj (Sum.inr e) =
      ⟨(e.tail, e.head),
        (sup_adj G₁ G₂ e.tail e.head).mpr (Or.inr e.adj)⟩ :=
  rfl

@[simp]
theorem orientedEdgeSupEquiv_tail
    {G₁ G₂ : SimpleGraph V}
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y)
    (e : Sum (OrientedEdge G₁) (OrientedEdge G₂)) :
    (orientedEdgeSupEquiv hdisj e).tail =
      e.elim OrientedEdge.tail OrientedEdge.tail := by
  cases e <;> rfl

@[simp]
theorem orientedEdgeSupEquiv_head
    {G₁ G₂ : SimpleGraph V}
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y)
    (e : Sum (OrientedEdge G₁) (OrientedEdge G₂)) :
    (orientedEdgeSupEquiv hdisj e).head =
      e.elim OrientedEdge.head OrientedEdge.head := by
  cases e <;> rfl

@[simp]
theorem orientedEdgeSupEquiv_symm
    {G₁ G₂ : SimpleGraph V}
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y)
    (e : Sum (OrientedEdge G₁) (OrientedEdge G₂)) :
    orientedEdgeSupEquiv hdisj
        (e.elim (fun z => Sum.inl z.symm) (fun z => Sum.inr z.symm)) =
      (orientedEdgeSupEquiv hdisj e).symm := by
  cases e <;> rfl

def sumTail
    {G₁ G₂ : SimpleGraph V}
    (e : Sum (OrientedEdge G₁) (OrientedEdge G₂)) : V :=
  e.elim OrientedEdge.tail OrientedEdge.tail

theorem splicedNode_tail
    [Fintype V] [DecidableEq V]
    {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (a : V) (p : OrientedEdge G₁) (q : OrientedEdge G₂)
    (hp : p.tail = a) (hq : q.tail = a)
    (e : Sum (OrientedEdge G₁) (OrientedEdge G₂)) :
    sumTail
        (permSplice
          (permSum R₁.node R₂.node) (Sum.inl p) (Sum.inr q) e) =
      sumTail e := by
  cases e with
  | inl e =>
      by_cases hep : e = p
      · subst e
        simp [sumTail, R₂.node_tail q, hp, hq]
      · rw [permSplice_apply_of_ne]
        · simp [sumTail, R₁.node_tail e]
        · intro h
          exact hep (Sum.inl.inj h)
        · exact Sum.inl_ne_inr
  | inr e =>
      by_cases heq : e = q
      · subst e
        simp [sumTail, R₁.node_tail p, hp, hq]
      · rw [permSplice_apply_of_ne]
        · simp [sumTail, R₂.node_tail e]
        · exact Sum.inr_ne_inl
        · intro h
          exact heq (Sum.inr.inj h)

private theorem splicedNode_reachable_inl_inr
    [Fintype V] [DecidableEq V]
    {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hattach :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support → v = a)
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (p : OrientedEdge G₁) (q : OrientedEdge G₂)
    (hp : p.tail = a) (hq : q.tail = a)
    (e : OrientedEdge G₁) (f : OrientedEdge G₂)
    (hef : e.tail = f.tail) :
    PermReachable
      (permSplice (permSum R₁.node R₂.node)
        (Sum.inl p) (Sum.inr q))
      (Sum.inl e) (Sum.inr f) := by
  let B := Hypermap.disjointSum R₁.toHypermap R₂.toHypermap
  have hsep :
      ¬ PermReachable B.node (Sum.inl p) (Sum.inr q) :=
    Hypermap.disjointSum_node_pivots_separate
      R₁.toHypermap R₂.toHypermap p q
  have hea : e.tail = a := by
    exact hattach e.adj.left_mem_support
      (hef ▸ f.adj.left_mem_support)
  have he_p : PermReachable R₁.node e p :=
    R₁.node_orbit_of_same_tail e p (hea.trans hp.symm)
  have hq_f : PermReachable R₂.node q f :=
    R₂.node_orbit_of_same_tail q f (hq.trans (hea.symm.trans hef))
  have he_p' :
      PermReachable
        (permSplice B.node (Sum.inl p) (Sum.inr q))
        (Sum.inl e) (Sum.inl p) :=
    permSplice_reachable_of_old_reachable
      B.node (Sum.inl p) (Sum.inr q) hsep
      (permSum_reachable_inl R₁.node R₂.node he_p)
  have hp_q :
      PermReachable
        (permSplice B.node (Sum.inl p) (Sum.inr q))
        (Sum.inl p) (Sum.inr q) :=
    permSplice_left_reachable_right
      B.node (Sum.inl p) (Sum.inr q) hsep
  have hq_f' :
      PermReachable
        (permSplice B.node (Sum.inl p) (Sum.inr q))
        (Sum.inr q) (Sum.inr f) :=
    permSplice_reachable_of_old_reachable
      B.node (Sum.inl p) (Sum.inr q) hsep
      (permSum_reachable_inr R₁.node R₂.node hq_f)
  exact
    PermReachable.trans _
      he_p' (PermReachable.trans _ hp_q hq_f')

theorem splicedNode_reachable_of_same_tail
    [Fintype V] [DecidableEq V]
    {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hattach :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support → v = a)
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (p : OrientedEdge G₁) (q : OrientedEdge G₂)
    (hp : p.tail = a) (hq : q.tail = a)
    (e f : Sum (OrientedEdge G₁) (OrientedEdge G₂))
    (hef : sumTail e = sumTail f) :
    PermReachable
      (permSplice (permSum R₁.node R₂.node)
        (Sum.inl p) (Sum.inr q)) e f := by
  let B := Hypermap.disjointSum R₁.toHypermap R₂.toHypermap
  have hsep :
      ¬ PermReachable B.node (Sum.inl p) (Sum.inr q) :=
    Hypermap.disjointSum_node_pivots_separate
      R₁.toHypermap R₂.toHypermap p q
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          exact permSplice_reachable_of_old_reachable
            B.node (Sum.inl p) (Sum.inr q) hsep
            (permSum_reachable_inl R₁.node R₂.node
              (R₁.node_orbit_of_same_tail e f hef))
      | inr f =>
          exact splicedNode_reachable_inl_inr
            hattach R₁ R₂ p q hp hq e f hef
  | inr e =>
      cases f with
      | inl f =>
          exact PermReachable.symm _
            (splicedNode_reachable_inl_inr
              hattach R₁ R₂ p q hp hq f e hef.symm)
      | inr f =>
          exact permSplice_reachable_of_old_reachable
            B.node (Sum.inl p) (Sum.inr q) hsep
            (permSum_reachable_inr R₁.node R₂.node
              (R₂.node_orbit_of_same_tail e f hef))

/-- Splice two planar rotations along their unique common support vertex. -/
noncomputable def cutVertexSum
    [Fintype V] [DecidableEq V]
    {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y)
    (hattach :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support → v = a)
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (p : OrientedEdge G₁) (q : OrientedEdge G₂)
    (hp : p.tail = a) (hq : q.tail = a) :
    RotationSystem (G₁ ⊔ G₂) where
  node :=
    (orientedEdgeSupEquiv hdisj).permCongr
      (permSplice (permSum R₁.node R₂.node)
        (Sum.inl p) (Sum.inr q))
  node_tail := by
    intro e
    let E := orientedEdgeSupEquiv hdisj
    let N :=
      permSplice (permSum R₁.node R₂.node)
        (Sum.inl p) (Sum.inr q)
    change (E (N (E.symm e))).tail = e.tail
    calc
      (E (N (E.symm e))).tail = sumTail (N (E.symm e)) :=
        by
          simpa only [E, sumTail] using
            orientedEdgeSupEquiv_tail hdisj (N (E.symm e))
      _ = sumTail (E.symm e) :=
        splicedNode_tail R₁ R₂ a p q hp hq (E.symm e)
      _ = (E (E.symm e)).tail :=
        by
          simpa only [E, sumTail] using
            (orientedEdgeSupEquiv_tail hdisj (E.symm e)).symm
      _ = e.tail := by simp
  node_orbit_of_same_tail := by
    intro e f hef
    let E := orientedEdgeSupEquiv hdisj
    let N :=
      permSplice (permSum R₁.node R₂.node)
        (Sum.inl p) (Sum.inr q)
    have htail :
        sumTail (E.symm e) = sumTail (E.symm f) := by
      calc
        sumTail (E.symm e) = (E (E.symm e)).tail :=
          by
            simpa only [E, sumTail] using
              (orientedEdgeSupEquiv_tail hdisj (E.symm e)).symm
        _ = e.tail := by simp
        _ = f.tail := hef
        _ = (E (E.symm f)).tail := by simp
        _ = sumTail (E.symm f) :=
          by
            simpa only [E, sumTail] using
              orientedEdgeSupEquiv_tail hdisj (E.symm f)
    have hN : PermReachable N (E.symm e) (E.symm f) :=
      splicedNode_reachable_of_same_tail
        hattach R₁ R₂ p q hp hq (E.symm e) (E.symm f) htail
    have hconj :
        ∀ x, E (N x) = (E.permCongr N) (E x) := by
      intro x
      simp
    simpa [E, N] using
      permReachable_conj E N (E.permCongr N) hconj hN

theorem disjointRotationEdge_symm_eq
    [Fintype V] [DecidableEq V]
    {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (e : Sum (OrientedEdge G₁) (OrientedEdge G₂)) :
    (Hypermap.disjointSum R₁.toHypermap R₂.toHypermap).edge.symm e =
      (Hypermap.disjointSum R₁.toHypermap R₂.toHypermap).edge e := by
  cases e <;> rfl

/-- The hypermap induced by the graph cut-vertex sum is the abstract one-point
sum of the two input hypermaps. -/
noncomputable def cutVertexSum_toHypermapIso
    [Fintype V] [DecidableEq V]
    {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y)
    (hattach :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support → v = a)
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (p : OrientedEdge G₁) (q : OrientedEdge G₂)
    (hp : p.tail = a) (hq : q.tail = a) :
    Hypermap.Iso
      ((cutVertexSum hdisj hattach R₁ R₂ p q hp hq).toHypermap)
      (Hypermap.onePointSum R₁.toHypermap R₂.toHypermap p q) := by
  let E := orientedEdgeSupEquiv hdisj
  let N :=
    permSplice (permSum R₁.node R₂.node)
      (Sum.inl p) (Sum.inr q)
  let R := cutVertexSum hdisj hattach R₁ R₂ p q hp hq
  let K := Hypermap.onePointSum R₁.toHypermap R₂.toHypermap p q
  have hnode :
      ∀ x : OrientedEdge (G₁ ⊔ G₂),
        E.symm (R.node x) = K.node (E.symm x) := by
    intro x
    change E.symm ((E.permCongr N) x) = N (E.symm x)
    simp
  have hedge :
      ∀ x : OrientedEdge (G₁ ⊔ G₂),
        E.symm (R.toHypermap.edge x) =
          K.edge (E.symm x) := by
    intro x
    change E.symm x.symm =
      (Hypermap.disjointSum R₁.toHypermap R₂.toHypermap).edge (E.symm x)
    apply E.injective
    rw [E.apply_symm_apply]
    let z := E.symm x
    have hx : E z = x := by simp [z]
    rw [← hx]
    cases z with
    | inl e =>
        rw [E.symm_apply_apply]
        change (E (Sum.inl e)).symm = E (Sum.inl e.symm)
        simpa [E] using
          (orientedEdgeSupEquiv_symm hdisj (Sum.inl e)).symm
    | inr e =>
        rw [E.symm_apply_apply]
        change (E (Sum.inr e)).symm = E (Sum.inr e.symm)
        simpa [E] using
          (orientedEdgeSupEquiv_symm hdisj (Sum.inr e)).symm
  exact {
    toEquiv := E.symm
    map_edge := hedge
    map_node := hnode
    map_face := by
      intro x
      change E.symm (R.node.symm x.symm) =
        K.node.symm
          ((Hypermap.disjointSum R₁.toHypermap R₂.toHypermap).edge.symm
            (E.symm x))
      calc
        E.symm (R.node.symm x.symm) =
            K.node.symm (E.symm x.symm) :=
          perm_conj_symm_apply E.symm R.node K.node hnode x.symm
        _ = K.node.symm (K.edge (E.symm x)) := by
          apply congrArg K.node.symm
          simpa using hedge x
        _ = K.node.symm
            ((Hypermap.disjointSum R₁.toHypermap R₂.toHypermap).edge.symm
              (E.symm x)) := by
                apply congrArg K.node.symm
                exact
                  (disjointRotationEdge_symm_eq R₁ R₂ (E.symm x)).symm
  }

theorem cutVertexSum_dual_eulerPlanar
    [Fintype V] [DecidableEq V]
    {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hdisj : ∀ ⦃x y : V⦄, G₁.Adj x y → ¬ G₂.Adj x y)
    (hattach :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support → v = a)
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (p : OrientedEdge G₁) (q : OrientedEdge G₂)
    (hp : p.tail = a) (hq : q.tail = a)
    (hconn₁ : R₁.toHypermap.Connected)
    (hconn₂ : R₂.toHypermap.Connected)
    (hplanar₁ : R₁.toHypermap.dual.EulerPlanar)
    (hplanar₂ : R₂.toHypermap.dual.EulerPlanar) :
    (cutVertexSum hdisj hattach R₁ R₂ p q hp hq).toHypermap.dual.EulerPlanar := by
  let K := Hypermap.onePointSum R₁.toHypermap R₂.toHypermap p q
  have hKdual : K.dual.EulerPlanar :=
    Hypermap.onePointSum_dual_eulerPlanar
      R₁.toHypermap R₂.toHypermap p q
      hconn₁ hconn₂ hplanar₁ hplanar₂
  have hK : K.EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff K).mp hKdual
  let φ :=
    cutVertexSum_toHypermapIso
      hdisj hattach R₁ R₂ p q hp hq
  have hR :
      (cutVertexSum hdisj hattach R₁ R₂ p q hp hq).toHypermap.EulerPlanar :=
    φ.eulerPlanar_iff.mpr hK
  exact
    (Hypermap.dual_eulerPlanar_iff
      (cutVertexSum hdisj hattach R₁ R₂ p q hp hq).toHypermap).mpr hR

end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
