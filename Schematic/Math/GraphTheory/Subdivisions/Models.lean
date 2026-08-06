import Schematic.Math.GraphTheory.PathsTrees

/-!
Topological-model and minor interfaces. Mathlib currently has extensive simple
graph API but no graph-minor/topological-minor layer to build on directly.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

structure SubdivisionModel {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  branchVertex : W -> V
  branchVertex_injective : Function.Injective branchVertex
  edgePath : forall {x y : W}, H.Adj x y -> G.Walk (branchVertex x) (branchVertex y)
  edgePath_isPath : forall {x y : W} (hxy : H.Adj x y), (edgePath hxy).IsPath
  no_internal_branch_vertices : Prop
  internally_disjoint_edge_paths : Prop

def ContainsWeakSubdivision {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (SubdivisionModel H G)

def SubdivisionModel.NoInternalBranchVertices
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : SubdivisionModel H G) : Prop :=
  forall {x y : W} (hxy : H.Adj x y) {z : V},
    z ∈ Walk.InternalVertices (M.edgePath hxy) ->
      forall w : W, z ≠ M.branchVertex w

def SubdivisionModel.InternallyDisjointEdgePaths
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : SubdivisionModel H G) : Prop :=
  forall {x y x' y' : W}
    (hxy : H.Adj x y) (hx'y' : H.Adj x' y'),
      Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) ->
        Disjoint
          (Walk.InternalVertices (M.edgePath hxy))
          (Walk.InternalVertices (M.edgePath hx'y'))

structure StrictSubdivisionModel {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) extends SubdivisionModel H G where
  no_internal_branch_vertices' : toSubdivisionModel.NoInternalBranchVertices
  internally_disjoint_edge_paths' : toSubdivisionModel.InternallyDisjointEdgePaths

def ContainsStrictSubdivision {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (StrictSubdivisionModel H G)

abbrev ContainsSubdivision {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ContainsStrictSubdivision H G

def StrictSubdivisionModel.toWeak
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G) :
    SubdivisionModel H G :=
  M.toSubdivisionModel

theorem ContainsStrictSubdivision.toWeak
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (h : ContainsStrictSubdivision H G) :
    ContainsWeakSubdivision H G := by
  rcases h with ⟨M⟩
  exact ⟨M.toWeak⟩

def SubdivisionModel.map
    {W : Type u} {V : Type v} {U : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (M : SubdivisionModel H G) :
    SubdivisionModel H G' where
  branchVertex x := f (M.branchVertex x)
  branchVertex_injective := hf.comp M.branchVertex_injective
  edgePath hxy := (M.edgePath hxy).map f
  edgePath_isPath hxy :=
    SimpleGraph.Walk.map_isPath_of_injective hf (M.edgePath_isPath hxy)
  no_internal_branch_vertices := M.no_internal_branch_vertices
  internally_disjoint_edge_paths := M.internally_disjoint_edge_paths

theorem ContainsWeakSubdivision.map
    {W : Type u} {V : Type v} {U : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (h : ContainsWeakSubdivision H G) :
    ContainsWeakSubdivision H G' := by
  rcases h with ⟨M⟩
  exact ⟨M.map f hf⟩

theorem ContainsWeakSubdivision.of_le
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G G' : SimpleGraph V}
    (hGG' : G ≤ G')
    (h : ContainsWeakSubdivision H G) :
    ContainsWeakSubdivision H G' :=
  h.map (.ofLE hGG') Function.injective_id

def StrictSubdivisionModel.map
    {W : Type u} {V : Type v} {U : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (M : StrictSubdivisionModel H G) :
    StrictSubdivisionModel H G' where
  toSubdivisionModel := M.toWeak.map f hf
  no_internal_branch_vertices' := by
    intro x y hxy z hz w hzw
    have hz_pre :
        Exists fun z₀ : V =>
          z₀ ∈ Walk.InternalVertices (M.edgePath hxy) ∧ f z₀ = z := by
      exact (Walk.mem_internalVertices_map_iff_of_injective
        f hf (M.edgePath hxy)).mp
          (by simpa [StrictSubdivisionModel.toWeak, SubdivisionModel.map] using hz)
    rcases hz_pre with ⟨z₀, hz₀, hz₀_eq⟩
    exact M.no_internal_branch_vertices' hxy hz₀ w (hf (hz₀_eq.trans hzw))
  internally_disjoint_edge_paths' := by
    intro x y x' y' hxy hx'y' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    have hz_pre :
        Exists fun z₀ : V =>
          z₀ ∈ Walk.InternalVertices (M.edgePath hxy) ∧ f z₀ = z := by
      exact (Walk.mem_internalVertices_map_iff_of_injective
        f hf (M.edgePath hxy)).mp
          (by simpa [StrictSubdivisionModel.toWeak, SubdivisionModel.map] using hz)
    have hz'_pre :
        Exists fun z₁ : V =>
          z₁ ∈ Walk.InternalVertices (M.edgePath hx'y') ∧ f z₁ = z := by
      exact (Walk.mem_internalVertices_map_iff_of_injective
        f hf (M.edgePath hx'y')).mp
          (by simpa [StrictSubdivisionModel.toWeak, SubdivisionModel.map] using hz')
    rcases hz_pre with ⟨z₀, hz₀, hz₀_eq⟩
    rcases hz'_pre with ⟨z₁, hz₁, hz₁_eq⟩
    have hz_eq : z₀ = z₁ := hf (hz₀_eq.trans hz₁_eq.symm)
    exact Set.disjoint_left.mp (M.internally_disjoint_edge_paths' hxy hx'y' hne)
      hz₀ (by simpa [hz_eq] using hz₁)

def StrictSubdivisionModel.targetRestrict
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (S : Set V)
    (hbranch : forall x : W, M.branchVertex x ∈ S)
    (hedge :
      forall {x y : W} (hxy : H.Adj x y) {z : V},
        z ∈ (M.edgePath hxy).support -> z ∈ S) :
    StrictSubdivisionModel H (G.induce S) where
  toSubdivisionModel.branchVertex x := ⟨M.branchVertex x, hbranch x⟩
  toSubdivisionModel.branchVertex_injective := by
    intro x y hxy
    exact M.branchVertex_injective (Subtype.ext_iff.mp hxy)
  toSubdivisionModel.edgePath hxy := by
    let p : G.Walk (M.branchVertex _) (M.branchVertex _) :=
      M.edgePath hxy
    let hpS : forall z : V, z ∈ p.support -> z ∈ S :=
      fun z hz => hedge hxy hz
    exact (p.induce S hpS).copy (Subtype.ext rfl) (Subtype.ext rfl)
  toSubdivisionModel.edgePath_isPath hxy := by
    let p : G.Walk (M.branchVertex _) (M.branchVertex _) :=
      M.edgePath hxy
    let hpS : forall z : V, z ∈ p.support -> z ∈ S :=
      fun z hz => hedge hxy hz
    have hpS_path : (p.induce S hpS).IsPath := by
      apply SimpleGraph.Walk.IsPath.of_map
        (f := (SimpleGraph.Embedding.induce (G := G) S).toHom)
      simpa [p, hpS] using M.edgePath_isPath hxy
    simpa [p, hpS] using
      (SimpleGraph.Walk.isPath_copy (p.induce S hpS)
        (Subtype.ext rfl) (Subtype.ext rfl)).mpr hpS_path
  toSubdivisionModel.no_internal_branch_vertices :=
    M.no_internal_branch_vertices
  toSubdivisionModel.internally_disjoint_edge_paths :=
    M.internally_disjoint_edge_paths
  no_internal_branch_vertices' := by
    intro x y hxy z hz w hzw
    let p : G.Walk (M.branchVertex _) (M.branchVertex _) :=
      M.edgePath hxy
    let hpS : forall z : V, z ∈ p.support -> z ∈ S :=
      fun z hz => hedge hxy hz
    let pS :
        (G.induce S).Walk
          ⟨M.branchVertex x, hpS _ p.start_mem_support⟩
          ⟨M.branchVertex y, hpS _ p.end_mem_support⟩ :=
      p.induce S hpS
    have hzS : z ∈ Walk.InternalVertices pS := by
      change z ∈
        Walk.InternalVertices
          (pS.copy (Subtype.ext rfl) (Subtype.ext rfl)) at hz
      exact
        (Walk.mem_internalVertices_copy_iff pS
          (Subtype.ext rfl) (Subtype.ext rfl)).mp hz
    have hz_map :
        (z : V) ∈
          Walk.InternalVertices
            (pS.map (SimpleGraph.Embedding.induce (G := G) S).toHom) := by
      exact
        (Walk.mem_internalVertices_map_iff_of_injective
          (SimpleGraph.Embedding.induce (G := G) S).toHom
          (SimpleGraph.Embedding.induce (G := G) S).injective pS).mpr
          ⟨z, hzS, rfl⟩
    have hz_orig : (z : V) ∈ Walk.InternalVertices p := by
      simpa [pS, p, hpS] using hz_map
    exact M.no_internal_branch_vertices' hxy hz_orig w
      (congrArg Subtype.val hzw)
  internally_disjoint_edge_paths' := by
    intro x y x' y' hxy hx'y' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    let p : G.Walk (M.branchVertex _) (M.branchVertex _) :=
      M.edgePath hxy
    let hpS : forall z : V, z ∈ p.support -> z ∈ S :=
      fun z hz => hedge hxy hz
    let pS :
        (G.induce S).Walk
          ⟨M.branchVertex x, hpS _ p.start_mem_support⟩
          ⟨M.branchVertex y, hpS _ p.end_mem_support⟩ :=
      p.induce S hpS
    have hzS : z ∈ Walk.InternalVertices pS := by
      change z ∈
        Walk.InternalVertices
          (pS.copy (Subtype.ext rfl) (Subtype.ext rfl)) at hz
      exact
        (Walk.mem_internalVertices_copy_iff pS
          (Subtype.ext rfl) (Subtype.ext rfl)).mp hz
    have hz_map :
        (z : V) ∈
          Walk.InternalVertices
            (pS.map (SimpleGraph.Embedding.induce (G := G) S).toHom) := by
      exact
        (Walk.mem_internalVertices_map_iff_of_injective
          (SimpleGraph.Embedding.induce (G := G) S).toHom
          (SimpleGraph.Embedding.induce (G := G) S).injective pS).mpr
          ⟨z, hzS, rfl⟩
    have hz_orig : (z : V) ∈ Walk.InternalVertices p := by
      simpa [pS, p, hpS] using hz_map
    let q : G.Walk (M.branchVertex _) (M.branchVertex _) :=
      M.edgePath hx'y'
    let hqS : forall z : V, z ∈ q.support -> z ∈ S :=
      fun z hz => hedge hx'y' hz
    let qS :
        (G.induce S).Walk
          ⟨M.branchVertex x', hqS _ q.start_mem_support⟩
          ⟨M.branchVertex y', hqS _ q.end_mem_support⟩ :=
      q.induce S hqS
    have hzS' : z ∈ Walk.InternalVertices qS := by
      change z ∈
        Walk.InternalVertices
          (qS.copy (Subtype.ext rfl) (Subtype.ext rfl)) at hz'
      exact
        (Walk.mem_internalVertices_copy_iff qS
          (Subtype.ext rfl) (Subtype.ext rfl)).mp hz'
    have hz_map' :
        (z : V) ∈
          Walk.InternalVertices
            (qS.map (SimpleGraph.Embedding.induce (G := G) S).toHom) := by
      exact
        (Walk.mem_internalVertices_map_iff_of_injective
          (SimpleGraph.Embedding.induce (G := G) S).toHom
          (SimpleGraph.Embedding.induce (G := G) S).injective qS).mpr
          ⟨z, hzS', rfl⟩
    have hz_orig' : (z : V) ∈ Walk.InternalVertices q := by
      simpa [qS, q, hqS] using hz_map'
    exact Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hxy hx'y' hne)
      hz_orig hz_orig'

def StrictSubdivisionModel.targetRestrictSupport
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (hsource : forall x : W, Exists fun y : W => H.Adj x y) :
    StrictSubdivisionModel H (G.induce G.support) :=
  M.targetRestrict G.support
    (fun x => by
      obtain ⟨y, hxy⟩ := hsource x
      rw [SimpleGraph.mem_support]
      let p : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath hxy
      have hne : M.branchVertex x ≠ M.branchVertex y := by
        intro h
        exact hxy.ne (M.branchVertex_injective h)
      have hp_not_nil : Not p.Nil :=
        SimpleGraph.Walk.not_nil_of_ne (p := p) hne
      exact ⟨p.snd, p.adj_snd hp_not_nil⟩)
    (fun {x y} hxy {z} hz => by
      have hne : M.branchVertex x ≠ M.branchVertex y := by
        intro h
        exact hxy.ne (M.branchVertex_injective h)
      have hp_not_nil : Not (M.edgePath hxy).Nil :=
        SimpleGraph.Walk.not_nil_of_ne (p := M.edgePath hxy)
          hne
      exact SimpleGraph.mem_support_of_mem_walk_support
        (M.edgePath hxy) hp_not_nil (w := z) hz)

theorem ContainsStrictSubdivision.targetRestrict
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (h : ContainsStrictSubdivision H G)
    (S : Set V)
    (hbranch :
      forall x : W,
        (Classical.choice h).branchVertex x ∈ S)
    (hedge :
      forall {x y : W} (hxy : H.Adj x y) {z : V},
        z ∈ ((Classical.choice h).edgePath hxy).support -> z ∈ S) :
    ContainsStrictSubdivision H (G.induce S) := by
  classical
  exact ⟨(Classical.choice h).targetRestrict S hbranch hedge⟩

theorem ContainsStrictSubdivision.targetRestrictSupport
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (h : ContainsStrictSubdivision H G)
    (hsource : forall x : W, Exists fun y : W => H.Adj x y) :
    ContainsStrictSubdivision H (G.induce G.support) := by
  classical
  exact ⟨(Classical.choice h).targetRestrictSupport hsource⟩

theorem ContainsStrictSubdivision.targetRestrictOfSupportSubset
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (h : ContainsStrictSubdivision H G)
    (hsource : forall x : W, Exists fun y : W => H.Adj x y)
    {S : Set V}
    (hS : G.support ⊆ S) :
    ContainsStrictSubdivision H (G.induce S) := by
  rcases h with ⟨M⟩
  refine ⟨M.targetRestrict S ?_ ?_⟩
  · intro x
    apply hS
    obtain ⟨y, hxy⟩ := hsource x
    rw [SimpleGraph.mem_support]
    let p : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath hxy
    have hne : M.branchVertex x ≠ M.branchVertex y := by
      intro h
      exact hxy.ne (M.branchVertex_injective h)
    have hp_not_nil : Not p.Nil :=
      SimpleGraph.Walk.not_nil_of_ne (p := p) hne
    exact ⟨p.snd, p.adj_snd hp_not_nil⟩
  · intro x y hxy z hz
    apply hS
    have hne : M.branchVertex x ≠ M.branchVertex y := by
      intro h
      exact hxy.ne (M.branchVertex_injective h)
    have hp_not_nil : Not (M.edgePath hxy).Nil :=
      SimpleGraph.Walk.not_nil_of_ne (p := M.edgePath hxy)
        hne
    exact SimpleGraph.mem_support_of_mem_walk_support
      (M.edgePath hxy) hp_not_nil (w := z) hz

def SubdivisionModel.domainRestrict
    {W₀ : Type*} {W : Type u} {V : Type v}
    {H₀ : SimpleGraph W₀} {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W₀ ↪ W)
    (h_adj : forall {x y : W₀}, H₀.Adj x y -> H.Adj (e x) (e y))
    (M : SubdivisionModel H G) :
    SubdivisionModel H₀ G where
  branchVertex x := M.branchVertex (e x)
  branchVertex_injective := M.branchVertex_injective.comp e.injective
  edgePath hxy := M.edgePath (h_adj hxy)
  edgePath_isPath hxy := M.edgePath_isPath (h_adj hxy)
  no_internal_branch_vertices := M.no_internal_branch_vertices
  internally_disjoint_edge_paths := M.internally_disjoint_edge_paths

def StrictSubdivisionModel.domainRestrict
    {W₀ : Type*} {W : Type u} {V : Type v}
    {H₀ : SimpleGraph W₀} {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W₀ ↪ W)
    (h_adj : forall {x y : W₀}, H₀.Adj x y -> H.Adj (e x) (e y))
    (M : StrictSubdivisionModel H G) :
    StrictSubdivisionModel H₀ G where
  toSubdivisionModel := M.toWeak.domainRestrict e h_adj
  no_internal_branch_vertices' := by
    intro x y hxy z hz w
    exact M.no_internal_branch_vertices' (h_adj hxy) hz (e w)
  internally_disjoint_edge_paths' := by
    intro x y x' y' hxy hx'y' hne
    refine M.internally_disjoint_edge_paths'
      (h_adj hxy) (h_adj hx'y') ?_
    intro hsame
    apply hne
    rcases hsame with hsame | hsame
    · exact Or.inl ⟨e.injective hsame.1, e.injective hsame.2⟩
    · exact Or.inr ⟨e.injective hsame.1, e.injective hsame.2⟩

theorem ContainsStrictSubdivision.map
    {W : Type u} {V : Type v} {U : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (h : ContainsStrictSubdivision H G) :
    ContainsStrictSubdivision H G' := by
  rcases h with ⟨M⟩
  exact ⟨M.map f hf⟩

theorem ContainsWeakSubdivision.domainRestrict
    {W₀ : Type*} {W : Type u} {V : Type v}
    {H₀ : SimpleGraph W₀} {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W₀ ↪ W)
    (h_adj : forall {x y : W₀}, H₀.Adj x y -> H.Adj (e x) (e y))
    (h : ContainsWeakSubdivision H G) :
    ContainsWeakSubdivision H₀ G := by
  rcases h with ⟨M⟩
  exact ⟨M.domainRestrict e h_adj⟩

theorem ContainsStrictSubdivision.domainRestrict
    {W₀ : Type*} {W : Type u} {V : Type v}
    {H₀ : SimpleGraph W₀} {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W₀ ↪ W)
    (h_adj : forall {x y : W₀}, H₀.Adj x y -> H.Adj (e x) (e y))
    (h : ContainsStrictSubdivision H G) :
    ContainsStrictSubdivision H₀ G := by
  rcases h with ⟨M⟩
  exact ⟨M.domainRestrict e h_adj⟩

theorem ContainsStrictSubdivision.of_le
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G G' : SimpleGraph V}
    (hGG' : G ≤ G')
    (h : ContainsStrictSubdivision H G) :
    ContainsStrictSubdivision H G' :=
  h.map (.ofLE hGG') Function.injective_id

/-- Restrict the target graph of a strict subdivision to a same-vertex
subgraph when every edge of every model path lies in that subgraph.

This is the reverse direction to `ContainsStrictSubdivision.of_le` used by
Kuratowski localization: after showing that a topological model never uses
edges outside one split piece, the same model can be regarded as living in
that piece. -/
def StrictSubdivisionModel.edgeRestrict
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G G₀ : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (hedge :
      forall {x y : W} (hxy : H.Adj x y) (e : Sym2 V),
        e ∈ (M.edgePath hxy).edges -> e ∈ G₀.edgeSet) :
    StrictSubdivisionModel H G₀ where
  toSubdivisionModel.branchVertex := M.branchVertex
  toSubdivisionModel.branchVertex_injective := M.branchVertex_injective
  toSubdivisionModel.edgePath hxy :=
    (M.edgePath hxy).transfer G₀ (hedge hxy)
  toSubdivisionModel.edgePath_isPath hxy := by
    exact (M.edgePath_isPath hxy).transfer (hedge hxy)
  toSubdivisionModel.no_internal_branch_vertices :=
    M.no_internal_branch_vertices
  toSubdivisionModel.internally_disjoint_edge_paths :=
    M.internally_disjoint_edge_paths
  no_internal_branch_vertices' := by
    intro x y hxy z hz w hzw
    have hz_orig :
        z ∈ Walk.InternalVertices (M.edgePath hxy) := by
      simpa [Walk.internalVertices_transfer] using hz
    exact M.no_internal_branch_vertices' hxy hz_orig w hzw
  internally_disjoint_edge_paths' := by
    intro x y x' y' hxy hx'y' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    have hz_orig :
        z ∈ Walk.InternalVertices (M.edgePath hxy) := by
      simpa [Walk.internalVertices_transfer] using hz
    have hz'_orig :
        z ∈ Walk.InternalVertices (M.edgePath hx'y') := by
      simpa [Walk.internalVertices_transfer] using hz'
    exact
      Set.disjoint_left.mp
        (M.internally_disjoint_edge_paths' hxy hx'y' hne)
        hz_orig hz'_orig

theorem ContainsStrictSubdivision.edgeRestrict
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G G₀ : SimpleGraph V}
    (h : ContainsStrictSubdivision H G)
    (hedge :
      forall {x y : W} (hxy : H.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice h).edgePath hxy).edges -> e ∈ G₀.edgeSet) :
    ContainsStrictSubdivision H G₀ := by
  classical
  exact ⟨(Classical.choice h).edgeRestrict hedge⟩

/-- Contrapositive of `StrictSubdivisionModel.edgeRestrict`: if a concrete
strict-subdivision model cannot be restricted to a same-vertex subgraph, then
some edge used by one of its model paths is outside that subgraph. -/
theorem StrictSubdivisionModel.exists_edge_not_mem_edgeSet_of_not_contains_edgeRestrict
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G G₀ : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (hno : Not (ContainsStrictSubdivision H G₀)) :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : H.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ (M.edgePath hxy).edges ∧ e ∉ G₀.edgeSet := by
  by_contra hnone
  apply hno
  refine ⟨M.edgeRestrict ?_⟩
  intro x y hxy e he
  by_contra he_not
  exact hnone ⟨x, y, hxy, e, he, he_not⟩

/-- Contrapositive of `ContainsStrictSubdivision.edgeRestrict`: if a strict
subdivision in `G` is not present in a same-vertex subgraph `G₀`, then some
edge of a chosen model path lies outside `G₀`. -/
theorem ContainsStrictSubdivision.exists_model_edge_not_mem_edgeSet_of_not_contains
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G G₀ : SimpleGraph V}
    (h : ContainsStrictSubdivision H G)
    (hno : Not (ContainsStrictSubdivision H G₀)) :
    Exists fun x : W =>
      Exists fun y : W =>
        Exists fun hxy : H.Adj x y =>
          Exists fun e : Sym2 V =>
            e ∈ ((Classical.choice h).edgePath hxy).edges ∧
              e ∉ G₀.edgeSet := by
  exact
    (Classical.choice h).exists_edge_not_mem_edgeSet_of_not_contains_edgeRestrict
      hno

theorem card_le_of_containsWeakSubdivision
    {W : Type u} {V : Type v}
    [Fintype W] [Fintype V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (h : ContainsWeakSubdivision H G) :
    Fintype.card W <= Fintype.card V := by
  rcases h with ⟨M⟩
  exact Fintype.card_le_of_injective M.branchVertex M.branchVertex_injective

theorem card_le_of_containsStrictSubdivision
    {W : Type u} {V : Type v}
    [Fintype W] [Fintype V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (h : ContainsStrictSubdivision H G) :
    Fintype.card W <= Fintype.card V :=
  card_le_of_containsWeakSubdivision h.toWeak

def StrictSubdivisionModel.EdgeUnsplit
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy : H.Adj x y) : Prop :=
  (M.edgePath hxy).length = 1

theorem StrictSubdivisionModel.edgeUnsplit_iff_of_adj_proof
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy hxy' : H.Adj x y) :
    M.EdgeUnsplit hxy ↔ M.EdgeUnsplit hxy' := by
  cases Subsingleton.elim hxy hxy'
  rfl

theorem StrictSubdivisionModel.edgeUnsplit_of_eq
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y x' y' : W}
    (hx : x = x')
    (hy : y = y')
    {hxy : H.Adj x y}
    {hx'y' : H.Adj x' y'}
    (h : M.EdgeUnsplit hxy) :
    M.EdgeUnsplit hx'y' := by
  subst x'
  subst y'
  exact (M.edgeUnsplit_iff_of_adj_proof hxy hx'y').1 h

theorem StrictSubdivisionModel.domainRestrict_edgeUnsplit
    {W₀ : Type*} {W : Type u} {V : Type v}
    {H₀ : SimpleGraph W₀} {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W₀ ↪ W)
    (h_adj : forall {x y : W₀}, H₀.Adj x y -> H.Adj (e x) (e y))
    (M : StrictSubdivisionModel H G)
    {x y : W₀}
    (hxy : H₀.Adj x y) :
    (M.domainRestrict e h_adj).EdgeUnsplit hxy ↔
      M.EdgeUnsplit (h_adj hxy) := by
  rfl

theorem StrictSubdivisionModel.adj_of_edgeUnsplit
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy : H.Adj x y)
    (h_unsplit : M.EdgeUnsplit hxy) :
    G.Adj (M.branchVertex x) (M.branchVertex y) :=
  SimpleGraph.Walk.adj_of_length_eq_one h_unsplit

theorem StrictSubdivisionModel.not_mem_internalVertices_of_edgeUnsplit
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy : H.Adj x y)
    (h_unsplit : M.EdgeUnsplit hxy)
    {z : V} :
    z ∉ Walk.InternalVertices (M.edgePath hxy) :=
  Walk.not_mem_internalVertices_of_length_eq_one h_unsplit

theorem StrictSubdivisionModel.branchVertex_ne
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy : x ≠ y) :
    M.branchVertex x ≠ M.branchVertex y := by
  intro h
  exact hxy (M.branchVertex_injective h)

theorem StrictSubdivisionModel.branchVertex_ne_of_adj
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy : H.Adj x y) :
    M.branchVertex x ≠ M.branchVertex y :=
  M.branchVertex_ne hxy.ne

theorem StrictSubdivisionModel.branchVertex_mem_edgePath_support_iff
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y w : W}
    (hxy : H.Adj x y) :
    M.branchVertex w ∈ (M.edgePath hxy).support ↔ w = x ∨ w = y := by
  constructor
  · intro hw_support
    by_cases hwx : w = x
    · exact Or.inl hwx
    by_cases hwy : w = y
    · exact Or.inr hwy
    exfalso
    have hw_ne_x : M.branchVertex w ≠ M.branchVertex x := by
      intro h
      exact hwx (M.branchVertex_injective h)
    have hw_ne_y : M.branchVertex w ≠ M.branchVertex y := by
      intro h
      exact hwy (M.branchVertex_injective h)
    have hw_internal :
        M.branchVertex w ∈ Walk.InternalVertices (M.edgePath hxy) :=
      ⟨hw_support, hw_ne_x, hw_ne_y⟩
    exact M.no_internal_branch_vertices' hxy hw_internal w rfl
  · rintro (rfl | rfl)
    · exact (M.edgePath hxy).start_mem_support
    · exact (M.edgePath hxy).end_mem_support

theorem StrictSubdivisionModel.edgePath_support_inter_subset_common_branch_vertices
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y x' y' : W}
    (hxy : H.Adj x y)
    (hx'y' : H.Adj x' y')
    (hne :
      Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x')))
    {z : V}
    (hz : z ∈ (M.edgePath hxy).support)
    (hz' : z ∈ (M.edgePath hx'y').support) :
    Exists fun w : W =>
      (w = x ∨ w = y) ∧ (w = x' ∨ w = y') ∧
        z = M.branchVertex w := by
  by_cases hzx : z = M.branchVertex x
  · have hx_mem :
        M.branchVertex x ∈ (M.edgePath hx'y').support := by
      simpa [hzx] using hz'
    have hx_endpoint :
        x = x' ∨ x = y' :=
      (M.branchVertex_mem_edgePath_support_iff hx'y').mp hx_mem
    exact ⟨x, Or.inl rfl, hx_endpoint, hzx⟩
  by_cases hzy : z = M.branchVertex y
  · have hy_mem :
        M.branchVertex y ∈ (M.edgePath hx'y').support := by
      simpa [hzy] using hz'
    have hy_endpoint :
        y = x' ∨ y = y' :=
      (M.branchVertex_mem_edgePath_support_iff hx'y').mp hy_mem
    exact ⟨y, Or.inr rfl, hy_endpoint, hzy⟩
  have hz_internal :
      z ∈ Walk.InternalVertices (M.edgePath hxy) :=
    ⟨hz, hzx, hzy⟩
  by_cases hzx' : z = M.branchVertex x'
  · have hx'_mem :
        M.branchVertex x' ∈ (M.edgePath hxy).support := by
      simpa [hzx'] using hz
    have hx'_endpoint :
        x' = x ∨ x' = y :=
      (M.branchVertex_mem_edgePath_support_iff hxy).mp hx'_mem
    exact ⟨x', hx'_endpoint, Or.inl rfl, hzx'⟩
  by_cases hzy' : z = M.branchVertex y'
  · have hy'_mem :
        M.branchVertex y' ∈ (M.edgePath hxy).support := by
      simpa [hzy'] using hz
    have hy'_endpoint :
        y' = x ∨ y' = y :=
      (M.branchVertex_mem_edgePath_support_iff hxy).mp hy'_mem
    exact ⟨y', hy'_endpoint, Or.inr rfl, hzy'⟩
  have hz'_internal :
      z ∈ Walk.InternalVertices (M.edgePath hx'y') :=
    ⟨hz', hzx', hzy'⟩
  exact False.elim
    (Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hxy hx'y' hne)
      hz_internal hz'_internal)

/-- If two distinct source edges of a strict subdivision have a unique common
source endpoint `c`, then every host vertex lying on both corresponding edge
path supports is the branch vertex of `c`.

This is the common-end version of
`edgePath_support_disjoint_of_no_common_endpoint`.  It is used in the
Kuratowski leakage analysis after the finite source-graph case split has
identified a single common endpoint for several mixed source edges. -/
theorem StrictSubdivisionModel.edgePath_support_inter_eq_common_branchVertex
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y x' y' c : W}
    (hxy : H.Adj x y)
    (hx'y' : H.Adj x' y')
    (hne :
      Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x')))
    (hunique :
      forall w : W,
        (w = x ∨ w = y) ->
          (w = x' ∨ w = y') ->
            w = c)
    {z : V}
    (hz : z ∈ (M.edgePath hxy).support)
    (hz' : z ∈ (M.edgePath hx'y').support) :
    z = M.branchVertex c := by
  rcases
      M.edgePath_support_inter_subset_common_branch_vertices
        hxy hx'y' hne hz hz' with
    ⟨w, hwxy, hwx'y', hzw⟩
  exact hzw.trans (by rw [hunique w hwxy hwx'y'])

/-- Set-valued form of
`StrictSubdivisionModel.edgePath_support_inter_eq_common_branchVertex`.

If two distinct source edges have the unique common source endpoint `c`, then
the full supports of their host edge paths meet exactly in the branch vertex
of `c`.  This is the form needed by path-append lemmas. -/
theorem StrictSubdivisionModel.edgePath_support_inter_eq_singleton_common_branchVertex
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y x' y' c : W}
    (hxy : H.Adj x y)
    (hx'y' : H.Adj x' y')
    (hne :
      Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x')))
    (hc_left : c = x ∨ c = y)
    (hc_right : c = x' ∨ c = y')
    (hunique :
      forall w : W,
        (w = x ∨ w = y) ->
          (w = x' ∨ w = y') ->
            w = c) :
    {z : V | z ∈ (M.edgePath hxy).support} ∩
        {z : V | z ∈ (M.edgePath hx'y').support} =
      {M.branchVertex c} := by
  ext z
  constructor
  · rintro ⟨hz, hz'⟩
    have hz_eq :
        z = M.branchVertex c :=
      M.edgePath_support_inter_eq_common_branchVertex
        hxy hx'y' hne hunique hz hz'
    exact by simp [hz_eq]
  · intro hz
    have hz_eq : z = M.branchVertex c := by
      simpa using hz
    subst z
    constructor
    · exact (M.branchVertex_mem_edgePath_support_iff hxy).mpr hc_left
    · exact (M.branchVertex_mem_edgePath_support_iff hx'y').mpr hc_right

/-- Edge paths of a strict subdivision with disjoint source endpoints have
disjoint full supports.

The core strict-subdivision interface gives disjoint internal vertices.  The
stronger full-support statement follows because the only possible support
intersections of two distinct edge paths are common branch vertices, and the
source endpoint sets are assumed disjoint. -/
theorem StrictSubdivisionModel.edgePath_support_disjoint_of_no_common_endpoint
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y x' y' : W}
    (hxy : H.Adj x y)
    (hx'y' : H.Adj x' y')
    (hxx' : x ≠ x') (hxy' : x ≠ y')
    (hyx' : y ≠ x') (hyy' : y ≠ y') :
    Disjoint
      {z : V | z ∈ (M.edgePath hxy).support}
      {z : V | z ∈ (M.edgePath hx'y').support} := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have hne :
      Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) := by
    intro h
    rcases h with hsame | hrev
    · exact hxx' hsame.1
    · exact hxy' hrev.1
  rcases
      M.edgePath_support_inter_subset_common_branch_vertices
        hxy hx'y' hne hz hz' with
    ⟨w, hwxy, hwx'y', _hzw⟩
  rcases hwxy with rfl | rfl
  · rcases hwx'y' with hx_eq_x' | hx_eq_y'
    · exact hxx' hx_eq_x'
    · exact hxy' hx_eq_y'
  · rcases hwx'y' with hy_eq_x' | hy_eq_y'
    · exact hyx' hy_eq_x'
    · exact hyy' hy_eq_y'

/-- Case split for the full supports of two strict-subdivision edge paths:
either the supports are disjoint, or the two source edges have a common
endpoint. -/
theorem StrictSubdivisionModel.edgePath_support_disjoint_or_common_endpoint
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y x' y' : W}
    (hxy : H.Adj x y)
    (hx'y' : H.Adj x' y') :
    Disjoint
      {z : V | z ∈ (M.edgePath hxy).support}
      {z : V | z ∈ (M.edgePath hx'y').support} ∨
      x = x' ∨ x = y' ∨ y = x' ∨ y = y' := by
  classical
  by_cases hxx' : x = x'
  · exact Or.inr (Or.inl hxx')
  by_cases hxy' : x = y'
  · exact Or.inr (Or.inr (Or.inl hxy'))
  by_cases hyx' : y = x'
  · exact Or.inr (Or.inr (Or.inr (Or.inl hyx')))
  by_cases hyy' : y = y'
  · exact Or.inr (Or.inr (Or.inr (Or.inr hyy')))
  · exact Or.inl
      (M.edgePath_support_disjoint_of_no_common_endpoint
        hxy hx'y' hxx' hxy' hyx' hyy')

theorem StrictSubdivisionModel.branchVertex_mem_support_of_adj
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy : H.Adj x y) :
    M.branchVertex x ∈ G.support := by
  rw [SimpleGraph.mem_support]
  let p : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath hxy
  have hp_not_nil : Not p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) (M.branchVertex_ne_of_adj hxy)
  exact ⟨p.snd, p.adj_snd hp_not_nil⟩

theorem StrictSubdivisionModel.branchVertex_mem_support_of_degree_pos
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x : W}
    [Fintype (H.neighborSet x)]
    (hdegree : 0 < H.degree x) :
    M.branchVertex x ∈ G.support := by
  have hx_support : x ∈ H.support :=
    (SimpleGraph.degree_pos_iff_mem_support (G := H) (v := x)).mp hdegree
  rw [SimpleGraph.mem_support] at hx_support
  obtain ⟨y, hxy⟩ := hx_support
  exact M.branchVertex_mem_support_of_adj hxy

theorem StrictSubdivisionModel.edgePath_snd_eq_branch_or_internal
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy : H.Adj x y) :
    let p : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath hxy
    p.snd = M.branchVertex y ∨ p.snd ∈ Walk.InternalVertices p := by
  classical
  intro p
  have hp_not_nil : Not p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) (M.branchVertex_ne_of_adj hxy)
  by_cases hsnd : p.snd = M.branchVertex y
  · exact Or.inl hsnd
  · right
    have hsnd_support : p.snd ∈ p.support := by
      rw [← SimpleGraph.Walk.cons_tail_eq p hp_not_nil]
      simp [SimpleGraph.Walk.support_cons]
    exact ⟨hsnd_support, (p.adj_snd hp_not_nil).ne.symm, hsnd⟩

noncomputable def StrictSubdivisionModel.firstStepNeighbor
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (x : W)
    (y : H.neighborSet x) :
    G.neighborSet (M.branchVertex x) := by
  classical
  let p : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath y.2
  have hp_not_nil : Not p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p)
      (M.branchVertex_ne_of_adj y.2)
  exact ⟨p.snd, p.adj_snd hp_not_nil⟩

/-- The first host vertices on two distinct source edges incident with the
same branch vertex are distinct.  This is the local strictness fact used when
a source theta is expanded into three genuine host edges at a branch
vertex. -/
theorem StrictSubdivisionModel.edgePath_snd_ne_of_incident
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y z : W}
    (hxy : H.Adj x y)
    (hxz : H.Adj x z)
    (hyz : y ≠ z) :
    (M.edgePath hxy).snd ≠ (M.edgePath hxz).snd := by
  intro hsnd
  let p : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath hxy
  let q : G.Walk (M.branchVertex x) (M.branchVertex z) := M.edgePath hxz
  have hp_not_nil : ¬p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p)
      (M.branchVertex_ne_of_adj hxy)
  have hq_not_nil : ¬q.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := q)
      (M.branchVertex_ne_of_adj hxz)
  have hp_snd : p.snd ∈ p.support :=
    List.mem_of_mem_tail (p.snd_mem_tail_support hp_not_nil)
  have hq_snd : p.snd ∈ q.support := by
    exact List.mem_of_mem_tail (by
      simpa [p, q, hsnd] using q.snd_mem_tail_support hq_not_nil)
  have hedge_ne :
      ¬((x = x ∧ y = z) ∨ (x = z ∧ y = x)) := by
    rintro (hsame | hrev)
    · exact hyz hsame.2
    · exact hxz.ne hrev.1
  have hunique :
      ∀ w : W,
        (w = x ∨ w = y) →
          (w = x ∨ w = z) →
            w = x := by
    intro w hwxy hwxz
    rcases hwxy with rfl | rfl
    · rfl
    · rcases hwxz with hyx | hyz'
      · exact hyx
      · exact False.elim (hyz hyz')
  have hsnd_eq :
      p.snd = M.branchVertex x :=
    M.edgePath_support_inter_eq_common_branchVertex
      hxy hxz hedge_ne hunique
      (by exact hp_snd)
      (by simpa [q] using hq_snd)
  have hp_tail : p.snd ∈ p.support.tail :=
    p.snd_mem_tail_support hp_not_nil
  exact Walk.IsPath.start_notMem_tail_support
    (by simpa [p] using M.edgePath_isPath hxy)
    (by simpa [hsnd_eq] using hp_tail)

/-- Follow one source edge away from `x`, cross two source edges through the
opposite branch vertex `y`, and return backwards along another source edge
incident with `x`.  This is the alternate arm between the first host
neighbours on the two selected incident edge paths. -/
def StrictSubdivisionModel.aroundBranchWalk
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y a b : W}
    (hxa : H.Adj x a)
    (hay : H.Adj a y)
    (hyb : H.Adj y b)
    (hxb : H.Adj x b) :
    G.Walk (M.edgePath hxa).snd (M.edgePath hxb).snd :=
  ((((M.edgePath hxa).tail.append (M.edgePath hay)).append
      (M.edgePath hyb)).append
        (M.edgePath hxb).tail.reverse)

/-- The alternate walk around `y` never visits the original branch vertex
`x`, provided the four displayed source vertices are distinct where needed.
This is a direct consequence of strict-subdivision branch exclusion and the
simple first/last edge paths. -/
theorem StrictSubdivisionModel.branchVertex_not_mem_aroundBranchWalk_support
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y a b : W}
    (hxa : H.Adj x a)
    (hay : H.Adj a y)
    (hyb : H.Adj y b)
    (hxb : H.Adj x b)
    (hxy : x ≠ y) :
    M.branchVertex x ∉
      (M.aroundBranchWalk hxa hay hyb hxb).support := by
  let pxa : G.Walk (M.branchVertex x) (M.branchVertex a) :=
    M.edgePath hxa
  let pxb : G.Walk (M.branchVertex x) (M.branchVertex b) :=
    M.edgePath hxb
  have hpxa_not_nil : ¬pxa.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pxa)
      (M.branchVertex_ne_of_adj hxa)
  have hpxb_not_nil : ¬pxb.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pxb)
      (M.branchVertex_ne_of_adj hxb)
  have hpxa_tail :
      M.branchVertex x ∉ pxa.tail.support := by
    rw [pxa.support_tail_of_not_nil hpxa_not_nil]
    exact Walk.IsPath.start_notMem_tail_support
      (by simpa [pxa] using M.edgePath_isPath hxa)
  have hpxb_tail :
      M.branchVertex x ∉ pxb.tail.support := by
    rw [pxb.support_tail_of_not_nil hpxb_not_nil]
    exact Walk.IsPath.start_notMem_tail_support
      (by simpa [pxb] using M.edgePath_isPath hxb)
  have hay_avoid :
      M.branchVertex x ∉ (M.edgePath hay).support := by
    intro hxmem
    rcases
        (M.branchVertex_mem_edgePath_support_iff hay).mp hxmem with
      hxa' | hxy'
    · exact hxa.ne hxa'
    · exact hxy hxy'
  have hyb_avoid :
      M.branchVertex x ∉ (M.edgePath hyb).support := by
    intro hxmem
    rcases
        (M.branchVertex_mem_edgePath_support_iff hyb).mp hxmem with
      hxy' | hxb'
    · exact hxy hxy'
    · exact hxb.ne hxb'
  intro hxmem
  change
    M.branchVertex x ∈
      ((((M.edgePath hxa).tail.append (M.edgePath hay)).append
          (M.edgePath hyb)).append
        (M.edgePath hxb).tail.reverse).support at hxmem
  have houter :=
    (SimpleGraph.Walk.mem_support_append_iff
      (((M.edgePath hxa).tail.append (M.edgePath hay)).append
        (M.edgePath hyb))
      (M.edgePath hxb).tail.reverse).mp hxmem
  rcases houter with hleft | hright
  · have hleft' :=
      (SimpleGraph.Walk.mem_support_append_iff
        ((M.edgePath hxa).tail.append (M.edgePath hay))
        (M.edgePath hyb)).mp hleft
    rcases hleft' with hleft'' | hmiddle
    · have hleft''' :=
        (SimpleGraph.Walk.mem_support_append_iff
          (M.edgePath hxa).tail (M.edgePath hay)).mp hleft''
      rcases hleft''' with htail | hmiddle
      · exact hpxa_tail (by simpa [pxa] using htail)
      · exact hay_avoid hmiddle
    · exact hyb_avoid hmiddle
  · have htail' :
        M.branchVertex x ∈ pxb.tail.support.reverse := by
      simpa [pxb, SimpleGraph.Walk.support_reverse] using hright
    exact hpxb_tail (List.mem_reverse.mp htail')

/-- Graph-side data retained from a theta at one degree-three branch vertex.
The three displayed neighbours are joined pairwise away from the branch
vertex.  Keeping all three routes lets a later embedding argument choose a
pair after inspecting the orientations in a selected face. -/
structure ThetaBranchPaths {V : Type v} (G : SimpleGraph V) where
  branch : V
  first : V
  second : V
  third : V
  adj_first : G.Adj branch first
  adj_second : G.Adj branch second
  adj_third : G.Adj branch third
  first_ne_second : first ≠ second
  first_ne_third : first ≠ third
  second_ne_third : second ≠ third
  firstSecond : G.Walk first second
  firstThird : G.Walk first third
  secondThird : G.Walk second third
  branch_not_mem_firstSecond : branch ∉ firstSecond.support
  branch_not_mem_firstThird : branch ∉ firstThird.support
  branch_not_mem_secondThird : branch ∉ secondThird.support

/-- A strict subdivision of a three-arm source supplies
`ThetaBranchPaths` at the chosen degree-three source vertex. -/
def StrictSubdivisionModel.thetaBranchPaths
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y a b c : W}
    (hxa : H.Adj x a)
    (hxb : H.Adj x b)
    (hxc : H.Adj x c)
    (hay : H.Adj a y)
    (hby : H.Adj b y)
    (hcy : H.Adj c y)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c)
    (hxy : x ≠ y) :
    ThetaBranchPaths G where
  branch := M.branchVertex x
  first := (M.edgePath hxa).snd
  second := (M.edgePath hxb).snd
  third := (M.edgePath hxc).snd
  adj_first :=
    (M.edgePath hxa).adj_snd
      (SimpleGraph.Walk.not_nil_of_ne
        (M.branchVertex_ne_of_adj hxa))
  adj_second :=
    (M.edgePath hxb).adj_snd
      (SimpleGraph.Walk.not_nil_of_ne
        (M.branchVertex_ne_of_adj hxb))
  adj_third :=
    (M.edgePath hxc).adj_snd
      (SimpleGraph.Walk.not_nil_of_ne
        (M.branchVertex_ne_of_adj hxc))
  first_ne_second := M.edgePath_snd_ne_of_incident hxa hxb hab
  first_ne_third := M.edgePath_snd_ne_of_incident hxa hxc hac
  second_ne_third := M.edgePath_snd_ne_of_incident hxb hxc hbc
  firstSecond := M.aroundBranchWalk hxa hay hby.symm hxb
  firstThird := M.aroundBranchWalk hxa hay hcy.symm hxc
  secondThird := M.aroundBranchWalk hxb hby hcy.symm hxc
  branch_not_mem_firstSecond :=
    M.branchVertex_not_mem_aroundBranchWalk_support
      hxa hay hby.symm hxb hxy
  branch_not_mem_firstThird :=
    M.branchVertex_not_mem_aroundBranchWalk_support
      hxa hay hcy.symm hxc hxy
  branch_not_mem_secondThird :=
    M.branchVertex_not_mem_aroundBranchWalk_support
      hxb hby hcy.symm hxc hxy

/-- Alternate host walk between the first step of a direct source arm
`x--y` and the first step of an arm `x--a--y`. -/
def StrictSubdivisionModel.directArmAlternateWalk
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y a : W}
    (hxy : H.Adj x y)
    (hay : H.Adj a y)
    (hxa : H.Adj x a) :
    G.Walk (M.edgePath hxy).snd (M.edgePath hxa).snd :=
  (((M.edgePath hxy).tail.append (M.edgePath hay).reverse).append
    (M.edgePath hxa).tail.reverse)

theorem StrictSubdivisionModel.branchVertex_not_mem_directArmAlternateWalk_support
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y a : W}
    (hxy : H.Adj x y)
    (hay : H.Adj a y)
    (hxa : H.Adj x a) :
    M.branchVertex x ∉
      (M.directArmAlternateWalk hxy hay hxa).support := by
  let pxy : G.Walk (M.branchVertex x) (M.branchVertex y) :=
    M.edgePath hxy
  let pxa : G.Walk (M.branchVertex x) (M.branchVertex a) :=
    M.edgePath hxa
  have hpxy_not_nil : ¬pxy.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pxy)
      (M.branchVertex_ne_of_adj hxy)
  have hpxa_not_nil : ¬pxa.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pxa)
      (M.branchVertex_ne_of_adj hxa)
  have hpxy_tail :
      M.branchVertex x ∉ pxy.tail.support := by
    rw [pxy.support_tail_of_not_nil hpxy_not_nil]
    exact Walk.IsPath.start_notMem_tail_support
      (by simpa [pxy] using M.edgePath_isPath hxy)
  have hpxa_tail :
      M.branchVertex x ∉ pxa.tail.support := by
    rw [pxa.support_tail_of_not_nil hpxa_not_nil]
    exact Walk.IsPath.start_notMem_tail_support
      (by simpa [pxa] using M.edgePath_isPath hxa)
  have hay_avoid :
      M.branchVertex x ∉ (M.edgePath hay).support := by
    intro hxmem
    rcases
        (M.branchVertex_mem_edgePath_support_iff hay).mp hxmem with
      hxa' | hxy'
    · exact hxa.ne hxa'
    · exact hxy.ne hxy'
  intro hxmem
  change
    M.branchVertex x ∈
      (((M.edgePath hxy).tail.append (M.edgePath hay).reverse).append
        (M.edgePath hxa).tail.reverse).support at hxmem
  have houter :=
    (SimpleGraph.Walk.mem_support_append_iff
      ((M.edgePath hxy).tail.append (M.edgePath hay).reverse)
      (M.edgePath hxa).tail.reverse).mp hxmem
  rcases houter with hleft | hright
  · have hleft' :=
      (SimpleGraph.Walk.mem_support_append_iff
        (M.edgePath hxy).tail (M.edgePath hay).reverse).mp hleft
    rcases hleft' with htail | hmiddle
    · exact hpxy_tail (by simpa [pxy] using htail)
    · have hmiddle' :
          M.branchVertex x ∈ (M.edgePath hay).support.reverse := by
        simpa [SimpleGraph.Walk.support_reverse] using hmiddle
      exact hay_avoid (List.mem_reverse.mp hmiddle')
  · have htail' :
        M.branchVertex x ∈ pxa.tail.support.reverse := by
      simpa [pxa, SimpleGraph.Walk.support_reverse] using hright
    exact hpxa_tail (List.mem_reverse.mp htail')

/-- Strict-subdivision constructor for the suppressed-edge theta source:
one arm is the direct source edge and the other two pass through the displayed
degree-two source vertices. -/
def StrictSubdivisionModel.edgeThetaBranchPaths
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y a b : W}
    (hxy : H.Adj x y)
    (hxa : H.Adj x a)
    (hay : H.Adj a y)
    (hxb : H.Adj x b)
    (hby : H.Adj b y)
    (hab : a ≠ b) :
    ThetaBranchPaths G where
  branch := M.branchVertex x
  first := (M.edgePath hxy).snd
  second := (M.edgePath hxa).snd
  third := (M.edgePath hxb).snd
  adj_first :=
    (M.edgePath hxy).adj_snd
      (SimpleGraph.Walk.not_nil_of_ne
        (M.branchVertex_ne_of_adj hxy))
  adj_second :=
    (M.edgePath hxa).adj_snd
      (SimpleGraph.Walk.not_nil_of_ne
        (M.branchVertex_ne_of_adj hxa))
  adj_third :=
    (M.edgePath hxb).adj_snd
      (SimpleGraph.Walk.not_nil_of_ne
        (M.branchVertex_ne_of_adj hxb))
  first_ne_second := M.edgePath_snd_ne_of_incident hxy hxa hay.ne.symm
  first_ne_third := M.edgePath_snd_ne_of_incident hxy hxb hby.ne.symm
  second_ne_third := M.edgePath_snd_ne_of_incident hxa hxb hab
  firstSecond := M.directArmAlternateWalk hxy hay hxa
  firstThird := M.directArmAlternateWalk hxy hby hxb
  secondThird := M.aroundBranchWalk hxa hay hby.symm hxb
  branch_not_mem_firstSecond :=
    M.branchVertex_not_mem_directArmAlternateWalk_support hxy hay hxa
  branch_not_mem_firstThird :=
    M.branchVertex_not_mem_directArmAlternateWalk_support hxy hby hxb
  branch_not_mem_secondThird :=
    M.branchVertex_not_mem_aroundBranchWalk_support
      hxa hay hby.symm hxb hxy.ne

theorem StrictSubdivisionModel.firstStepNeighbor_injective
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (x : W) :
    Function.Injective (M.firstStepNeighbor x) := by
  classical
  intro y z hyz_image
  apply Subtype.ext
  by_contra hyz
  let py : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath y.2
  let pz : G.Walk (M.branchVertex x) (M.branchVertex z) := M.edgePath z.2
  have hsnd :
      py.snd = pz.snd := by
    exact congr_arg Subtype.val hyz_image
  have hnot_same :
      ¬ ((x = x ∧ (y : W) = z) ∨ (x = z ∧ (y : W) = x)) := by
    intro hsame
    rcases hsame with hsame | hsame
    · exact hyz hsame.2
    · exact z.2.ne hsame.1
  have hy_cases := M.edgePath_snd_eq_branch_or_internal y.2
  have hz_cases := M.edgePath_snd_eq_branch_or_internal z.2
  dsimp [py] at hy_cases
  dsimp [pz] at hz_cases
  rcases hy_cases with hy_branch | hy_internal
  · rcases hz_cases with hz_branch | hz_internal
    · exact hyz (M.branchVertex_injective (by
        calc
          M.branchVertex (y : W) = py.snd := hy_branch.symm
          _ = pz.snd := hsnd
          _ = M.branchVertex (z : W) := hz_branch))
    · exact
        M.no_internal_branch_vertices' z.2 hz_internal (y : W) (by
          calc
            pz.snd = py.snd := hsnd.symm
            _ = M.branchVertex (y : W) := hy_branch)
  · rcases hz_cases with hz_branch | hz_internal
    · exact
        M.no_internal_branch_vertices' y.2 hy_internal (z : W) (by
          calc
            py.snd = pz.snd := hsnd
            _ = M.branchVertex (z : W) := hz_branch)
    · exact
        Set.disjoint_left.mp
          (M.internally_disjoint_edge_paths' y.2 z.2 hnot_same)
          hy_internal (by
            show py.snd ∈ Walk.InternalVertices pz
            rw [hsnd]
            exact hz_internal)

theorem StrictSubdivisionModel.source_degree_le_branchVertex_degree
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (x : W)
    [Fintype (H.neighborSet x)]
    [Fintype (G.neighborSet (M.branchVertex x))] :
    H.degree x <= G.degree (M.branchVertex x) := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective
    (M.firstStepNeighbor x) (M.firstStepNeighbor_injective x)

/-- Host vertices whose degree is smaller than the source degree cannot be
branch vertices of a strict subdivision. -/
theorem StrictSubdivisionModel.branchVertex_ne_of_host_degree_lt_source_degree
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (x : W)
    [Fintype (H.neighborSet x)]
    [Fintype (G.neighborSet (M.branchVertex x))]
    {v : V}
    [Fintype (G.neighborSet v)]
    (hdegree : G.degree v < H.degree x) :
    M.branchVertex x ≠ v := by
  intro hx
  subst v
  have hsource :
      H.degree x <= G.degree (M.branchVertex x) :=
    M.source_degree_le_branchVertex_degree x
  omega

/-- If a host vertex of degree at most two is internal on one model path, then
any ambient edge incident with it is an edge of that same path.  This packages
the local degree-two suppression fact at the strict-subdivision level. -/
theorem StrictSubdivisionModel.neighbor_mem_edgePath_toSubgraph_of_internal_degree_le_two
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W}
    (hxy : H.Adj x y)
    {v w : V}
    (hv : v ∈ Walk.InternalVertices (M.edgePath hxy))
    [Fintype (G.neighborSet v)]
    (hdegree : G.degree v <= 2)
    (hvw : G.Adj v w) :
    w ∈ (M.edgePath hxy).toSubgraph.neighborSet v :=
  Walk.IsPath.neighbor_mem_toSubgraph_of_internal_degree_le_two
    (G := G) (p := M.edgePath hxy) (M.edgePath_isPath hxy)
    hv hdegree hvw

theorem highDegree_ncard_ge_of_containsStrictSubdivision
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    [Fintype W] [DecidableRel H.Adj]
    [Fintype V] [DecidableRel G.Adj]
    {d : Nat}
    (hdeg : forall x : W, d <= H.degree x)
    (h : ContainsStrictSubdivision H G) :
    Fintype.card W <= {v : V | d <= G.degree v}.ncard := by
  classical
  rcases h with ⟨M⟩
  let e : W ↪ {v : V | d <= G.degree v} := {
    toFun := fun x =>
      have hbranch_degree : H.degree x <= G.degree (M.branchVertex x) := by
        letI : Fintype (H.neighborSet x) := inferInstance
        letI : Fintype (G.neighborSet (M.branchVertex x)) := inferInstance
        exact M.source_degree_le_branchVertex_degree x
      ⟨M.branchVertex x, le_trans (hdeg x) hbranch_degree⟩
    inj' := by
      intro x y hxy
      exact M.branchVertex_injective (Subtype.ext_iff.mp hxy) }
  have hcard : Fintype.card W <= Fintype.card {v : V | d <= G.degree v} :=
    Fintype.card_le_of_injective e e.injective
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact hcard


end Schematic.Math.GraphTheory
