import Schematic.Math.GraphTheory.Subdivisions.Models

/-! Finite graph-minor models and their elementary transports. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

structure MinorModel {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W -> G.Subgraph
  connected : forall x : W, (branch x).coe.Connected
  nonempty : forall x : W, (branch x).verts.Nonempty
  vertex_disjoint :
    forall x y : W, x ≠ y -> Disjoint (branch x).verts (branch y).verts
  edge_realized :
    forall {x y : W},
      H.Adj x y ->
      Exists fun a : V =>
        Exists fun b : V =>
        a ∈ (branch x).verts ∧ b ∈ (branch y).verts ∧ G.Adj a b

def ContainsMinor {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (MinorModel H G)

def MinorModel.map
    {W : Type u} {V : Type v} {U : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (M : MinorModel H G) :
    MinorModel H G' where
  branch x := (M.branch x).map f
  connected := by
    intro x
    rw [SimpleGraph.connected_iff]
    constructor
    · intro a b
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      simp only [SimpleGraph.Subgraph.map_verts, Set.mem_image] at ha hb
      rcases ha with ⟨a₀, ha₀, rfl⟩
      rcases hb with ⟨b₀, hb₀, rfl⟩
      let F : (M.branch x).coe →g ((M.branch x).map f).coe :=
        ⟨fun z => ⟨f z, by exact ⟨z, z.2, rfl⟩⟩, by
          intro y z hyz
          exact ⟨y, z, hyz, rfl, rfl⟩⟩
      exact ((M.connected x) ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩).map F
    · obtain ⟨a, ha⟩ := M.nonempty x
      exact ⟨⟨f a, by exact ⟨a, ha, rfl⟩⟩⟩
  nonempty := by
    intro x
    obtain ⟨a, ha⟩ := M.nonempty x
    exact ⟨f a, by exact ⟨a, ha, rfl⟩⟩
  vertex_disjoint := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro z hzx hzy
    simp only [SimpleGraph.Subgraph.map_verts, Set.mem_image] at hzx hzy
    rcases hzx with ⟨a, ha, haz⟩
    rcases hzy with ⟨b, hb, hbz⟩
    have hab : a = b := hf (haz.trans hbz.symm)
    exact (Set.disjoint_left.mp (M.vertex_disjoint x y hxy) ha)
      (by simpa [hab] using hb)
  edge_realized := by
    intro x y hxy
    obtain ⟨a, b, ha, hb, hab⟩ := M.edge_realized hxy
    exact ⟨f a, f b, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, f.map_adj hab⟩

theorem ContainsMinor.map
    {W : Type u} {V : Type v} {U : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (h : ContainsMinor H G) :
    ContainsMinor H G' := by
  rcases h with ⟨M⟩
  exact ⟨M.map f hf⟩

theorem ContainsMinor.of_le
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G G' : SimpleGraph V}
    (hGG' : G ≤ G')
    (h : ContainsMinor H G) :
    ContainsMinor H G' :=
  h.map (.ofLE hGG') Function.injective_id

theorem card_le_of_containsMinor
    {W : Type u} {V : Type v}
    [Fintype W] [Fintype V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (h : ContainsMinor H G) :
    Fintype.card W <= Fintype.card V := by
  classical
  rcases h with ⟨M⟩
  let rep : W -> V := fun x => (M.nonempty x).some
  have hrep : forall x : W, rep x ∈ (M.branch x).verts := by
    intro x
    exact (M.nonempty x).some_mem
  have hinj : Function.Injective rep := by
    intro x y hxy
    by_contra hne
    exact (Set.disjoint_left.mp (M.vertex_disjoint x y hne) (hrep x))
      (by simpa [rep, hxy] using hrep y)
  exact Fintype.card_le_of_injective rep hinj


end Schematic.Math.GraphTheory
