import Schematic.Math.GraphTheory.Minors.Rerouting.LinkageSymmetry

/-! Endpoint-clean paths and linkages between vertex sets. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-!
## Set-to-set linkages

GM IX uses `X -> Y` paths, not merely paths whose two displayed endpoints
belong to `X` and `Y`.  Such a path has its initial vertex as its only vertex
in `X`, and its terminal vertex as its only vertex in `Y`.  Keeping those
conditions in the linkage object prevents fixed-terminal Menger statements
from being used as if they already supplied the source-clean paths required
by GM IX (2.2).
-/

/-- One path normalized from a source set to a target set. -/
structure SetToSetPathData
    {u v : V}
    (p : G.Walk u v)
    (X Y : Set V) where
  source : V
  target : V
  source_mem : source ∈ X
  target_mem : target ∈ Y
  path : G.Walk source target
  isPath : path.IsPath
  support_subset : {z : V | z ∈ path.support} ⊆ {z : V | z ∈ p.support}
  source_clean :
    forall z : V, z ∈ path.support -> z ∈ X -> z = source
  target_clean :
    forall z : V, z ∈ path.support -> z ∈ Y -> z = target

/--
Normalize an ordinary path whose start lies in `X` and whose end lies in `Y`.

The normalized path starts at the last `X`-vertex of the original path and
ends at the first subsequent `Y`-vertex.  This is the literal path convention
used in GM IX (2.2).
-/
theorem Walk.IsPath.exists_setToSetPathData
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (X Y : Set V)
    (hu : u ∈ X)
    (hv : v ∈ Y) :
    Nonempty (SetToSetPathData p X Y) := by
  classical
  obtain ⟨x, hxrev, hxX, hq_path, hq_source_clean, hq_subset⟩ :=
    Walk.IsPath.exists_suffix_from_last_mem hp X hu
  let q : G.Walk x v := (p.reverse.takeUntil x hxrev).reverse
  obtain ⟨y, hyq, hyY, hr_target_clean⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem hq_path Y hv
  let r : G.Walk x y := q.takeUntil y hyq
  refine ⟨{
    source := x
    target := y
    source_mem := hxX
    target_mem := hyY
    path := r
    isPath := hq_path.takeUntil hyq
    support_subset := ?_
    source_clean := ?_
    target_clean := ?_
  }⟩
  · intro z hz
    have hzq : z ∈ q.support :=
      SimpleGraph.Walk.support_takeUntil_subset q hyq hz
    exact hq_subset z hzq
  · intro z hz hzX
    have hzq : z ∈ q.support :=
      SimpleGraph.Walk.support_takeUntil_subset q hyq hz
    exact hq_source_clean z hzq hzX
  · intro z hz hzY
    exact hr_target_clean z (by simpa [r] using hz) hzY

/--
Three mutually vertex-disjoint paths from a vertex set `X` to a vertex set
`Y`, in the exact sense of GM IX: each path has no other vertex in either
endpoint set.
-/
structure ThreeSetLinkage
    (G : SimpleGraph V)
    (X Y : Set V) where
  source : Fin 3 -> V
  target : Fin 3 -> V
  source_mem : forall i : Fin 3, source i ∈ X
  target_mem : forall i : Fin 3, target i ∈ Y
  source_injective : Function.Injective source
  target_injective : Function.Injective target
  path : forall i : Fin 3, G.Walk (source i) (target i)
  isPath : forall i : Fin 3, (path i).IsPath
  pairwise_vertex_disjoint :
    forall i j : Fin 3, i ≠ j ->
      Disjoint {v : V | v ∈ (path i).support}
        {v : V | v ∈ (path j).support}
  source_clean :
    forall i : Fin 3, forall z : V,
      z ∈ (path i).support -> z ∈ X -> z = source i
  target_clean :
    forall i : Fin 3, forall z : V,
      z ∈ (path i).support -> z ∈ Y -> z = target i

/--
Normalize an ordinary three-linkage to a GM IX set-to-set linkage.

Each path is normalized independently.  Since normalization only deletes
initial and terminal segments, pairwise vertex-disjointness is inherited.
-/
noncomputable def ThreeVertexLinkage.toThreeSetLinkage
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right)
    (X Y : Set V)
    (hleft : forall i : Fin 3, left i ∈ X)
    (hright : forall i : Fin 3, right i ∈ Y) :
    ThreeSetLinkage G X Y := by
  classical
  let D : forall i : Fin 3, SetToSetPathData (L.path i) X Y :=
    fun i =>
      Classical.choice
        (Walk.IsPath.exists_setToSetPathData (L.isPath i) X Y
          (hleft i) (hright (L.targetEquiv i)))
  refine {
    source := fun i => (D i).source
    target := fun i => (D i).target
    source_mem := fun i => (D i).source_mem
    target_mem := fun i => (D i).target_mem
    source_injective := ?_
    target_injective := ?_
    path := fun i => (D i).path
    isPath := fun i => (D i).isPath
    pairwise_vertex_disjoint := ?_
    source_clean := fun i => (D i).source_clean
    target_clean := fun i => (D i).target_clean
  }
  · intro i j hij
    by_contra hne
    exact
      Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hne)
        ((D i).support_subset (D i).path.start_mem_support)
        ((D j).support_subset
          (by
            change (D i).source = (D j).source at hij
            exact hij.symm ▸ (D j).path.start_mem_support))
  · intro i j hij
    by_contra hne
    exact
      Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hne)
        ((D i).support_subset (D i).path.end_mem_support)
        ((D j).support_subset
          (by
            change (D i).target = (D j).target at hij
            exact hij.symm ▸ (D j).path.end_mem_support))
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact
      Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij)
        ((D i).support_subset hzi)
        ((D j).support_subset hzj)

/--
A partial family of mutually disjoint `X -> Y` paths.

Unlike `PartialThreeVertexLinkage`, the endpoints are stored directly rather
than as indices into two preselected triples.  This is the correct state for
the augmenting-path proof of GM IX (2.2): selected endpoints are fixed, while
the endpoints of paths added later remain free to move inside `X` and `Y`.
-/
structure PartialSetLinkage
    (G : SimpleGraph V)
    (X Y : Set V)
    (n : Nat) where
  source : Fin n -> V
  target : Fin n -> V
  source_mem : forall i : Fin n, source i ∈ X
  target_mem : forall i : Fin n, target i ∈ Y
  source_injective : Function.Injective source
  target_injective : Function.Injective target
  path : forall i : Fin n, G.Walk (source i) (target i)
  isPath : forall i : Fin n, (path i).IsPath
  pairwise_vertex_disjoint :
    forall i j : Fin n, i ≠ j ->
      Disjoint {v : V | v ∈ (path i).support}
        {v : V | v ∈ (path j).support}
  source_clean :
    forall i : Fin n, forall z : V,
      z ∈ (path i).support -> z ∈ X -> z = source i
  target_clean :
    forall i : Fin n, forall z : V,
      z ∈ (path i).support -> z ∈ Y -> z = target i


end Schematic.Math.GraphTheory
