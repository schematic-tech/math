import Schematic.Math.GraphTheory.Connectivity.Definitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
Connected-component supports and induced connected subgraphs.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem Connected.exists_adjacent_crossing
    (hG : G.Connected)
    {S : Set V}
    (hS : S.Nonempty)
    (hS_compl : Sᶜ.Nonempty) :
    Exists fun u : V =>
      u ∈ S ∧
        Exists fun v : V => v ∉ S ∧ G.Adj u v := by
  classical
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hS_compl
  obtain ⟨p⟩ := hG u v
  obtain ⟨⟨⟨x, y⟩, hxy⟩, _hd, hxS, hyS⟩ := p.exists_boundary_dart S hu hv
  exact ⟨x, hxS, y, hyS, hxy⟩

theorem exists_not_reachable_from_of_not_connected
    [Nonempty V]
    (root : V)
    (hnot : ¬ G.Connected) :
    Exists fun v : V => ¬ G.Reachable root v := by
  by_contra hnone
  have hroot_reaches : forall v : V, G.Reachable root v := by
    intro v
    by_contra hv
    exact hnone ⟨v, hv⟩
  exact hnot {
    preconnected := by
      intro u v
      exact (hroot_reaches u).symm.trans (hroot_reaches v)
    nonempty := inferInstance
  }

theorem exists_connectedComponent_not_mem_of_not_connected
    [Nonempty V]
    (root : V)
    (hnot : ¬ G.Connected) :
    Exists fun C : G.ConnectedComponent => root ∉ C.supp := by
  rcases exists_not_reachable_from_of_not_connected
      (G := G) root hnot with
    ⟨v, hvnot⟩
  let C : G.ConnectedComponent := G.connectedComponentMk v
  refine ⟨C, ?_⟩
  intro hrootC
  exact hvnot
    (SimpleGraph.ConnectedComponent.reachable_of_mem_supp
      C hrootC SimpleGraph.ConnectedComponent.connectedComponentMk_mem)

theorem connected_induce_exists_walk_support_subset
    {A : Set V}
    (hA : (G.induce A).Connected)
    {u v : V}
    (hu : u ∈ A)
    (hv : v ∈ A) :
    Exists fun p : G.Walk u v =>
      forall x : V, x ∈ p.support -> x ∈ A := by
  obtain ⟨p⟩ := hA ⟨u, hu⟩ ⟨v, hv⟩
  let q : G.Walk u v := p.map (SimpleGraph.Embedding.induce A).toHom
  refine ⟨q, ?_⟩
  intro x hx
  change x ∈ (p.map (SimpleGraph.Embedding.induce A).toHom).support at hx
  simp only [SimpleGraph.Walk.support_map, List.mem_map] at hx
  rcases hx with ⟨y, _hy, rfl⟩
  exact y.2

theorem connected_induce_exists_path_support_subset
    [DecidableEq V]
    {A : Set V}
    (hA : (G.induce A).Connected)
    {u v : V}
    (hu : u ∈ A)
    (hv : v ∈ A) :
    Exists fun p : G.Walk u v =>
      p.IsPath ∧ forall x : V, x ∈ p.support -> x ∈ A := by
  obtain ⟨p, hp_support⟩ :=
    connected_induce_exists_walk_support_subset (G := G) hA hu hv
  refine ⟨(p.toPath : G.Walk u v), p.toPath.property, ?_⟩
  intro x hx
  exact hp_support x (SimpleGraph.Walk.support_toPath_subset p hx)

theorem reachable_induce_exists_path_support_subset
    [DecidableEq V]
    {A : Set V} {u v : V}
    (hu : u ∈ A)
    (hv : v ∈ A)
    (hreach :
      (G.induce A).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    Exists fun p : G.Walk u v =>
      p.IsPath ∧ forall x : V, x ∈ p.support -> x ∈ A := by
  obtain ⟨p⟩ := hreach
  let q : G.Walk u v := p.map (SimpleGraph.Embedding.induce A).toHom
  refine ⟨(q.toPath : G.Walk u v), q.toPath.property, ?_⟩
  intro x hx
  have hxq : x ∈ q.support :=
    SimpleGraph.Walk.support_toPath_subset q hx
  change x ∈ (p.map (SimpleGraph.Embedding.induce A).toHom).support at hxq
  simp only [SimpleGraph.Walk.support_map, List.mem_map] at hxq
  rcases hxq with ⟨y, _hy, rfl⟩
  exact y.2

theorem ncard_iUnion_fin3_le_of_forall_ncard_le_one
    [Fintype V]
    {A : Fin 3 -> Set V}
    (hA : forall i : Fin 3, (A i).ncard <= 1) :
    (⋃ i : Fin 3, A i).ncard <= 3 := by
  classical
  have hunion : (⋃ i : Fin 3, A i) = (A 0 ∪ A 1) ∪ A 2 := by
    ext x
    constructor
    · rintro ⟨S, ⟨i, rfl⟩, hxi⟩
      fin_cases i
      · exact Or.inl (Or.inl (by simpa using hxi))
      · exact Or.inl (Or.inr (by simpa using hxi))
      · exact Or.inr (by simpa using hxi)
    · intro hx
      rcases hx with hx01 | hx2
      · rcases hx01 with hx0 | hx1
        · exact ⟨A 0, ⟨0, rfl⟩, hx0⟩
        · exact ⟨A 1, ⟨1, rfl⟩, hx1⟩
      · exact ⟨A 2, ⟨2, rfl⟩, hx2⟩
  rw [hunion]
  have h01 : (A 0 ∪ A 1).ncard <= 2 := by
    calc
      (A 0 ∪ A 1).ncard <= (A 0).ncard + (A 1).ncard :=
        Set.ncard_union_le (A 0) (A 1)
      _ <= 2 := by
        have h0 := hA 0
        have h1 := hA 1
        omega
  calc
    ((A 0 ∪ A 1) ∪ A 2).ncard <= (A 0 ∪ A 1).ncard + (A 2).ncard :=
      Set.ncard_union_le (A 0 ∪ A 1) (A 2)
    _ <= 3 := by
      have h2 := hA 2
      omega

theorem reachable_induce_compl_mem_of_closed
    {S K : Set V}
    {u v : (Sᶜ : Set V)}
    (huK : (u : V) ∈ K)
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ S -> Not (G.Adj a b))
    (hreach : (G.induce Sᶜ).Reachable u v) :
    (v : V) ∈ K := by
  classical
  let H : (G.induce Sᶜ).Subgraph :=
    (⊤ : (G.induce Sᶜ).Subgraph).induce {x : (Sᶜ : Set V) | (x : V) ∈ K}
  have huH : u ∈ H.verts := by
    simp [H, huK]
  have hvH : v ∈ H.verts :=
    SimpleGraph.Reachable.mem_subgraphVerts hreach (H := H) ?_ huH
  · simpa [H] using hvH
  intro x hxH y hxy
  have hxK : (x : V) ∈ K := by
    simpa [H] using hxH
  have hyK : (y : V) ∈ K := by
    by_contra hyK
    exact hclosed hxK hyK y.2 (by simpa using hxy)
  simp [H, hxK, hyK]
  exact hxy

def induceComponentSupport
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    Set V :=
  {v | Exists fun hv : v ∈ A => (⟨v, hv⟩ : A) ∈ C.supp}

def nestedInduceComponentSupport
    {A : Set V}
    {B : Set A}
    (C : ((G.induce A).induce B).ConnectedComponent) :
    Set V :=
  {v | Exists fun hv : v ∈ A =>
    (⟨v, hv⟩ : A) ∈ induceComponentSupport (G := G.induce A) C}

def relativeVertexBoundary
    (G : SimpleGraph V)
    (K S : Set V) :
    Set V :=
  {v | v ∈ S ∧ Exists fun u : V => u ∈ K ∧ G.Adj u v}

theorem nestedInduceComponentSupport_subset
    {A : Set V}
    {B : Set A}
    (C : ((G.induce A).induce B).ConnectedComponent) :
    nestedInduceComponentSupport (G := G) C ⊆ A := by
  intro v hv
  exact hv.choose

theorem induceComponentSupport_subset
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    induceComponentSupport (G := G) C ⊆ A := by
  intro v hv
  exact hv.choose

theorem induceComponentSupport_disjoint_of_ne
    {A : Set V}
    {C D : (G.induce A).ConnectedComponent}
    (hCD : C ≠ D) :
    Disjoint
      (induceComponentSupport (G := G) C)
      (induceComponentSupport (G := G) D) := by
  rw [Set.disjoint_left]
  intro v hvC hvD
  rcases hvC with ⟨hvA, hvCsupp⟩
  rcases hvD with ⟨hvA', hvDsupp⟩
  apply hCD
  refine SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (v := (⟨v, hvA⟩ : A)) hvCsupp ?_
  have hsub : (⟨v, hvA⟩ : A) = ⟨v, hvA'⟩ := Subtype.ext rfl
  simpa [hsub] using hvDsupp

theorem induceComponentSupport_nonempty
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    (induceComponentSupport (G := G) C).Nonempty := by
  obtain ⟨u, huC⟩ := C.nonempty_supp
  exact ⟨u, u.2, huC⟩

theorem induceComponentSupport_eq_of_connected
    {A : Set V}
    (hA : (G.induce A).Connected)
    (C : (G.induce A).ConnectedComponent) :
    induceComponentSupport (G := G) C = A := by
  ext v
  constructor
  · intro hv
    exact induceComponentSupport_subset (G := G) C hv
  · intro hvA
    obtain ⟨u, huC⟩ := C.nonempty_supp
    have hreach :
        (G.induce A).Reachable u (⟨v, hvA⟩ : A) :=
      hA u ⟨v, hvA⟩
    have hu_eq :
        (G.induce A).connectedComponentMk u = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp huC
    have hvC :
        (⟨v, hvA⟩ : A) ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      rw [← hu_eq]
      exact (SimpleGraph.ConnectedComponent.sound hreach).symm
    exact ⟨hvA, hvC⟩

theorem induceComponentSupport_mem_of_adj
    {A : Set V}
    (C : (G.induce A).ConnectedComponent)
    {x y : V}
    (hx : x ∈ induceComponentSupport (G := G) C)
    (hyA : y ∈ A)
    (hxy : G.Adj x y) :
    y ∈ induceComponentSupport (G := G) C := by
  rcases hx with ⟨hxA, hxC⟩
  have hxyA : (G.induce A).Adj ⟨x, hxA⟩ ⟨y, hyA⟩ := hxy
  exact ⟨hyA, C.mem_supp_of_adj_mem_supp hxC hxyA⟩

theorem nestedInduceComponentSupport_nonempty
    {A : Set V}
    {B : Set A}
    (C : ((G.induce A).induce B).ConnectedComponent) :
    (nestedInduceComponentSupport (G := G) C).Nonempty := by
  rcases induceComponentSupport_nonempty (G := G.induce A) C with
    ⟨u, hu⟩
  exact ⟨u, u.2, hu⟩

theorem nestedInduceComponentSupport_mem_of_adj
    {A : Set V}
    {B : Set A}
    (C : ((G.induce A).induce B).ConnectedComponent)
    {x y : V}
    (hx : x ∈ nestedInduceComponentSupport (G := G) C)
    (hyA : y ∈ A)
    (hyB : (⟨y, hyA⟩ : A) ∈ B)
    (hxy : G.Adj x y) :
    y ∈ nestedInduceComponentSupport (G := G) C := by
  rcases hx with ⟨hxA, hxC⟩
  exact
    ⟨hyA,
      induceComponentSupport_mem_of_adj
        (G := G.induce A) C hxC hyB hxy⟩

theorem nestedInduceComponentSupport_closed_in_delete_of_insert_componentSupport
    {root : V}
    (C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent)
    {S : Set V}
    (hS : S = insert root (induceComponentSupport (G := G) C))
    {c : S}
    (L : ((G.induce S).induce (({c} : Set S)ᶜ)).ConnectedComponent)
    (hroot_not :
      root ∉ nestedInduceComponentSupport (G := G) L) :
    forall {a b : V},
      a ∈ nestedInduceComponentSupport (G := G) L ->
        b ∉ nestedInduceComponentSupport (G := G) L ->
          b ∉ ({(c : V)} : Set V) -> Not (G.Adj a b) := by
  classical
  intro a b ha hb hb_ne_c hab
  have haS : a ∈ S :=
    nestedInduceComponentSupport_subset (G := G) L ha
  have haC : a ∈ induceComponentSupport (G := G) C := by
    have haS' : a ∈ insert root (induceComponentSupport (G := G) C) := by
      simpa [hS] using haS
    rcases haS' with haroot | haC
    · exact False.elim (hroot_not (by simpa [haroot] using ha))
    · exact haC
  by_cases hbS : b ∈ S
  · have hbT : (⟨b, hbS⟩ : S) ∈ (({c} : Set S)ᶜ) := by
      intro hbc
      have hbcV : b = (c : V) := congrArg Subtype.val hbc
      exact hb_ne_c (by simp [hbcV])
    exact hb
      (nestedInduceComponentSupport_mem_of_adj
        (G := G) L ha hbS hbT hab)
  · have hbroot : b ≠ root := by
      intro hbroot
      exact hbS (by
        rw [hS]
        exact Or.inl hbroot)
    have hbA : b ∈ (({root} : Set V)ᶜ) := by
      simp [hbroot]
    have hbC : b ∈ induceComponentSupport (G := G) C :=
      induceComponentSupport_mem_of_adj (G := G) C haC hbA hab
    exact hbS (by
      rw [hS]
      exact Or.inr hbC)

theorem induceComponentSupport_closed_in_induce
    {A : Set V}
    (C : (G.induce A).ConnectedComponent)
    {x y : V}
    (hx : x ∈ induceComponentSupport (G := G) C)
    (hyA : y ∈ A)
    (hxy : G.Adj x y) :
    y ∈ induceComponentSupport (G := G) C :=
  induceComponentSupport_mem_of_adj (G := G) C hx hyA hxy

theorem induceComponentSupport_closed_with_relativeBoundary
    {S : Set V}
    (C : (G.induce Sᶜ).ConnectedComponent) :
    forall {a b : V},
      a ∈ induceComponentSupport (G := G) C ->
        b ∉ induceComponentSupport (G := G) C ->
          b ∉ relativeVertexBoundary G (induceComponentSupport (G := G) C) S ->
            Not (G.Adj a b) := by
  intro a b ha hb hb_boundary hab
  by_cases hbS : b ∈ S
  · exact hb_boundary ⟨hbS, a, ha, hab⟩
  · exact hb
      (induceComponentSupport_mem_of_adj (G := G) C ha hbS hab)

theorem induceComponentSupport_connected
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    (G.induce (induceComponentSupport (G := G) C)).Connected := by
  classical
  let Hset : Set V := induceComponentSupport (G := G) C
  change (G.induce Hset).Connected
  refine { preconnected := ?_, nonempty := ?_ }
  · intro u v
    rcases u.2 with ⟨huA, huC⟩
    rcases v.2 with ⟨hvA, hvC⟩
    let uC : C := ⟨⟨u, huA⟩, huC⟩
    let vC : C := ⟨⟨v, hvA⟩, hvC⟩
    let F : C.toSimpleGraph →g (G.induce Hset) := {
      toFun w := ⟨((w : A) : V), ⟨(w : A).2, w.2⟩⟩
      map_rel' := by
        intro a b hab
        exact hab }
    exact ((SimpleGraph.ConnectedComponent.connected_toSimpleGraph C) uC vC).map F
  · obtain ⟨u, huC⟩ := C.nonempty_supp
    exact ⟨⟨u, ⟨u.2, huC⟩⟩⟩

theorem induceComponentSupport_insert_connected_of_adj
    {A : Set V}
    (C : (G.induce A).ConnectedComponent)
    {root u : V}
    (huC : u ∈ induceComponentSupport (G := G) C)
    (hur : G.Adj u root) :
    (G.induce (insert root (induceComponentSupport (G := G) C))).Connected := by
  classical
  have hpair : (G.induce ({root, u} : Set V)).Connected :=
    SimpleGraph.induce_pair_connected_of_adj (G := G) hur.symm
  have hcomp : (G.induce (induceComponentSupport (G := G) C)).Connected :=
    induceComponentSupport_connected (G := G) C
  have hinter :
      (({root, u} : Set V) ∩
        induceComponentSupport (G := G) C).Nonempty := by
    exact ⟨u, by simp, huC⟩
  have hconn :
      (G.induce (({root, u} : Set V) ∪
        induceComponentSupport (G := G) C)).Connected :=
    SimpleGraph.induce_union_connected
      (G := G) hpair.preconnected hcomp.preconnected hinter
  have hset :
      (({root, u} : Set V) ∪ induceComponentSupport (G := G) C) =
        insert root (induceComponentSupport (G := G) C) := by
    ext x
    constructor
    · intro hx
      rcases hx with hxpair | hxC
      · rcases hxpair with hxroot | hxu
        · exact Or.inl hxroot
        · have hxu_eq : x = u := by
            simpa using hxu
          exact Or.inr (by simpa [hxu_eq] using huC)
      · exact Or.inr hxC
    · intro hx
      rcases hx with hxroot | hxC
      · exact Or.inl (by simp [hxroot])
      · exact Or.inr hxC
  rw [hset] at hconn
  exact hconn

theorem degree_induce_insert_componentSupport_eq_of_mem
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {root v : V}
    (C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent)
    (hvC : v ∈ induceComponentSupport (G := G) C) :
    let S : Set V := insert root (induceComponentSupport (G := G) C)
    letI : DecidablePred (fun x : V => x ∈ S) := Classical.decPred _
    letI : Fintype S := Subtype.fintype (fun x : V => x ∈ S)
    (G.induce S).degree (⟨v, Or.inr hvC⟩ : S) = G.degree v := by
  classical
  dsimp
  let S : Set V := insert root (induceComponentSupport (G := G) C)
  letI : DecidablePred (fun x : V => x ∈ S) := Classical.decPred _
  letI : Fintype S := Subtype.fintype (fun x : V => x ∈ S)
  have hneighbor_sub :
      G.neighborSet v ⊆ S := by
    intro w hvw
    by_cases hwroot : w = root
    · exact Or.inl hwroot
    · have hwA : w ∈ (({root} : Set V)ᶜ) := by
        simp [hwroot]
      exact Or.inr
        (induceComponentSupport_mem_of_adj
          (G := G) C hvC hwA hvw)
  simpa [S] using
    SimpleGraph.degree_induce_of_neighborSet_subset
      (G := G)
      (s := S)
      (v := (⟨v, Or.inr hvC⟩ : S))
      hneighbor_sub

theorem induce_insert_componentSupport_delete_root_connected
    {root : V}
    (C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent) :
    let S : Set V := insert root (induceComponentSupport (G := G) C)
    let rootS : S := ⟨root, by simp [S]⟩
    ((G.induce S).induce (({rootS} : Set S)ᶜ)).Connected := by
  classical
  intro S rootS
  have hcomp :
      (G.induce (induceComponentSupport (G := G) C)).Connected :=
    induceComponentSupport_connected (G := G) C
  let T : Set S := ({rootS} : Set S)ᶜ
  let H : SimpleGraph T :=
    (G.induce S).induce T
  refine {
    preconnected := ?_
    nonempty := ?_
  }
  · intro a b
    have haK : ((a : S) : V) ∈ induceComponentSupport (G := G) C := by
      have haS : ((a : S) : V) ∈ S := (a : S).2
      rcases haS with hroot | hK
      · have haeq : (a : S) = rootS := Subtype.ext hroot
        exact False.elim (a.2 (by simpa using haeq))
      · exact hK
    have hbK : ((b : S) : V) ∈ induceComponentSupport (G := G) C := by
      have hbS : ((b : S) : V) ∈ S := (b : S).2
      rcases hbS with hroot | hK
      · have hbeq : (b : S) = rootS := Subtype.ext hroot
        exact False.elim (b.2 (by simpa using hbeq))
      · exact hK
    let aK : (induceComponentSupport (G := G) C : Set V) :=
      ⟨((a : S) : V), haK⟩
    let bK : (induceComponentSupport (G := G) C : Set V) :=
      ⟨((b : S) : V), hbK⟩
    let f :
        (G.induce (induceComponentSupport (G := G) C)) →g H := {
      toFun := fun z =>
        ⟨⟨(z : V), Or.inr z.2⟩, by
          intro hzroot
          have hzrootV : (z : V) = root :=
            congrArg Subtype.val hzroot
          have hzA :
              (z : V) ∈ (({root} : Set V)ᶜ) :=
            induceComponentSupport_subset (G := G) C z.2
          exact hzA (by simp [hzrootV])⟩
      map_rel' := by
        intro x y hxy
        exact hxy }
    have hreachK :
        (G.induce (induceComponentSupport (G := G) C)).Reachable aK bK :=
      hcomp aK bK
    simpa [H, f, aK, bK] using hreachK.map f
  · have hK_nonempty :
        (induceComponentSupport (G := G) C).Nonempty :=
      induceComponentSupport_nonempty (G := G) C
    rcases hK_nonempty with ⟨u, huK⟩
    refine ⟨⟨⟨u, Or.inr huK⟩, ?_⟩⟩
    intro huroot
    have hurootV : u = root := congrArg Subtype.val huroot
    have huA : u ∈ (({root} : Set V)ᶜ) :=
      induceComponentSupport_subset (G := G) C huK
    exact huA (by simp [hurootV])

theorem exists_cutVertex_ne_root_of_not_twoConnected_insert_componentSupport
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {root u : V}
    (C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent)
    (huC : u ∈ induceComponentSupport (G := G) C)
    (hur : G.Adj u root)
    (hnot2 :
      ¬ IsTwoConnected
        (G.induce (insert root (induceComponentSupport (G := G) C))))
    (hdegree : forall v : V, 2 <= G.degree v) :
    let S : Set V := insert root (induceComponentSupport (G := G) C)
    let rootS : S := ⟨root, by simp [S]⟩
    Exists fun c : S =>
      c ≠ rootS ∧
        Not (((G.induce S).induce ({c} : Set S)ᶜ).Connected) := by
  classical
  intro S rootS
  letI : DecidablePred (fun x : V => x ∈ S) := Classical.decPred _
  letI : Fintype S := Subtype.fintype (fun x : V => x ∈ S)
  have hconn : (G.induce S).Connected := by
    simpa [S] using
      induceComponentSupport_insert_connected_of_adj
        (G := G) C huC hur
  have hroot_connected :
      ((G.induce S).induce (({rootS} : Set S)ᶜ)).Connected := by
    simpa [S, rootS] using
      induce_insert_componentSupport_delete_root_connected
        (G := G) C
  have hne_root : Exists fun v : S => v ≠ rootS := by
    refine ⟨⟨u, Or.inr huC⟩, ?_⟩
    intro h
    exact hur.ne (congrArg Subtype.val h)
  have hdegree_S :
      forall v : S, v ≠ rootS -> 2 <= (G.induce S).degree v := by
    intro v hvroot
    have hvC : (v : V) ∈ induceComponentSupport (G := G) C := by
      rcases v.2 with hroot | hC
      · exact False.elim (hvroot (Subtype.ext hroot))
      · exact hC
    have hdeg_eq : (G.induce S).degree v = G.degree (v : V) := by
      have htmp :=
        degree_induce_insert_componentSupport_eq_of_mem
          (G := G) C hvC
      have hv_eq :
          (⟨(v : V), Or.inr hvC⟩ : S) = v := Subtype.ext rfl
      simpa [S, hv_eq] using htmp
    have hvdeg : 2 <= G.degree (v : V) := hdegree (v : V)
    omega
  have hcard : 2 < Nat.card S :=
    natCard_gt_two_of_min_degree_two_away_from_root
      (G := G.induce S) hne_root hdegree_S
  exact
    not_isTwoConnected_exists_cutVertex_ne_root_of_connected
      (G := G.induce S) (root := rootS) hconn hcard
      hroot_connected (by simpa [S] using hnot2)

theorem exists_smaller_componentSupport_of_not_twoConnected_insert_componentSupport
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {root u : V}
    (C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent)
    (huC : u ∈ induceComponentSupport (G := G) C)
    (hur : G.Adj u root)
    (hnot2 :
      ¬ IsTwoConnected
        (G.induce (insert root (induceComponentSupport (G := G) C))))
    (hdegree : forall v : V, 2 <= G.degree v) :
    Exists fun root' : V =>
      Exists fun C' : (G.induce (({root'} : Set V)ᶜ)).ConnectedComponent =>
        (insert root' (induceComponentSupport (G := G) C')).ncard <
          (insert root (induceComponentSupport (G := G) C)).ncard := by
  classical
  let S : Set V := insert root (induceComponentSupport (G := G) C)
  let rootS : S := ⟨root, by simp [S]⟩
  letI : DecidablePred (fun x : V => x ∈ S) := Classical.decPred _
  letI : Fintype S := Subtype.fintype (fun x : V => x ∈ S)
  have hcutExists :=
    exists_cutVertex_ne_root_of_not_twoConnected_insert_componentSupport
      (G := G) C huC hur hnot2 hdegree
  change
    Exists fun c : S =>
      c ≠ rootS ∧
        Not (((G.induce S).induce (({c} : Set S)ᶜ : Set S)).Connected)
    at hcutExists
  rcases hcutExists with ⟨c, hc_ne_root, hcut⟩
  let T : Set S := (Set.singleton c)ᶜ
  let rootT : T := ⟨rootS, by
    intro hrootc
    exact hc_ne_root hrootc.symm⟩
  let Hc : SimpleGraph T := (G.induce S).induce T
  haveI : Nonempty T := ⟨rootT⟩
  rcases
      exists_connectedComponent_not_mem_of_not_connected
        (G := Hc) rootT (by simpa [Hc, T] using hcut) with
    ⟨L, hrootT_not_L⟩
  have hroot_not_nested :
      root ∉ nestedInduceComponentSupport (G := G) L := by
    intro hroot
    rcases hroot with ⟨hrootS', hrootSupp⟩
    rcases hrootSupp with ⟨hrootT', hrootL⟩
    have hrootT_eq :
        (⟨(⟨root, hrootS'⟩ : S), hrootT'⟩ : T) = rootT := by
      exact Subtype.ext (Subtype.ext rfl)
    exact hrootT_not_L (by simpa [hrootT_eq] using hrootL)
  have hclosed :
      forall {a b : V},
        a ∈ nestedInduceComponentSupport (G := G) L ->
          b ∉ nestedInduceComponentSupport (G := G) L ->
            b ∉ ({(c : V)} : Set V) -> Not (G.Adj a b) := by
    intro a b ha hb hb_ne_c
    exact
      nestedInduceComponentSupport_closed_in_delete_of_insert_componentSupport
        (G := G) C (hS := rfl) L hroot_not_nested
        ha hb (by simpa using hb_ne_c)
  rcases nestedInduceComponentSupport_nonempty (G := G) L with
    ⟨x, hxL⟩
  rcases hxL with ⟨hxS, hxSupp⟩
  rcases hxSupp with ⟨hxT, hxLsupp⟩
  have hxNested : x ∈ nestedInduceComponentSupport (G := G) L :=
    ⟨hxS, hxT, hxLsupp⟩
  have hx_ne_c : x ≠ (c : V) := by
    intro hxc
    exact hxT (by
      change (⟨x, hxS⟩ : S) = c
      exact Subtype.ext hxc)
  let xDel : (({(c : V)} : Set V)ᶜ : Set V) := ⟨x, by simp [hx_ne_c]⟩
  let C' : (G.induce (({(c : V)} : Set V)ᶜ : Set V)).ConnectedComponent :=
    (G.induce (({(c : V)} : Set V)ᶜ : Set V)).connectedComponentMk xDel
  have hC'_subset :
      induceComponentSupport (G := G) C' ⊆
        nestedInduceComponentSupport (G := G) L := by
    intro y hyC'
    rcases hyC' with ⟨hyDel, hySupp⟩
    have hreach :
        (G.induce (({(c : V)} : Set V)ᶜ)).Reachable
          xDel ⟨y, hyDel⟩ := by
      exact
        SimpleGraph.ConnectedComponent.reachable_of_mem_supp
          C' SimpleGraph.ConnectedComponent.connectedComponentMk_mem hySupp
    exact
      reachable_induce_compl_mem_of_closed
        (G := G) (S := ({(c : V)} : Set V))
        (K := nestedInduceComponentSupport (G := G) L)
        hxNested hclosed hreach
  have hcV_ne_root : (c : V) ≠ root := by
    intro hcroot
    exact hc_ne_root (Subtype.ext hcroot)
  have hsmall_subset :
      insert (c : V) (induceComponentSupport (G := G) C') ⊆ S := by
    intro z hz
    rcases hz with hzc | hzC'
    · simp [hzc, c.2]
    · exact
        nestedInduceComponentSupport_subset (G := G) L
          (hC'_subset hzC')
  have hroot_not_small :
      root ∉ insert (c : V) (induceComponentSupport (G := G) C') := by
    intro hrootSmall
    rcases hrootSmall with hrootc | hrootC'
    · exact hcV_ne_root hrootc.symm
    · exact hroot_not_nested (hC'_subset hrootC')
  have hproper :
      insert (c : V) (induceComponentSupport (G := G) C') ⊂ S := by
    refine ⟨hsmall_subset, ?_⟩
    intro hreverse
    exact hroot_not_small (hreverse (by simp [S]))
  have hlt :
      (insert (c : V) (induceComponentSupport (G := G) C')).ncard <
        S.ncard :=
    Set.ncard_lt_ncard hproper
  exact ⟨(c : V), C', by simpa [S] using hlt⟩

theorem induceComponentSupport_exists_adj_root_of_connected_compl_singleton
    (hconn : G.Connected)
    {root : V}
    (C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent) :
    Exists fun u : V =>
      u ∈ induceComponentSupport (G := G) C ∧ G.Adj u root := by
  classical
  let K : Set V := induceComponentSupport (G := G) C
  have hK_nonempty : K.Nonempty :=
    induceComponentSupport_nonempty (G := G) C
  have hroot_not_K : root ∉ K := by
    intro hrootK
    exact hrootK.choose (by simp)
  have hK_compl_nonempty : Kᶜ.Nonempty := ⟨root, hroot_not_K⟩
  rcases Connected.exists_adjacent_crossing
      (G := G) hconn (S := K) hK_nonempty hK_compl_nonempty with
    ⟨u, huK, v, hv_not_K, huv⟩
  have hvroot : v = root := by
    by_contra hvroot
    have hvA : v ∈ (({root} : Set V)ᶜ) := by
      simp [hvroot]
    exact hv_not_K
      (induceComponentSupport_mem_of_adj (G := G) C huK hvA huv)
  exact ⟨u, huK, by simpa [hvroot] using huv⟩

theorem isTwoConnected_or_exists_cutComponent_twoConnected_of_connected_min_degree_two
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdegree : forall v : V, 2 <= G.degree v) :
    IsTwoConnected G ∨
      Exists fun root : V =>
        Exists fun C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent =>
          IsTwoConnected
            (G.induce (insert root (induceComponentSupport (G := G) C))) := by
  classical
  by_cases h2 : IsTwoConnected G
  · exact Or.inl h2
  · right
    let P : Nat -> Prop := fun n =>
      Exists fun root : V =>
        Exists fun C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent =>
          n = (insert root (induceComponentSupport (G := G) C)).ncard
    have hP : Exists fun n : Nat => P n := by
      rcases hconn.nonempty with ⟨root⟩
      have hpos : 0 < G.degree root := by
        have hroot_degree : 2 <= G.degree root := hdegree root
        omega
      rcases (G.degree_pos_iff_exists_adj root).mp hpos with
        ⟨u, hrootu⟩
      let uDel : (({root} : Set V)ᶜ : Set V) :=
        ⟨u, by
          intro hu
          exact hrootu.ne hu.symm⟩
      let C : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent :=
        (G.induce (({root} : Set V)ᶜ)).connectedComponentMk uDel
      exact
        ⟨(insert root (induceComponentSupport (G := G) C)).ncard,
          root, C, rfl⟩
    let n0 : Nat := Nat.find hP
    rcases Nat.find_spec hP with ⟨root, C, hn0⟩
    rcases
        induceComponentSupport_exists_adj_root_of_connected_compl_singleton
          (G := G) hconn C with
      ⟨u, huC, hur⟩
    by_cases hC2 :
      IsTwoConnected
        (G.induce (insert root (induceComponentSupport (G := G) C)))
    · exact ⟨root, C, hC2⟩
    · rcases
        exists_smaller_componentSupport_of_not_twoConnected_insert_componentSupport
          (G := G) C huC hur hC2 hdegree with
      ⟨root', C', hlt⟩
      have hPsmall :
          P ((insert root' (induceComponentSupport (G := G) C')).ncard) :=
        ⟨root', C', rfl⟩
      have hmin_le :
          n0 <= (insert root' (induceComponentSupport (G := G) C')).ncard :=
        Nat.find_min' hP hPsmall
      omega

def induceComponentSubgraph
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    G.Subgraph :=
  (⊤ : G.Subgraph).induce (induceComponentSupport (G := G) C)

@[simp]
theorem induceComponentSubgraph_verts
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    (induceComponentSubgraph (G := G) C).verts =
      induceComponentSupport (G := G) C := by
  simp [induceComponentSubgraph]

theorem induceComponentSubgraph_connected
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    (induceComponentSubgraph (G := G) C).Connected := by
  change ((⊤ : G.Subgraph).induce (induceComponentSupport (G := G) C)).Connected
  rw [← SimpleGraph.connected_induce_iff]
  exact induceComponentSupport_connected (G := G) C

theorem induceComponentSubgraph_mem_verts_iff
    {A : Set V}
    (C : (G.induce A).ConnectedComponent)
    {v : V} :
    v ∈ (induceComponentSubgraph (G := G) C).verts ↔
      v ∈ induceComponentSupport (G := G) C := by
  simp

theorem induceComponentSubgraph_le_induce_support
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    induceComponentSubgraph (G := G) C ≤
      (⊤ : G.Subgraph).induce (induceComponentSupport (G := G) C) := by
  rfl

theorem connected_set_subset_induceComponentSupport
    {A K : Set V}
    (hK_connected : (G.induce K).Connected)
    (hK_subset : K ⊆ A) :
    Exists fun C : (G.induce A).ConnectedComponent =>
      K ⊆ induceComponentSupport (G := G) C := by
  obtain ⟨xK⟩ := hK_connected.nonempty
  let xA : A := ⟨xK, hK_subset xK.2⟩
  let C : (G.induce A).ConnectedComponent :=
    (G.induce A).connectedComponentMk xA
  refine ⟨C, ?_⟩
  intro y hyK
  let yK : K := ⟨y, hyK⟩
  let yA : A := ⟨y, hK_subset hyK⟩
  let f : (G.induce K) →g (G.induce A) := {
    toFun := fun z => ⟨z, hK_subset z.2⟩
    map_rel' := by
      intro u v huv
      exact huv }
  have hreachK : (G.induce K).Reachable xK yK :=
    hK_connected xK yK
  have hreachA : (G.induce A).Reachable xA yA := by
    simpa [xA, yA, yK, f] using hreachK.map f
  refine ⟨hK_subset hyK, ?_⟩
  change (G.induce A).connectedComponentMk yA = C
  exact SimpleGraph.ConnectedComponent.sound hreachA.symm

end Schematic.Math.GraphTheory
