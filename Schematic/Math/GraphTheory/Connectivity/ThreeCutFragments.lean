import Schematic.Math.GraphTheory.Connectivity.EdgeContraction
import Schematic.Math.GraphTheory.Connectivity.Separations

/-!
Maximal fragments behind three-vertex cuts and contractible edges.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A connected fragment behind a three-vertex cut containing a selected
edge.  These are the finite objects maximized in the contractible-edge
argument. -/
structure ThreeCutFragment (G : SimpleGraph V) where
  left : V
  right : V
  apex : V
  verts : Finset V
  edge : G.Adj left right
  cut : ¬ (G.induce (({left, right, apex} : Set V)ᶜ)).Connected
  connected : (G.induce (verts : Set V)).Connected
  disjoint : Disjoint (verts : Set V) ({left, right, apex} : Set V)

noncomputable instance [Fintype V] :
    Fintype (ThreeCutFragment G) := by
  classical
  let data :
      ThreeCutFragment G → V × V × V × Finset V :=
    fun F => (F.left, F.right, F.apex, F.verts)
  exact Fintype.ofInjective data (by
    intro A B h
    cases A
    cases B
    simp_all [data])

theorem connected_induce_insert_of_connected_of_adj
    {A : Set V} {u v : V}
    (hA : (G.induce A).Connected)
    (hu : u ∈ A)
    (huv : G.Adj u v) :
    (G.induce (insert v A)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  let u' : (insert v A : Set V) := ⟨u, Set.mem_insert_of_mem v hu⟩
  refine ⟨u', ?_⟩
  intro x
  rcases Set.mem_insert_iff.mp x.2 with hxv | hxA
  · have hx : x = ⟨v, Set.mem_insert v A⟩ := Subtype.ext hxv
    subst x
    exact SimpleGraph.Adj.reachable huv
  · let uA : A := ⟨u, hu⟩
    let xA : A := ⟨x.1, hxA⟩
    let f : G.induce A →g G.induce (insert v A) :=
      { toFun := fun z => ⟨z.1, Set.mem_insert_of_mem v z.2⟩
        map_rel' := by
          intro a b hab
          exact hab }
    have hreach := (hA uA xA).map f
    simpa [u', uA, xA, f] using hreach

theorem IsThreeConnected.exists_maximal_threeCutFragment
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    (hcard : 4 < Nat.card V)
    (hnoncontract :
      forall {a b : V} (hab : G.Adj a b),
        ¬ IsThreeConnected
          (GraphContraction.collapseEdge G hab).graph) :
    Exists fun M : ThreeCutFragment G =>
      forall N : ThreeCutFragment G, N.verts.card ≤ M.verts.card := by
  classical
  have hcardF : 4 < Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using hcard
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨y, hxy⟩ := hG.connected (by decide) |>.preconnected.exists_adj_of_nontrivial x
  obtain ⟨z, hcut⟩ :=
    hG.exists_three_vertex_cut_of_not_collapseEdge_isThreeConnected
      hcard hxy (hnoncontract hxy)
  have htriple_card : ({x, y, z} : Set V).ncard ≤ 3 := by
    calc
      ({x, y, z} : Set V).ncard ≤ ({y, z} : Set V).ncard + 1 :=
        Set.ncard_insert_le x ({y, z} : Set V)
      _ ≤ (({z} : Set V).ncard + 1) + 1 := by
        exact Nat.add_le_add_right
          (Set.ncard_insert_le y ({z} : Set V)) 1
      _ = 3 := by simp
  have htriple_ne_univ : ({x, y, z} : Set V) ≠ Set.univ := by
    intro htriple
    have huniv :
        (Set.univ : Set V).ncard = Fintype.card V := by simp
    rw [htriple, huniv] at htriple_card
    omega
  obtain ⟨w, hw⟩ :=
    (Set.ne_univ_iff_exists_notMem ({x, y, z} : Set V)).mp
      htriple_ne_univ
  have hw_connected :
      (G.induce (({w} : Finset V) : Set V)).Connected := by
    let w' : (({w} : Finset V) : Set V) := ⟨w, by simp⟩
    haveI : Nonempty ((({w} : Finset V) : Set V)) := ⟨w'⟩
    letI : Subsingleton ((({w} : Finset V) : Set V)) :=
      ⟨by
        intro p q
        apply Subtype.ext
        have hp : p.1 = w := by simpa using p.2
        have hq : q.1 = w := by simpa using q.2
        exact hp.trans hq.symm⟩
    exact SimpleGraph.Connected.of_subsingleton
  let M0 : ThreeCutFragment G :=
    { left := x
      right := y
      apex := z
      verts := {w}
      edge := hxy
      cut := hcut
      connected := hw_connected
      disjoint := by
        rw [Set.disjoint_left]
        intro v hv hvt
        have hvw : v = w := by simpa using hv
        subst v
        exact hw hvt }
  obtain ⟨M, _hM_mem, hMmax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (ThreeCutFragment G))
      (fun F => F.verts.card)
      (by exact ⟨M0, Finset.mem_univ M0⟩)
  exact ⟨M, fun N => hMmax N (Finset.mem_univ N)⟩

theorem ThreeCutFragment.not_adj_of_maximal
    [Fintype V] [DecidableEq V]
    (M : ThreeCutFragment G)
    (hmax :
      forall N : ThreeCutFragment G, N.verts.card ≤ M.verts.card)
    {u v : V}
    (hu : u ∈ (M.verts : Set V))
    (hv : v ∉ (M.verts : Set V))
    (hvcut : v ∉ ({M.left, M.right, M.apex} : Set V)) :
    ¬ G.Adj u v := by
  intro huv
  let F' : Finset V := insert v M.verts
  have hvfin : v ∉ M.verts := by simpa using hv
  have hconn :
      (G.induce (F' : Set V)).Connected := by
    have h :=
      connected_induce_insert_of_connected_of_adj
        M.connected hu huv
    rw [show (F' : Set V) = insert v (M.verts : Set V) by
      simp [F']]
    exact h
  let N : ThreeCutFragment G :=
    { left := M.left
      right := M.right
      apex := M.apex
      verts := F'
      edge := M.edge
      cut := M.cut
      connected := hconn
      disjoint := by
        rw [Set.disjoint_left]
        intro x hx hxcut
        have hx' : x = v ∨ x ∈ (M.verts : Set V) := by
          simpa [F'] using hx
        rcases hx' with rfl | hxM
        · exact hvcut hxcut
        · exact Set.disjoint_left.mp M.disjoint hxM hxcut }
  have hle := hmax N
  have hcard : N.verts.card = M.verts.card + 1 := by
    simp [N, F', Finset.card_insert_of_notMem hvfin]
  omega

theorem ThreeCutFragment.cut_ncard_eq_three
    [Fintype V]
    (hG : IsThreeConnected G)
    (M : ThreeCutFragment G) :
    ({M.left, M.right, M.apex} : Set V).ncard = 3 := by
  have hnotlt :
      ¬ ({M.left, M.right, M.apex} : Set V).ncard < 3 := by
    intro hlt
    exact M.cut (hG.2 _ hlt)
  have hle :
      ({M.left, M.right, M.apex} : Set V).ncard ≤ 3 := by
    calc
      ({M.left, M.right, M.apex} : Set V).ncard ≤
          ({M.right, M.apex} : Set V).ncard + 1 :=
        Set.ncard_insert_le M.left ({M.right, M.apex} : Set V)
      _ ≤ (({M.apex} : Set V).ncard + 1) + 1 := by
        exact Nat.add_le_add_right
          (Set.ncard_insert_le M.right ({M.apex} : Set V)) 1
      _ = 3 := by simp
  omega

theorem ThreeCutFragment.apex_ne_left
    [Fintype V]
    (hG : IsThreeConnected G)
    (M : ThreeCutFragment G) :
    M.apex ≠ M.left := by
  intro h
  have hcard := M.cut_ncard_eq_three hG
  rw [h] at hcard
  have hle : ({M.right, M.left} : Set V).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le M.right ({M.left} : Set V)
  have heq : ({M.right, M.left} : Set V).ncard = 3 := by
    simpa using hcard
  omega

theorem ThreeCutFragment.apex_ne_right
    [Fintype V]
    (hG : IsThreeConnected G)
    (M : ThreeCutFragment G) :
    M.apex ≠ M.right := by
  intro h
  have hcard := M.cut_ncard_eq_three hG
  rw [h] at hcard
  have hle : ({M.left, M.right} : Set V).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le M.left ({M.right} : Set V)
  have heq : ({M.left, M.right} : Set V).ncard = 3 := by
    simpa using hcard
  omega

theorem ThreeCutFragment.outside_nonempty
    [Fintype V]
    (M : ThreeCutFragment G) :
    (((M.verts : Set V) ∪
      ({M.left, M.right, M.apex} : Set V))ᶜ).Nonempty := by
  classical
  let F : Set V := (M.verts : Set V)
  let T : Set V := {M.left, M.right, M.apex}
  by_contra hnone
  have hcover : forall x : V, x ∈ F ∨ x ∈ T := by
    intro x
    by_contra hx
    push Not at hx
    apply hnone
    refine ⟨x, ?_⟩
    intro hxunion
    exact hxunion.elim hx.1 hx.2
  have heq : F = Tᶜ := by
    apply Set.Subset.antisymm
    · intro x hxF hxT
      exact Set.disjoint_left.mp M.disjoint hxF hxT
    · intro x hxT
      exact (hcover x).resolve_right hxT
  apply M.cut
  rw [← heq]
  exact M.connected

theorem ThreeCutFragment.exists_adj_mem_verts_of_mem_cut_of_maximal
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    (M : ThreeCutFragment G)
    (hmax :
      forall N : ThreeCutFragment G, N.verts.card ≤ M.verts.card)
    {t : V}
    (ht : t ∈ ({M.left, M.right, M.apex} : Set V)) :
    Exists fun v : V =>
      v ∈ (M.verts : Set V) ∧ G.Adj t v := by
  classical
  by_contra hnone
  push Not at hnone
  let F : Set V := (M.verts : Set V)
  let T : Set V := {M.left, M.right, M.apex}
  let T' : Set V := T \ {t}
  have hboundary :
      forall {a b : V}, a ∈ F -> b ∉ F -> b ∉ T' ->
        Not (G.Adj a b) := by
    intro a b haF hbF hbT'
    by_cases hbT : b ∈ T
    · have hbt : b = t := by
        by_contra hne
        exact hbT' ⟨hbT, hne⟩
      subst b
      intro hat
      exact hnone a haF hat.symm
    · exact M.not_adj_of_maximal hmax haF hbF (by simpa [T] using hbT)
  have hdisj : Disjoint F T' := by
    rw [Set.disjoint_left]
    intro x hxF hxT'
    exact Set.disjoint_left.mp M.disjoint hxF hxT'.1
  have hF : F.Nonempty := by
    obtain ⟨x⟩ := M.connected.nonempty
    exact ⟨x.1, x.2⟩
  have houtside : (F ∪ T')ᶜ.Nonempty := by
    refine ⟨t, ?_⟩
    intro htunion
    rcases htunion with htF | htT'
    · exact Set.disjoint_left.mp M.disjoint htF ht
    · exact htT'.2 rfl
  have hT' : T'.ncard < 3 := by
    have hTcard : T.ncard = 3 := by
      simpa [T] using M.cut_ncard_eq_three hG
    have htT : t ∈ T := by simpa [T] using ht
    rw [Set.ncard_diff_singleton_of_mem htT, hTcard]
    decide
  exact hG.no_nonempty_set_with_small_boundary
    hboundary hdisj hF houtside hT'

theorem ThreeCutFragment.exists_apex_adj_outside_of_maximal
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    (M : ThreeCutFragment G)
    (hmax :
      forall N : ThreeCutFragment G, N.verts.card ≤ M.verts.card) :
    Exists fun u : V =>
      u ∉ ((M.verts : Set V) ∪ ({M.left, M.right} : Set V)) ∧
        G.Adj M.apex u := by
  classical
  by_contra hnone
  push Not at hnone
  let F : Set V := (M.verts : Set V)
  let T : Set V := {M.left, M.right, M.apex}
  let P : Set V := {M.left, M.right}
  let R : Set V := (F ∪ T)ᶜ
  have hboundary :
      forall {a b : V}, a ∈ R -> b ∉ R -> b ∉ P ->
        Not (G.Adj a b) := by
    intro a b haR hbR hbP
    have haF : a ∉ F := fun ha => haR (Or.inl ha)
    have haT : a ∉ T := fun ha => haR (Or.inr ha)
    by_cases hbF : b ∈ F
    · intro hab
      exact
        (M.not_adj_of_maximal hmax hbF haF
          (by simpa [T] using haT)) hab.symm
    · have hbT : b ∈ T := by
        by_contra hbT
        exact hbR (by
          intro hbunion
          exact hbunion.elim hbF hbT)
      have hb_apex : b = M.apex := by
        have hb_cases :
            b = M.left ∨ b = M.right ∨ b = M.apex := by
          simpa only [T, Set.mem_insert_iff, Set.mem_singleton_iff] using hbT
        rcases hb_cases with hbl | hbr | hba
        · exact False.elim (hbP (by simp [P, hbl]))
        · exact False.elim (hbP (by simp [P, hbr]))
        · exact hba
      subst b
      intro haa
      exact hnone a (by
        intro haH
        rcases haH with haF' | haP
        · exact haF haF'
        · exact haT (by
            rcases haP with hal | har
            · simp [T, hal]
            · have har' : a = M.right := by simpa using har
              simp [T, har'])) haa.symm
  have hdisj : Disjoint R P := by
    rw [Set.disjoint_left]
    intro x hxR hxP
    exact hxR (Or.inr (by
      rcases hxP with hxl | hxr
      · simp [T, hxl]
      · have hxr' : x = M.right := by simpa using hxr
        simp [T, hxr']))
  have hR : R.Nonempty := by
    change
      (((M.verts : Set V) ∪
        ({M.left, M.right, M.apex} : Set V))ᶜ).Nonempty
    exact M.outside_nonempty
  have houtside : (R ∪ P)ᶜ.Nonempty := by
    obtain ⟨x⟩ := M.connected.nonempty
    refine ⟨x.1, ?_⟩
    intro hx
    rcases hx with hxR | hxP
    · exact hxR (Or.inl x.2)
    · exact Set.disjoint_left.mp M.disjoint x.2 (by
        rcases hxP with hxl | hxr
        · simp [hxl]
        · have hxr' : x.1 = M.right := by simpa using hxr
          simp [hxr'])
  have hPsmall : P.ncard < 3 := by
    have hPle : P.ncard ≤ 2 := by
      simpa [P] using Set.ncard_insert_le M.left ({M.right} : Set V)
    omega
  exact hG.no_nonempty_set_with_small_boundary
    hboundary hdisj hR houtside hPsmall

theorem ThreeCutFragment.edgeFragment_delete_connected
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    (M : ThreeCutFragment G)
    (hmax :
      forall N : ThreeCutFragment G, N.verts.card ≤ M.verts.card)
    (w : V) :
    let H : Set V :=
      (M.verts : Set V) ∪ ({M.left, M.right} : Set V)
    (G.induce (H \ {w})).Connected := by
  classical
  dsimp only
  let F : Set V := (M.verts : Set V)
  let P : Set V := {M.left, M.right}
  let T : Set V := {M.left, M.right, M.apex}
  let H : Set V := F ∪ P
  change (G.induce (H \ {w})).Connected
  have hleftF : M.left ∉ F := by
    intro h
    exact Set.disjoint_left.mp M.disjoint h (by simp)
  have hrightF : M.right ∉ F := by
    intro h
    exact Set.disjoint_left.mp M.disjoint h (by simp)
  have hapexF : M.apex ∉ F := by
    intro h
    exact Set.disjoint_left.mp M.disjoint h (by simp)
  have hleftH : M.left ∈ H := by simp [H, P]
  have hrightH : M.right ∈ H := by simp [H, P]
  have hapexH : M.apex ∉ H := by
    intro h
    rcases h with hF | hP
    · exact hapexF hF
    · rcases hP with hleft | hright
      · exact M.apex_ne_left hG (Set.mem_singleton_iff.mp hleft)
      · exact M.apex_ne_right hG (Set.mem_singleton_iff.mp hright)
  by_cases hwleft : w = M.left
  · subst w
    obtain ⟨v, hvF, hrv⟩ :=
      M.exists_adj_mem_verts_of_mem_cut_of_maximal
        hG hmax (t := M.right) (by simp)
    have hconn :
        (G.induce (insert M.right F)).Connected :=
      connected_induce_insert_of_connected_of_adj
        M.connected hvF hrv.symm
    have heq : H \ {M.left} = insert M.right F := by
      ext x
      simp only [H, P, Set.mem_diff, Set.mem_union,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxF | hxl | hxr, hxne⟩
        · exact Or.inr hxF
        · exact False.elim (hxne hxl)
        · exact Or.inl hxr
      · rintro (hxr | hxF)
        · exact ⟨Or.inr (Or.inr hxr), fun hxl => M.edge.ne (hxl.symm.trans hxr)⟩
        · exact ⟨Or.inl hxF, fun hxl => hleftF (hxl ▸ hxF)⟩
    rw [heq]
    exact hconn
  · by_cases hwright : w = M.right
    · subst w
      obtain ⟨v, hvF, hlv⟩ :=
        M.exists_adj_mem_verts_of_mem_cut_of_maximal
          hG hmax (t := M.left) (by simp)
      have hconn :
          (G.induce (insert M.left F)).Connected :=
        connected_induce_insert_of_connected_of_adj
          M.connected hvF hlv.symm
      have heq : H \ {M.right} = insert M.left F := by
        ext x
        simp only [H, P, Set.mem_diff, Set.mem_union,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hxF | hxl | hxr, hxne⟩
          · exact Or.inr hxF
          · exact Or.inl hxl
          · exact False.elim (hxne hxr)
        · rintro (hxl | hxF)
          · exact ⟨Or.inr (Or.inl hxl),
              fun hxr => M.edge.ne (hxl.symm.trans hxr)⟩
          · exact ⟨Or.inl hxF, fun hxr => hrightF (hxr ▸ hxF)⟩
      rw [heq]
      exact hconn
    · let S : Set V := {w, M.apex}
      have hSsmall : S.ncard < 3 := by
        have hSle : S.ncard ≤ 2 := by
          simpa [S] using Set.ncard_insert_le w ({M.apex} : Set V)
        omega
      have hsource : (G.induce Sᶜ).Connected := hG.2 S hSsmall
      let f :
          {x : V // x ∈ Sᶜ} →
            {x : V // x ∈ H \ {w}} :=
        fun x => by
          have hxw : x.1 ≠ w := by
            intro hxw
            exact x.2 (by simp [S, hxw])
          if hxH : x.1 ∈ H then
            exact ⟨x.1, hxH, hxw⟩
          else
            exact ⟨M.left, hleftH, fun h => hwleft h.symm⟩
      have hf_adj :
          forall {x y : {x : V // x ∈ Sᶜ}},
            (G.induce Sᶜ).Adj x y →
              f x = f y ∨ (G.induce (H \ {w})).Adj (f x) (f y) := by
        intro x y hxy
        have hxApex : x.1 ≠ M.apex := by
          intro hx
          exact x.2 (by simp [S, hx])
        have hyApex : y.1 ≠ M.apex := by
          intro hy
          exact y.2 (by simp [S, hy])
        by_cases hxH : x.1 ∈ H
        · by_cases hyH : y.1 ∈ H
          · exact Or.inr (by simpa [f, hxH, hyH] using hxy)
          · rcases hxH with hxF | hxP
            · have hyF : y.1 ∉ F := fun hy => hyH (Or.inl hy)
              have hyT : y.1 ∉ T := by
                intro hy
                have hycases :
                    y.1 = M.left ∨ y.1 = M.right ∨ y.1 = M.apex := by
                  simpa only [T, Set.mem_insert_iff,
                    Set.mem_singleton_iff] using hy
                rcases hycases with hyl | hyr | hya
                · exact hyH (hyl ▸ hleftH)
                · exact hyH (hyr ▸ hrightH)
                · exact hyApex hya
              exact False.elim
                ((M.not_adj_of_maximal hmax hxF hyF
                  (by simpa [T] using hyT)) hxy)
            · have hxcases : x.1 = M.left ∨ x.1 = M.right := by
                simpa only [P, Set.mem_insert_iff,
                  Set.mem_singleton_iff] using hxP
              rcases hxcases with hxl | hxr
              · exact Or.inl (by
                  apply Subtype.ext
                  simp [f, hleftH, hyH, hxl])
              · exact Or.inr (by
                  change G.Adj (f x).1 (f y).1
                  simpa [f, hrightH, hyH, hxr] using M.edge.symm)
        · by_cases hyH : y.1 ∈ H
          · rcases hyH with hyF | hyP
            · have hxF : x.1 ∉ F := fun hx => hxH (Or.inl hx)
              have hxT : x.1 ∉ T := by
                intro hx
                have hxcases :
                    x.1 = M.left ∨ x.1 = M.right ∨ x.1 = M.apex := by
                  simpa only [T, Set.mem_insert_iff,
                    Set.mem_singleton_iff] using hx
                rcases hxcases with hxl | hxr | hxa
                · exact hxH (hxl ▸ hleftH)
                · exact hxH (hxr ▸ hrightH)
                · exact hxApex hxa
              exact False.elim
                ((M.not_adj_of_maximal hmax hyF hxF
                  (by simpa [T] using hxT)) hxy.symm)
            · have hycases : y.1 = M.left ∨ y.1 = M.right := by
                simpa only [P, Set.mem_insert_iff,
                  Set.mem_singleton_iff] using hyP
              rcases hycases with hyl | hyr
              · exact Or.inl (by
                  apply Subtype.ext
                  simp [f, hxH, hleftH, hyl])
              · exact Or.inr (by
                  change G.Adj (f x).1 (f y).1
                  simpa [f, hxH, hrightH, hyr] using M.edge)
          · exact Or.inl (by simp [f, hxH, hyH])
      have hf_surjective : Function.Surjective f := by
        intro y
        have hyw : y.1 ≠ w := y.2.2
        have hya : y.1 ≠ M.apex := by
          intro hya
          exact hapexH (hya ▸ y.2.1)
        let x : {x : V // x ∈ Sᶜ} :=
          ⟨y.1, by
            intro hyS
            rcases hyS with hyw' | hya'
            · exact hyw (Set.mem_singleton_iff.mp hyw')
            · exact hya (Set.mem_singleton_iff.mp hya')⟩
        refine ⟨x, ?_⟩
        apply Subtype.ext
        simp [f, x, y.2.1]
      exact
        SimpleGraph.Connected.map_of_adj_eq_or_adj
          hsource f hf_adj hf_surjective

theorem IsThreeConnected.exists_adj_collapseEdge_isThreeConnected
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    (hcard : 4 < Nat.card V) :
    Exists fun a : V =>
      Exists fun b : V =>
        Exists fun hab : G.Adj a b =>
          IsThreeConnected
            (GraphContraction.collapseEdge G hab).graph := by
  classical
  by_contra hnone
  have hnoncontract :
      forall {a b : V} (hab : G.Adj a b),
        ¬ IsThreeConnected
          (GraphContraction.collapseEdge G hab).graph := by
    intro a b hab hcontract
    exact hnone ⟨a, b, hab, hcontract⟩
  obtain ⟨M, hmax⟩ :=
    hG.exists_maximal_threeCutFragment hcard hnoncontract
  obtain ⟨u, huoutside, hzu⟩ :=
    M.exists_apex_adj_outside_of_maximal hG hmax
  obtain ⟨v, hcut⟩ :=
    hG.exists_three_vertex_cut_of_not_collapseEdge_isThreeConnected
      hcard hzu (hnoncontract hzu)
  let F : Set V := (M.verts : Set V)
  let P : Set V := {M.left, M.right}
  let H : Set V := F ∪ P
  let Hfin : Finset V := insert M.left (insert M.right M.verts)
  let F' : Finset V := Hfin.erase v
  have hleftF : M.left ∉ M.verts := by
    intro h
    exact Set.disjoint_left.mp M.disjoint
      (by simpa using h) (by simp)
  have hrightF : M.right ∉ M.verts := by
    intro h
    exact Set.disjoint_left.mp M.disjoint
      (by simpa using h) (by simp)
  have hHfin : (Hfin : Set V) = H := by
    ext x
    simp [Hfin, H, F, P]
  have hF' : (F' : Set V) = H \ {v} := by
    ext x
    simp [F', hHfin]
  have hconn : (G.induce (F' : Set V)).Connected := by
    rw [hF']
    exact M.edgeFragment_delete_connected hG hmax v
  have hapexH : M.apex ∉ H := by
    intro h
    rcases h with hF | hP
    · exact Set.disjoint_left.mp M.disjoint hF (by simp)
    · rcases hP with hleft | hright
      · exact M.apex_ne_left hG (Set.mem_singleton_iff.mp hleft)
      · exact M.apex_ne_right hG (Set.mem_singleton_iff.mp hright)
  have huH : u ∉ H := by
    simpa [H, F, P] using huoutside
  let N : ThreeCutFragment G :=
    { left := M.apex
      right := u
      apex := v
      verts := F'
      edge := hzu
      cut := hcut
      connected := hconn
      disjoint := by
        rw [Set.disjoint_left]
        intro x hxF' hxcut
        have hxFfin : x ∈ F' := by simpa using hxF'
        have hxH : x ∈ H := by
          rw [← hHfin]
          exact Finset.mem_of_mem_erase hxFfin
        have hxv : x ≠ v := by
          intro hxv
          subst x
          exact Finset.notMem_erase v Hfin hxFfin
        have hxcases :
            x = M.apex ∨ x = u ∨ x = v := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxcut
        rcases hxcases with hxa | hxu | hxv'
        · exact hapexH (hxa ▸ hxH)
        · exact huH (hxu ▸ hxH)
        · exact hxv hxv' }
  have hHcard : Hfin.card = M.verts.card + 2 := by
    simp [Hfin, hleftF, hrightF, M.edge.ne]
  have hF'lower : M.verts.card + 1 ≤ F'.card := by
    have hpred : Hfin.card - 1 ≤ F'.card := by
      simpa [F'] using
        (Finset.pred_card_le_card_erase (s := Hfin) (a := v))
    omega
  have hupper : F'.card ≤ M.verts.card := by
    simpa [N] using hmax N
  omega

end Schematic.Math.GraphTheory
