import Schematic.Math.GraphTheory.Embedding.Geometry.Connectivity

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

theorem DLink.to_reachable
    {r : List G.Dart} {x y : G.Dart}
    (hxy : G.DLink r x y) :
    G.Reachable x y :=
  CLink.to_reachable (G := G) hxy.2

@[simp]
theorem DPath.nil (r : List G.Dart) (x : G.Dart) :
    G.DPath r x [] := by
  simp [DPath]

@[simp]
theorem DPath.cons (r : List G.Dart) (x y : G.Dart) (p : List G.Dart) :
    G.DPath r x (y :: p) ↔ G.DLink r x y ∧ G.DPath r y p := by
  rfl

theorem DPath.to_cPath
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hp : G.DPath r x p) :
    G.CPath x p := by
  refine List.RelPath.imp (S := G.CLink) ?_ hp
  intro a b hab
  exact hab.2

theorem DPath.to_reachable
    {r : List G.Dart} {x y : G.Dart} {p : List G.Dart}
    (hp : G.DPath r x (p ++ [y])) :
    G.Reachable x y :=
  CPath.to_reachable (G := G) (DPath.to_cPath (G := G) hp)

theorem DPath.to_cPath_snoc_face_edge
    {r : List G.Dart} {x y : G.Dart} {p : List G.Dart}
    (hp : G.DPath r x p)
    (hlast : (x :: p).getLastD x = y) :
    G.CPath x (p ++ [G.face (G.edge y)]) :=
  CPath.snoc (G := G)
    (DPath.to_cPath (G := G) hp) hlast
    (CLink.face_edge (G := G) y)

theorem DPath.snoc
    {r : List G.Dart} {x y z : G.Dart} {p : List G.Dart}
    (hp : G.DPath r x p)
    (hlast : (x :: p).getLastD x = y)
    (hyz : G.DLink r y z) :
    G.DPath r x (p ++ [z]) :=
  List.RelPath.snoc hp hlast hyz

theorem DPath.sources_not_mem_of_append_singleton
    {r : List G.Dart} {x y : G.Dart} {p : List G.Dart}
    (hp : G.DPath r x (p ++ [y])) :
    ∀ z : G.Dart, z ∈ x :: p → z ∉ r := by
  induction p generalizing x with
  | nil =>
      have hp' : G.DLink r x y := by
        simpa [DPath] using hp
      intro z hz
      simp at hz
      subst z
      exact hp'.1
  | cons w p ih =>
      have hp' : G.DLink r x w ∧ G.DPath r w (p ++ [y]) := by
        simpa [DPath] using hp
      intro z hz
      rw [List.mem_cons] at hz
      rcases hz with hz | hz
      · subst z
        exact hp'.1.1
      · exact ih hp'.2 z hz

@[simp]
theorem RCLPath.nil (r : List G.Dart) (x : G.Dart) :
    G.RCLPath r x [] := by
  simp [RCLPath]

@[simp]
theorem RCLPath.cons (r : List G.Dart) (x y : G.Dart) (p : List G.Dart) :
    G.RCLPath r x (y :: p) ↔
      G.RCLStep r x = y ∧ G.RCLPath r y p := by
  rfl

theorem RCLStep.cLink
    (r : List G.Dart) (x : G.Dart) :
    G.CLink x (G.RCLStep r x) := by
  unfold RCLStep
  by_cases hx : x ∈ r
  · simp [hx, CLink.face_edge (G := G) x]
  · simp [hx, CLink.face (G := G) x]

theorem RCLStep.eq_face_of_not_mem
    {r : List G.Dart} {x : G.Dart}
    (hx : x ∉ r) :
    G.RCLStep r x = G.face x := by
  simp [RCLStep, hx]

theorem RCLStep.eq_face_edge_of_mem
    {r : List G.Dart} {x : G.Dart}
    (hx : x ∈ r) :
    G.RCLStep r x = G.face (G.edge x) := by
  simp [RCLStep, hx]

theorem RCLStep.eq_node_symm_of_mem
    {r : List G.Dart} {x : G.Dart}
    (hx : x ∈ r) :
    G.RCLStep r x = G.node.symm x := by
  rw [RCLStep.eq_face_edge_of_mem (G := G) hx]
  apply G.node.injective
  simp

theorem RCLPath.to_cPath
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hp : G.RCLPath r x p) :
    G.CPath x p := by
  refine List.RelPath.imp (S := G.CLink) ?_ hp
  intro a b hab
  rw [← hab]
  exact RCLStep.cLink (G := G) r a

theorem RCLPath.snoc
    {r : List G.Dart} {x y z : G.Dart} {p : List G.Dart}
    (hp : G.RCLPath r x p)
    (hlast : (x :: p).getLastD x = y)
    (hyz : G.RCLStep r y = z) :
    G.RCLPath r x (p ++ [z]) :=
  List.RelPath.snoc hp hlast hyz

theorem RCLPath.append
    {r : List G.Dart} {x y : G.Dart} {p q : List G.Dart}
    (hp : G.RCLPath r x p)
    (hlast : (x :: p).getLastD x = y)
    (hq : G.RCLPath r y q) :
    G.RCLPath r x (p ++ q) :=
  List.RelPath.append hp hlast hq

theorem RCLPath.append_cons
    {r : List G.Dart} {x y z : G.Dart} {p q : List G.Dart}
    (hp : G.RCLPath r x p)
    (hlast : (x :: p).getLastD x = y)
    (hyz : G.RCLStep r y = z)
    (hq : G.RCLPath r z q) :
    G.RCLPath r x (p ++ z :: q) :=
  List.RelPath.append_cons hp hlast hyz hq

theorem RCLPath.to_reachable
    {r : List G.Dart} {x y : G.Dart} {p : List G.Dart}
    (hp : G.RCLPath r x (p ++ [y])) :
    G.Reachable x y :=
  CPath.to_reachable (G := G) (RCLPath.to_cPath (G := G) hp)

theorem RCLPath.step_mem_tail_or_last
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hp : G.RCLPath r x p)
    {y : G.Dart}
    (hy : y ∈ x :: p) :
    G.RCLStep r y ∈ p ∨ y = (x :: p).getLastD x := by
  induction p generalizing x with
  | nil =>
      simp at hy
      subst y
      right
      simp [List.getLastD]
  | cons z p ih =>
      have hp' : G.RCLStep r x = z ∧ G.RCLPath r z p := by
        simpa [RCLPath] using hp
      rw [List.mem_cons] at hy
      rcases hy with hy | hy
      · subst y
        left
        simp [hp'.1]
      · rcases ih hp'.2 hy with hmem | hlast
        · left
          simp [hmem]
        · right
          simpa [List.getLastD] using hlast

theorem RCLPath.step_mem_cons_of_cycle
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hp : G.RCLPath r x p)
    (hclose : G.RCLStep r ((x :: p).getLastD x) = x)
    {y : G.Dart}
    (hy : y ∈ x :: p) :
    G.RCLStep r y ∈ x :: p := by
  rcases RCLPath.step_mem_tail_or_last (G := G) hp hy with hmem | hlast
  · exact List.mem_cons_of_mem x hmem
  · subst y
    rw [List.mem_cons]
    exact Or.inl hclose

theorem RCLCycle.step_mem
    {r : List G.Dart} {c : List G.Dart}
    (hc : G.RCLCycle r c)
    {y : G.Dart}
    (hy : y ∈ c) :
    G.RCLStep r y ∈ c := by
  cases c with
  | nil =>
      cases hc
  | cons x p =>
      exact RCLPath.step_mem_cons_of_cycle (G := G) hc.1 hc.2 hy

theorem RCLCycle.to_cPath
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hc : G.RCLCycle r (x :: p)) :
    G.CPath x p :=
  RCLPath.to_cPath (G := G) hc.1

theorem RCLCycle.close_cLink
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hc : G.RCLCycle r (x :: p)) :
    G.CLink ((x :: p).getLastD x) x := by
  have hlink := RCLStep.cLink (G := G) r ((x :: p).getLastD x)
  rwa [hc.2] at hlink

theorem Jordan.not_cPath_to_RCLCycle_with_node_contact
    (hJ : G.Jordan)
    {r : List G.Dart} {x z : G.Dart} {p c : List G.Dart}
    (hp : G.CPath x p)
    (hlink : G.CLink ((x :: p).getLastD x) z)
    (hc : G.RCLCycle r (z :: c))
    (hpNodup : (x :: p).Nodup)
    (hcNodup : (z :: c).Nodup)
    (hdisj :
      ∀ y : G.Dart, y ∈ x :: p → y ∈ z :: c → False)
    (hnode : G.node x ∈ z :: c)
    (hzlast : G.node.symm ((z :: c).getLastD z) = z) :
    False :=
  Jordan.not_cPath_to_cycle_with_node_contact
    (G := G) hJ hp hlink (RCLCycle.to_cPath (G := G) hc)
    hpNodup hcNodup hdisj hnode hzlast

theorem RCLCycle.node_symm_mem_of_ring_mem
    {r c : List G.Dart} {x : G.Dart}
    (hc : G.RCLCycle r c)
    (hxC : x ∈ c)
    (hxR : x ∈ r) :
    G.node.symm x ∈ c := by
  have hstep : G.RCLStep r x ∈ c :=
    RCLCycle.step_mem (G := G) hc hxC
  rwa [RCLStep.eq_node_symm_of_mem (G := G) hxR] at hstep

theorem RCLCycle.of_path_last_mem
    {r : List G.Dart} {x z : G.Dart} {p : List G.Dart}
    (hp : G.RCLPath r x p)
    (hlast : (x :: p).getLastD x = z)
    (hz : z ∈ r)
    (hx : x = G.face (G.edge z)) :
    G.RCLCycle r (x :: p) := by
  refine ⟨hp, ?_⟩
  rw [hlast, hx]
  simp [RCLStep, hz]

theorem DPath.exists_node_contact_cPath_to_face_edge_of_cycle_contact
    {r c : List G.Dart} {x s : G.Dart} {p : List G.Dart}
    (hc : G.RCLCycle r c)
    (hp : G.DPath r s p)
    (hlast : (s :: p).getLastD s = x)
    (hcontact : ∃ y : G.Dart, y ∈ s :: p ∧ y ∈ c)
    (hx'not : G.face (G.edge x) ∉ c) :
    ∃ x1 : G.Dart, ∃ q : List G.Dart,
      G.node x1 ∈ c ∧
        G.CPath x1 q ∧
          (x1 :: q).getLastD x1 = G.face (G.edge x) ∧
            ∀ y : G.Dart, y ∈ x1 :: q → y ∉ c := by
  classical
  induction p generalizing s with
  | nil =>
      have hsx : s = x := by
        simpa [List.getLastD] using hlast
      subst x
      rcases hcontact with ⟨y, hy, hyc⟩
      have hsC : s ∈ c := by
        simp at hy
        subst y
        exact hyc
      refine ⟨G.face (G.edge s), [], ?_, ?_, ?_, ?_⟩
      · simpa using hsC
      · simp [CPath]
      · simp [List.getLastD]
      · intro y hy
        simp at hy
        subst y
        exact hx'not
  | cons y p ih =>
      have hp' : G.DLink r s y ∧ G.DPath r y p := by
        simpa [DPath] using hp
      have hlastTail : (y :: p).getLastD y = x := by
        simpa [List.getLastD] using hlast
      by_cases htailContact :
          ∃ z : G.Dart, z ∈ y :: p ∧ z ∈ c
      · exact ih hp'.2 hlastTail htailContact
      · have hsC : s ∈ c := by
          rcases hcontact with ⟨z, hzmem, hzc⟩
          rw [List.mem_cons] at hzmem
          rcases hzmem with hzs | hztail
          · subst z
            exact hzc
          · exact False.elim (htailContact ⟨z, hztail, hzc⟩)
        have hyNotC : y ∉ c := by
          intro hyc
          exact htailContact ⟨y, by simp, hyc⟩
        have hstepC : G.RCLStep r s ∈ c :=
          RCLCycle.step_mem (G := G) hc hsC
        have hfaceC : G.face s ∈ c := by
          rwa [RCLStep.eq_face_of_not_mem (G := G) hp'.1.1] at hstepC
        rcases hp'.1.2 with hnode | hface
        · subst y
          refine ⟨G.node.symm s, p ++ [G.face (G.edge x)], ?_, ?_, ?_, ?_⟩
          · simpa using hsC
          · exact DPath.to_cPath_snoc_face_edge
              (G := G) hp'.2 hlastTail
          · exact List.getLastD_cons_append_singleton
              (G.node.symm s) (G.face (G.edge x)) p
          · intro z hz
            have hzCases :
                z ∈ G.node.symm s :: p ∨
                  z = G.face (G.edge x) := by
              simpa [List.mem_append, or_assoc] using hz
            rcases hzCases with hzTail | hzLast
            · intro hzc
              exact htailContact ⟨z, hzTail, hzc⟩
            · subst z
              exact hx'not
        · subst y
          exact False.elim (hyNotC hfaceC)

theorem DConnect.to_reachable
    {r : List G.Dart} {x y : G.Dart}
    (hxy : G.DConnect r x y) :
    G.Reachable (G.node.symm y) x :=
  hxy.lift' id fun _ _ h => DLink.to_reachable (G := G) h

theorem DConnect.exists_dPath
    {r : List G.Dart} {x y : G.Dart}
    (hxy : G.DConnect r x y) :
    ∃ p : List G.Dart,
      G.DPath r (G.node.symm y) p ∧
        (G.node.symm y :: p).getLastD (G.node.symm y) = x := by
  induction hxy with
  | refl =>
      exact ⟨[], by simp, by simp [List.getLastD]⟩
  | tail _ hstep ih =>
      rcases ih with ⟨p, hp, hlast⟩
      exact ⟨p ++ [_],
        DPath.snoc (G := G) hp hlast hstep,
        List.getLastD_cons_append_singleton (G.node.symm y) _ p⟩

theorem DiskN.exists_dPath_cycle_contact_of_ring_subset
    {r c : List G.Dart} {x : G.Dart}
    (hc : G.RCLCycle r c)
    (hrc : ∀ y : G.Dart, y ∈ r → y ∈ c)
    (hx : G.DiskN r x) :
    ∃ s : G.Dart, ∃ p : List G.Dart,
      G.DPath r s p ∧
        (s :: p).getLastD s = x ∧
          ∃ y : G.Dart, y ∈ s :: p ∧ y ∈ c := by
  rcases hx with ⟨y, hyR, hxy⟩
  rcases DConnect.exists_dPath (G := G) hxy with ⟨p, hp, hlast⟩
  have hyC : y ∈ c := hrc y hyR
  have hsC : G.node.symm y ∈ c :=
    RCLCycle.node_symm_mem_of_ring_mem (G := G) hc hyC hyR
  exact ⟨G.node.symm y, p, hp, hlast,
    ⟨G.node.symm y, by simp, hsC⟩⟩

theorem DiskN.exists_node_contact_cPath_to_face_edge_of_ring_subset
    {r c : List G.Dart} {x : G.Dart}
    (hc : G.RCLCycle r c)
    (hrc : ∀ y : G.Dart, y ∈ r → y ∈ c)
    (hx : G.DiskN r x)
    (hx'not : G.face (G.edge x) ∉ c) :
    ∃ x1 : G.Dart, ∃ q : List G.Dart,
      G.node x1 ∈ c ∧
        G.CPath x1 q ∧
          (x1 :: q).getLastD x1 = G.face (G.edge x) ∧
            ∀ y : G.Dart, y ∈ x1 :: q → y ∉ c := by
  rcases DiskN.exists_dPath_cycle_contact_of_ring_subset
      (G := G) hc hrc hx with
    ⟨s, p, hp, hlast, hcontact⟩
  exact DPath.exists_node_contact_cPath_to_face_edge_of_cycle_contact
    (G := G) hc hp hlast hcontact hx'not

theorem dConnect_step_node_symm
    {r : List G.Dart} {x y : G.Dart}
    (hxy : G.DConnect r x y)
    (hx : x ∉ r) :
    G.DConnect r (G.node.symm x) y :=
  hxy.trans
    (Relation.ReflTransGen.single ⟨hx, CLink.node_symm (G := G) x⟩)

theorem dConnect_step_face
    {r : List G.Dart} {x y : G.Dart}
    (hxy : G.DConnect r x y)
    (hx : x ∉ r) :
    G.DConnect r (G.face x) y :=
  hxy.trans
    (Relation.ReflTransGen.single ⟨hx, CLink.face (G := G) x⟩)

theorem diskN_node_symm_of_mem
    {r : List G.Dart} {x : G.Dart}
    (hx : x ∈ r) :
    G.DiskN r (G.node.symm x) :=
  ⟨x, hx, G.dConnect_refl_node_symm r x⟩

theorem diskN_node_symm
    {r : List G.Dart} {x : G.Dart}
    (hx : G.DiskN r x) :
    G.DiskN r (G.node.symm x) := by
  by_cases hxmem : x ∈ r
  · exact G.diskN_node_symm_of_mem hxmem
  · rcases hx with ⟨y, hy, hxy⟩
    exact ⟨y, hy, G.dConnect_step_node_symm hxy hxmem⟩

private theorem holds_iterate
    {α : Type _} (f : α → α) (P : α → Prop)
    (hstep : ∀ ⦃x⦄, P x → P (f x))
    (n : Nat) {x : α} (hx : P x) :
    P ((f^[n]) x) := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih => exact ih (hstep hx)

private theorem holds_of_permReachable
    {α : Type _} [Fintype α]
    (f : Equiv.Perm α) (P : α → Prop)
    (hstep : ∀ ⦃x⦄, P x → P (f x))
    {x y : α} (hxy : PermReachable f x y) (hx : P x) :
    P y := by
  rcases permReachable_exists_iterate f hxy with ⟨n, rfl⟩
  exact holds_iterate f P hstep n hx

theorem diskN_node_symm_iterate
    {r : List G.Dart} (n : Nat) {x : G.Dart}
    (hx : G.DiskN r x) :
    G.DiskN r (((G.node.symm : G.Dart → G.Dart)^[n]) x) :=
  holds_iterate G.node.symm (G.DiskN r)
    (by intro z hz; exact G.diskN_node_symm hz) n hx

theorem diskN_of_nodeSymmReachable
    [Fintype G.Dart]
    {r : List G.Dart} {x y : G.Dart}
    (hxy : PermReachable G.node.symm x y)
    (hx : G.DiskN r x) :
    G.DiskN r y :=
  holds_of_permReachable G.node.symm (G.DiskN r)
    (by intro z hz; exact G.diskN_node_symm hz) hxy hx

theorem diskN_node_symm_iff
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart} :
    G.DiskN r (G.node.symm x) ↔ G.DiskN r x := by
  constructor
  · intro hx
    apply G.diskN_of_nodeSymmReachable
      (x := G.node.symm x)
      (y := x)
    · simpa using
        PermReachable.backward G.node.symm (G.node.symm x)
    · exact hx
  · exact G.diskN_node_symm

theorem diskN_node_iff
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart} :
    G.DiskN r (G.node x) ↔ G.DiskN r x := by
  have h := diskN_node_symm_iff (G := G) (r := r) (x := G.node x)
  simpa using h.symm

/-- The exclusive two-way `DiskN` partition used in Coq
`revsnip.v::diskN_chord_ring`.  The cover and disjointness clauses together
are the propositional form of Coq's Boolean-sum identity
`diskN cr₁ + diskN cr₂ = diskN r`. -/
def DiskNPartition
    (r cr₁ cr₂ : List G.Dart) (x : G.Dart) : Prop :=
  ((G.DiskN cr₁ x ∨ G.DiskN cr₂ x) ↔ G.DiskN r x) ∧
    ¬ (G.DiskN cr₁ x ∧ G.DiskN cr₂ x)

theorem DiskNPartition.left_iff
    {r cr₁ cr₂ : List G.Dart} {x : G.Dart}
    (h : G.DiskNPartition r cr₁ cr₂ x) :
    G.DiskN cr₁ x ↔ G.DiskN r x ∧ ¬ G.DiskN cr₂ x := by
  constructor
  · intro hx
    exact ⟨h.1.1 (Or.inl hx), fun hx₂ => h.2 ⟨hx, hx₂⟩⟩
  · rintro ⟨hr, hx₂⟩
    rcases h.1.2 hr with hx₁ | hx₂'
    · exact hx₁
    · exact False.elim (hx₂ hx₂')

theorem DiskNPartition.right_iff
    {r cr₁ cr₂ : List G.Dart} {x : G.Dart}
    (h : G.DiskNPartition r cr₁ cr₂ x) :
    G.DiskN cr₂ x ↔ G.DiskN r x ∧ ¬ G.DiskN cr₁ x := by
  constructor
  · intro hx
    exact ⟨h.1.1 (Or.inr hx), fun hx₁ => h.2 ⟨hx₁, hx⟩⟩
  · rintro ⟨hr, hx₁⟩
    rcases h.1.2 hr with hx₁' | hx₂
    · exact False.elim (hx₁ hx₁')
    · exact hx₂

theorem DiskNPartition.congr
    {r cr₁ cr₂ : List G.Dart} {x y : G.Dart}
    (hr : G.DiskN r x ↔ G.DiskN r y)
    (hcr₁ : G.DiskN cr₁ x ↔ G.DiskN cr₁ y)
    (hcr₂ : G.DiskN cr₂ x ↔ G.DiskN cr₂ y)
    (hy : G.DiskNPartition r cr₁ cr₂ y) :
    G.DiskNPartition r cr₁ cr₂ x := by
  simpa only [DiskNPartition, hr, hcr₁, hcr₂] using hy

theorem diskNPartition_node_symm_step
    [Fintype G.Dart]
    {r cr₁ cr₂ : List G.Dart} {x y : G.Dart}
    (hyx : y = G.node.symm x)
    (hy : G.DiskNPartition r cr₁ cr₂ y) :
    G.DiskNPartition r cr₁ cr₂ x := by
  subst y
  exact DiskNPartition.congr (G := G)
    (diskN_node_symm_iff (G := G) (r := r)).symm
    (diskN_node_symm_iff (G := G) (r := cr₁)).symm
    (diskN_node_symm_iff (G := G) (r := cr₂)).symm
    hy

theorem diskNPartition_node_step
    [Fintype G.Dart]
    {r cr₁ cr₂ : List G.Dart} {x y : G.Dart}
    (hyx : y = G.node x)
    (hy : G.DiskNPartition r cr₁ cr₂ y) :
    G.DiskNPartition r cr₁ cr₂ x := by
  subst y
  exact DiskNPartition.congr (G := G)
    (diskN_node_iff (G := G) (r := r)).symm
    (diskN_node_iff (G := G) (r := cr₁)).symm
    (diskN_node_iff (G := G) (r := cr₂)).symm
    hy

theorem diskN_split_node_symm_step
    [Fintype G.Dart]
    {r cr₁ cr₂ : List G.Dart} {x y : G.Dart}
    (hyx : y = G.node.symm x)
    (hy :
      G.DiskN cr₁ y ↔ G.DiskN r y ∧ ¬ G.DiskN cr₂ y) :
    G.DiskN cr₁ x ↔ G.DiskN r x ∧ ¬ G.DiskN cr₂ x := by
  subst y
  constructor
  · intro hx₁
    have hy₁ : G.DiskN cr₁ (G.node.symm x) :=
      (diskN_node_symm_iff (G := G) (r := cr₁)).2 hx₁
    have hyr := hy.1 hy₁
    refine ⟨(diskN_node_symm_iff (G := G) (r := r)).1 hyr.1, ?_⟩
    intro hx₂
    exact hyr.2
      ((diskN_node_symm_iff (G := G) (r := cr₂)).2 hx₂)
  · rintro ⟨hx, hx₂⟩
    have hyr : G.DiskN r (G.node.symm x) :=
      (diskN_node_symm_iff (G := G) (r := r)).2 hx
    have hy₂ : ¬ G.DiskN cr₂ (G.node.symm x) := by
      intro hy₂
      exact hx₂ ((diskN_node_symm_iff (G := G) (r := cr₂)).1 hy₂)
    exact (diskN_node_symm_iff (G := G) (r := cr₁)).1
      (hy.2 ⟨hyr, hy₂⟩)

theorem diskN_split_node_step
    [Fintype G.Dart]
    {r cr₁ cr₂ : List G.Dart} {x y : G.Dart}
    (hyx : y = G.node x)
    (hy :
      G.DiskN cr₁ y ↔ G.DiskN r y ∧ ¬ G.DiskN cr₂ y) :
    G.DiskN cr₁ x ↔ G.DiskN r x ∧ ¬ G.DiskN cr₂ x := by
  subst y
  constructor
  · intro hx₁
    have hy₁ : G.DiskN cr₁ (G.node x) :=
      (diskN_node_iff (G := G) (r := cr₁)).2 hx₁
    have hyr := hy.1 hy₁
    refine ⟨(diskN_node_iff (G := G) (r := r)).1 hyr.1, ?_⟩
    intro hx₂
    exact hyr.2
      ((diskN_node_iff (G := G) (r := cr₂)).2 hx₂)
  · rintro ⟨hx, hx₂⟩
    have hyr : G.DiskN r (G.node x) :=
      (diskN_node_iff (G := G) (r := r)).2 hx
    have hy₂ : ¬ G.DiskN cr₂ (G.node x) := by
      intro hy₂
      exact hx₂ ((diskN_node_iff (G := G) (r := cr₂)).1 hy₂)
    exact (diskN_node_iff (G := G) (r := cr₁)).1
      (hy.2 ⟨hyr, hy₂⟩)

theorem diskN_of_mem
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart}
    (hx : x ∈ r) :
    G.DiskN r x := by
  have hbase : G.DiskN r (G.node.symm x) :=
    G.diskN_node_symm_of_mem hx
  have hreach : PermReachable G.node.symm (G.node.symm x) x := by
    simpa using PermReachable.backward G.node.symm (G.node.symm x)
  exact G.diskN_of_nodeSymmReachable hreach hbase

theorem diskN_face_of_not_mem
    {r : List G.Dart} {x : G.Dart}
    (hx : G.DiskN r x)
    (hxmem : x ∉ r) :
    G.DiskN r (G.face x) := by
  rcases hx with ⟨y, hy, hxy⟩
  exact ⟨y, hy, G.dConnect_step_face hxy hxmem⟩

theorem diskN_face_of_not_faceBand
    {r : List G.Dart} {x : G.Dart}
    (hx : G.DiskN r x)
    (hband : ¬ G.FaceBand r x) :
    G.DiskN r (G.face x) := by
  apply G.diskN_face_of_not_mem hx
  intro hxmem
  exact hband ⟨x, hxmem, PermReachable.refl G.face x⟩

theorem diskF_face
    {r : List G.Dart} {x : G.Dart}
    (hx : G.DiskF r x) :
    G.DiskF r (G.face x) := by
  rcases hx with ⟨hxN, hxBand⟩
  refine ⟨G.diskN_face_of_not_faceBand hxN hxBand, ?_⟩
  rintro ⟨y, hy, hyface⟩
  apply hxBand
  exact ⟨y, hy, PermReachable.trans G.face hyface
    (by simpa using PermReachable.backward G.face (G.face x))⟩

theorem diskF_face_iterate
    {r : List G.Dart} (n : Nat) {x : G.Dart}
    (hx : G.DiskF r x) :
    G.DiskF r (((G.face : G.Dart → G.Dart)^[n]) x) :=
  holds_iterate G.face (G.DiskF r)
    (by intro z hz; exact G.diskF_face hz) n hx

theorem diskF_of_faceReachable
    [Fintype G.Dart]
    {r : List G.Dart} {x y : G.Dart}
    (hxy : PermReachable G.face x y)
    (hx : G.DiskF r x) :
    G.DiskF r y :=
  holds_of_permReachable G.face (G.DiskF r)
    (by intro z hz; exact G.diskF_face hz) hxy hx

theorem diskN_face_iterate_of_not_faceBand
    {r : List G.Dart} (n : Nat) {x : G.Dart}
    (hx : G.DiskN r x)
    (hband : ¬ G.FaceBand r x) :
    G.DiskN r (((G.face : G.Dart → G.Dart)^[n]) x) := by
  have hstep :
      ∀ ⦃z : G.Dart⦄,
        (G.DiskN r z ∧ ¬ G.FaceBand r z) →
          G.DiskN r (G.face z) ∧ ¬ G.FaceBand r (G.face z) := by
    rintro z ⟨hzN, hzBand⟩
    refine ⟨G.diskN_face_of_not_faceBand hzN hzBand, ?_⟩
    rintro ⟨u, hu, huface⟩
    exact hzBand ⟨u, hu, PermReachable.trans G.face huface
      (by simpa using PermReachable.backward G.face (G.face z))⟩
  exact (holds_iterate G.face
    (fun z => G.DiskN r z ∧ ¬ G.FaceBand r z)
    hstep n ⟨hx, hband⟩).1

theorem diskN_of_faceReachable_of_not_faceBand
    [Fintype G.Dart]
    {r : List G.Dart} {x y : G.Dart}
    (hxy : PermReachable G.face x y)
    (hx : G.DiskN r x)
    (hband : ¬ G.FaceBand r x) :
    G.DiskN r y := by
  rcases permReachable_exists_iterate G.face hxy with ⟨n, hn⟩
  simpa [hn] using G.diskN_face_iterate_of_not_faceBand n hx hband

theorem diskN_faceReachable_iff_of_not_faceBand
    [Fintype G.Dart]
    {r : List G.Dart} {x y : G.Dart}
    (hxy : PermReachable G.face x y)
    (hband : ¬ G.FaceBand r x) :
    G.DiskN r y ↔ G.DiskN r x := by
  have hband_y : ¬ G.FaceBand r y := by
    intro hy
    rcases hy with ⟨z, hz, hzy⟩
    exact hband
      ⟨z, hz, PermReachable.trans G.face hzy
        (PermReachable.symm G.face hxy)⟩
  constructor
  · intro hy
    exact G.diskN_of_faceReachable_of_not_faceBand
      (PermReachable.symm G.face hxy) hy hband_y
  · intro hx
    exact G.diskN_of_faceReachable_of_not_faceBand hxy hx hband

theorem diskN_split_face_step_of_not_faceBand
    [Fintype G.Dart]
    {r cr₁ cr₂ : List G.Dart} {x y : G.Dart}
    (hyx : y = G.face x)
    (hrBand : ¬ G.FaceBand r x)
    (hcr₁Band : ¬ G.FaceBand cr₁ x)
    (hcr₂Band : ¬ G.FaceBand cr₂ x)
    (hy :
      G.DiskN cr₁ y ↔ G.DiskN r y ∧ ¬ G.DiskN cr₂ y) :
    G.DiskN cr₁ x ↔ G.DiskN r x ∧ ¬ G.DiskN cr₂ x := by
  subst y
  have hface : PermReachable G.face x (G.face x) :=
    PermReachable.forward G.face x
  have hcr₁ :
      G.DiskN cr₁ (G.face x) ↔ G.DiskN cr₁ x :=
    G.diskN_faceReachable_iff_of_not_faceBand hface hcr₁Band
  have hr :
      G.DiskN r (G.face x) ↔ G.DiskN r x :=
    G.diskN_faceReachable_iff_of_not_faceBand hface hrBand
  have hcr₂ :
      G.DiskN cr₂ (G.face x) ↔ G.DiskN cr₂ x :=
    G.diskN_faceReachable_iff_of_not_faceBand hface hcr₂Band
  constructor
  · intro hx₁
    have hy₁ : G.DiskN cr₁ (G.face x) := hcr₁.2 hx₁
    have hyr := hy.1 hy₁
    refine ⟨hr.1 hyr.1, ?_⟩
    intro hx₂
    exact hyr.2 (hcr₂.2 hx₂)
  · rintro ⟨hx, hx₂⟩
    have hyr : G.DiskN r (G.face x) := hr.2 hx
    have hy₂ : ¬ G.DiskN cr₂ (G.face x) := by
      intro hy₂
      exact hx₂ (hcr₂.1 hy₂)
    exact hcr₁.1 (hy.2 ⟨hyr, hy₂⟩)

theorem diskN_split_face_step_of_faceBand_union
    [Fintype G.Dart]
    {r cr₁ cr₂ : List G.Dart} {x y : G.Dart}
    (hyx : y = G.face x)
    (hFaceBand :
      ∀ u : G.Dart,
        (G.FaceBand cr₁ u ∨ G.FaceBand cr₂ u) ↔ G.FaceBand r u)
    (hrBand : ¬ G.FaceBand r x)
    (hy :
      G.DiskN cr₁ y ↔ G.DiskN r y ∧ ¬ G.DiskN cr₂ y) :
    G.DiskN cr₁ x ↔ G.DiskN r x ∧ ¬ G.DiskN cr₂ x := by
  have hcr₁Band : ¬ G.FaceBand cr₁ x := by
    intro hx
    exact hrBand ((hFaceBand x).1 (Or.inl hx))
  have hcr₂Band : ¬ G.FaceBand cr₂ x := by
    intro hx
    exact hrBand ((hFaceBand x).1 (Or.inr hx))
  exact G.diskN_split_face_step_of_not_faceBand
    hyx hrBand hcr₁Band hcr₂Band hy

theorem diskFC_face
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart}
    (hx : G.DiskFC r x) :
    G.DiskFC r (G.face x) := by
  rcases hx with ⟨hxN, hxBand⟩
  have hfaceBand : ¬ G.FaceBand r (G.face x) := by
    rintro ⟨y, hy, hyface⟩
    exact hxBand
      ⟨y, hy, PermReachable.trans G.face hyface
        (by simpa using PermReachable.backward G.face (G.face x))⟩
  refine ⟨?_, hfaceBand⟩
  intro hfaceN
  have hfaceF : G.DiskF r (G.face x) := ⟨hfaceN, hfaceBand⟩
  have hxF : G.DiskF r x :=
    G.diskF_of_faceReachable
      (by simpa using PermReachable.backward G.face (G.face x)) hfaceF
  exact hxN hxF.1

theorem diskFC_face_iterate
    [Fintype G.Dart]
    {r : List G.Dart} (n : Nat) {x : G.Dart}
    (hx : G.DiskFC r x) :
    G.DiskFC r (((G.face : G.Dart → G.Dart)^[n]) x) :=
  holds_iterate G.face (G.DiskFC r)
    (by intro z hz; exact G.diskFC_face hz) n hx

theorem diskFC_of_faceReachable
    [Fintype G.Dart]
    {r : List G.Dart} {x y : G.Dart}
    (hxy : PermReachable G.face x y)
    (hx : G.DiskFC r x) :
    G.DiskFC r y :=
  holds_of_permReachable G.face (G.DiskFC r)
    (by intro z hz; exact G.diskFC_face hz) hxy hx

theorem diskE_iff
    {r : List G.Dart} {x : G.Dart} :
    G.DiskE r x ↔ G.DiskN r x ∧ x ∉ r :=
  Iff.rfl

theorem diskN_E
    [Fintype G.Dart]
    {r : List G.Dart} {x : G.Dart} :
    G.DiskN r x ↔ x ∈ r ∨ G.DiskE r x := by
  constructor
  · intro hx
    by_cases hxmem : x ∈ r
    · exact Or.inl hxmem
    · exact Or.inr ⟨hx, hxmem⟩
  · rintro (hxmem | hxE)
    · exact G.diskN_of_mem hxmem
    · exact hxE.1

theorem diskF_iff
    {r : List G.Dart} {x : G.Dart} :
    G.DiskF r x ↔ G.DiskN r x ∧ ¬ G.FaceBand r x :=
  Iff.rfl

theorem diskFC_iff
    {r : List G.Dart} {x : G.Dart} :
    G.DiskFC r x ↔ ¬ G.DiskN r x ∧ ¬ G.FaceBand r x :=
  Iff.rfl

/-- Face orbits that meet a dart predicate.  This is the Prop-valued analogue
of the orbit subset counted by Coq `fcard face A`. -/
def FaceOrbitMeeting (A : G.Dart → Prop) : Type _ :=
  { o : G.FaceOrbit // ∃ x : G.Dart, PermOrbit.of G.face x = o ∧ A x }

/-- Count the face orbits meeting a predicate.  On finite hypermaps this is
Coq `fcard face A`; for non-finite types `Nat.card` follows Lean's usual
cardinality convention. -/
noncomputable def FaceOrbitCountOf (A : G.Dart → Prop) : Nat :=
  Nat.card (G.FaceOrbitMeeting A)

noncomputable def faceOrbitMeetingEquivOfIff
    {A B : G.Dart → Prop}
    (hAB : ∀ x : G.Dart, A x ↔ B x) :
    G.FaceOrbitMeeting A ≃ G.FaceOrbitMeeting B where
  toFun o := by
    exact ⟨o.1, by
      rcases o.2 with ⟨x, hox, hx⟩
      exact ⟨x, hox, (hAB x).1 hx⟩⟩
  invFun o := by
    exact ⟨o.1, by
      rcases o.2 with ⟨x, hox, hx⟩
      exact ⟨x, hox, (hAB x).2 hx⟩⟩
  left_inv o := Subtype.ext rfl
  right_inv o := Subtype.ext rfl

theorem faceOrbitCountOf_congr
    {A B : G.Dart → Prop}
    (hAB : ∀ x : G.Dart, A x ↔ B x) :
    G.FaceOrbitCountOf A = G.FaceOrbitCountOf B := by
  rw [FaceOrbitCountOf]
  exact Nat.card_congr (G.faceOrbitMeetingEquivOfIff hAB)

/-- Face orbits meeting a disjoint union split as the sum of the two orbit
types, provided the second predicate is invariant on face orbits. -/
noncomputable def faceOrbitMeetingOrEquiv
    (A B : G.Dart → Prop)
    (hB : ∀ x y : G.Dart, PermReachable G.face x y → (B x ↔ B y))
    (hdisjoint : ∀ x : G.Dart, A x → ¬ B x) :
    G.FaceOrbitMeeting (fun x => A x ∨ B x) ≃
      G.FaceOrbitMeeting A ⊕ G.FaceOrbitMeeting B := by
  classical
  let p : G.FaceOrbit → Prop := fun o =>
    ∃ x : G.Dart, PermOrbit.of G.face x = o ∧ A x
  let q : G.FaceOrbit → Prop := fun o =>
    ∃ x : G.Dart, PermOrbit.of G.face x = o ∧ B x
  have hpq : Disjoint p q := by
    refine Pi.disjoint_iff.mpr fun o ↦ Prop.disjoint_iff.mpr ?_
    rintro ⟨⟨x, hxo, hx⟩, y, hyo, hy⟩
    have hxy : PermReachable G.face x y :=
      Quotient.exact (hxo.trans hyo.symm)
    exact hdisjoint x hx ((hB x y hxy).2 hy)
  let eUnion :
      G.FaceOrbitMeeting (fun x => A x ∨ B x) ≃
        {o : G.FaceOrbit // p o ∨ q o} :=
    Equiv.subtypeEquivRight (fun o => by
      constructor
      · rintro ⟨x, hxo, hx | hx⟩
        · exact Or.inl ⟨x, hxo, hx⟩
        · exact Or.inr ⟨x, hxo, hx⟩
      · rintro (⟨x, hxo, hx⟩ | ⟨x, hxo, hx⟩)
        · exact ⟨x, hxo, Or.inl hx⟩
        · exact ⟨x, hxo, Or.inr hx⟩)
  exact eUnion.trans (subtypeOrEquiv p q hpq)

theorem faceOrbitCountOf_or
    (A B : G.Dart → Prop)
    (hB : ∀ x y : G.Dart, PermReachable G.face x y → (B x ↔ B y))
    (hdisjoint : ∀ x : G.Dart, A x → ¬ B x) :
    G.FaceOrbitCountOf (fun x => A x ∨ B x) =
      G.FaceOrbitCountOf A + G.FaceOrbitCountOf B := by
  haveI : Finite (G.FaceOrbitMeeting A) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Finite (G.FaceOrbitMeeting B) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  unfold FaceOrbitCountOf
  rw [← Nat.card_sum]
  exact Nat.card_congr (G.faceOrbitMeetingOrEquiv A B hB hdisjoint)

theorem faceOrbitCountOf_pos_iff_exists
    [Fintype G.Dart]
    {A : G.Dart → Prop} :
    0 < G.FaceOrbitCountOf A ↔ ∃ x : G.Dart, A x := by
  haveI : Finite (G.FaceOrbitMeeting A) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  constructor
  · intro h
    rcases (Nat.card_pos_iff.mp h).1 with ⟨o⟩
    rcases o.2 with ⟨x, _hox, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact Nat.card_pos_iff.mpr
      ⟨⟨⟨PermOrbit.of G.face x, x, rfl, hx⟩⟩, inferInstance⟩

theorem one_lt_faceOrbitCountOf_iff_exists_not_faceReachable
    [Fintype G.Dart]
    {A : G.Dart → Prop} :
    1 < G.FaceOrbitCountOf A ↔
      ∃ x : G.Dart, A x ∧
        ∃ y : G.Dart, A y ∧ ¬ PermReachable G.face x y := by
  haveI : Finite (G.FaceOrbitMeeting A) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  constructor
  · intro h
    have hnontrivial : Nontrivial (G.FaceOrbitMeeting A) :=
      (Finite.one_lt_card_iff_nontrivial).1 (by
        simpa [FaceOrbitCountOf] using h)
    rcases exists_pair_ne (G.FaceOrbitMeeting A) with ⟨o, p, hop⟩
    rcases o.2 with ⟨x, hox, hx⟩
    rcases p.2 with ⟨y, hpy, hy⟩
    refine ⟨x, hx, y, hy, ?_⟩
    intro hxy
    apply hop
    apply Subtype.ext
    calc
      o.1 = PermOrbit.of G.face x := hox.symm
      _ = PermOrbit.of G.face y := PermOrbit.of_eq_of G.face hxy
      _ = p.1 := hpy
  · rintro ⟨x, hx, y, hy, hxy⟩
    rw [FaceOrbitCountOf]
    apply (Finite.one_lt_card_iff_nontrivial).2
    apply nontrivial_iff.mpr
    refine ⟨⟨PermOrbit.of G.face x, x, rfl, hx⟩,
      ⟨PermOrbit.of G.face y, y, rfl, hy⟩, ?_⟩
    intro hEq
    apply hxy
    exact Quotient.exact (congrArg Subtype.val hEq)

/-- Coq `nontrivial_ring m r`: both strict face sides of the ring contain more
than `m` face orbits. -/
noncomputable def NontrivialRing (m : Nat) (r : List G.Dart) : Prop :=
  m < G.FaceOrbitCountOf (G.DiskF r) ∧
    m < G.FaceOrbitCountOf (G.DiskFC r)

theorem nontrivialRing_zero_iff
    [Fintype G.Dart]
    {r : List G.Dart} :
    G.NontrivialRing 0 r ↔
      (∃ x : G.Dart, G.DiskF r x) ∧
        ∃ x : G.Dart, G.DiskFC r x := by
  simp [NontrivialRing, faceOrbitCountOf_pos_iff_exists]

theorem nontrivialRing_one_iff
    [Fintype G.Dart]
    {r : List G.Dart} :
    G.NontrivialRing 1 r ↔
      (∃ x : G.Dart, G.DiskF r x ∧
        ∃ y : G.Dart, G.DiskF r y ∧ ¬ PermReachable G.face x y) ∧
      (∃ x : G.Dart, G.DiskFC r x ∧
        ∃ y : G.Dart, G.DiskFC r y ∧ ¬ PermReachable G.face x y) := by
  simp [NontrivialRing,
    one_lt_faceOrbitCountOf_iff_exists_not_faceReachable]

theorem FaceBand.of_mem
    {r : List G.Dart} {x u : G.Dart}
    (hx : x ∈ r)
    (hxu : PermReachable G.face x u) :
    G.FaceBand r u :=
  ⟨x, hx, hxu⟩

theorem FaceBand.of_faceReachable
    {r : List G.Dart} {u v : G.Dart}
    (hu : G.FaceBand r u)
    (huv : PermReachable G.face u v) :
    G.FaceBand r v := by
  rcases hu with ⟨x, hx, hxu⟩
  exact ⟨x, hx, PermReachable.trans G.face hxu huv⟩

theorem FaceBand.congr_faceReachable
    {r : List G.Dart} {u v : G.Dart}
    (huv : PermReachable G.face u v) :
    G.FaceBand r u ↔ G.FaceBand r v := by
  constructor
  · intro hu
    exact FaceBand.of_faceReachable (G := G) hu huv
  · intro hv
    exact FaceBand.of_faceReachable (G := G) hv
      (PermReachable.symm G.face huv)

theorem FaceBand.cons
    {r : List G.Dart} {x u : G.Dart} :
    G.FaceBand (x :: r) u ↔
      PermReachable G.face x u ∨ G.FaceBand r u := by
  constructor
  · rintro ⟨y, hy, hyu⟩
    cases hy with
    | head =>
        exact Or.inl hyu
    | tail _ hy =>
        exact Or.inr ⟨y, hy, hyu⟩
  · rintro (hxu | ⟨y, hy, hyu⟩)
    · exact ⟨x, by simp, hxu⟩
    · exact ⟨y, by simp [hy], hyu⟩

theorem FaceBand.append
    {r s : List G.Dart} {u : G.Dart} :
    G.FaceBand (r ++ s) u ↔ G.FaceBand r u ∨ G.FaceBand s u := by
  constructor
  · rintro ⟨x, hx, hxu⟩
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl ⟨x, hx, hxu⟩
    · exact Or.inr ⟨x, hx, hxu⟩
  · rintro (⟨x, hx, hxu⟩ | ⟨x, hx, hxu⟩)
    · exact ⟨x, List.mem_append_left s hx, hxu⟩
    · exact ⟨x, List.mem_append_right r hx, hxu⟩

theorem FaceBand.subset
    {r s : List G.Dart}
    (hsub : ∀ x : G.Dart, x ∈ r → x ∈ s)
    {u : G.Dart}
    (hu : G.FaceBand r u) :
    G.FaceBand s u := by
  rcases hu with ⟨x, hx, hxu⟩
  exact ⟨x, hsub x hx, hxu⟩

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
