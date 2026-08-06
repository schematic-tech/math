import Schematic.Math.GraphTheory.Embedding.Geometry.Chords

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

theorem diskE_edge
    [Fintype G.Dart]
    (hJ : G.Jordan)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x : G.Dart}
    (hx : G.DiskE r x) :
    G.DiskE r (G.edge x) := by
  classical
  let x' : G.Dart := G.face (G.edge x)
  have hx'Disk : G.DiskN r x' := by
    dsimp [x']
    exact G.diskN_face_edge_of_diskE hx
  have hx'reach : PermReachable G.face x' (G.edge x) := by
    dsimp [x']
    exact PermReachable.symm G.face
      (PermReachable.forward G.face (G.edge x))
  rcases G.exists_short_facePath_of_faceReachable hx'reach with
    ⟨q, hq, hlast, hqNodup⟩
  by_cases hhit : ∃ y : G.Dart, y ∈ x' :: q ∧ y ∈ r
  · rcases hhit with ⟨y, hyPath, hyR⟩
    rcases SimpleRLinkCycle.exists_rotated_cons (G := G) hr hyR with
      ⟨r1, hr1, hperm, _hyNotTail⟩
    let z : G.Dart := (y :: r1).getLastD y
    let z' : G.Dart := G.face (G.edge z)
    have hzRot : z ∈ y :: r1 := by
      dsimp [z]
      exact List.getLastD_cons_mem y r1
    have hzR : z ∈ r := by
      exact (hperm.mem_iff).1 hzRot
    have hzy : G.RLink z y := by
      dsimp [z]
      exact hr1.1.2
    have hyz' : PermReachable G.face y z' := by
      dsimp [z']
      exact RLink.face_edge_reachable (G := G) hzy
    have hx'y : PermReachable G.face x' y :=
      FacePath.mem_faceReachable (G := G) hq hyPath
    have hx'z' : PermReachable G.face x' z' :=
      PermReachable.trans G.face hx'y hyz'
    have hclose : G.face ((x' :: q).getLastD x') = x' := by
      dsimp [x']
      rw [hlast]
    have hz'Mem : z' ∈ x' :: q :=
      FacePath.mem_of_faceReachable_closed (G := G) hq hclose hx'z'
    rw [List.mem_cons] at hz'Mem
    rcases hz'Mem with hz'Head | hz'q
    · have hzEqx : z = x := by
        apply face_edge_injective (G := G)
        dsimp [z', x'] at hz'Head
        exact hz'Head
      exact False.elim (hx.2 (by simpa [hzEqx] using hzR))
    · rcases FacePath.exists_split_at_tail_mem (G := G) hq hz'q with
        ⟨q1, q2, hsplit, hq1, hfaceq1, hq2, hlastq2⟩
      have hfullNodup : (x' :: (q1 ++ z' :: q2)).Nodup := by
        simpa [hsplit] using hqNodup
      have hyCat : y ∈ (x' :: q1) ++ (z' :: q2) := by
        simpa [List.cons_append, List.append_assoc, hsplit] using hyPath
      rw [List.mem_append] at hyCat
      rcases hyCat with hyQ1 | hyTail
      · have hfullNodup' :
            (G.face (G.edge x) ::
              (q1 ++ G.face (G.edge z) :: q2)).Nodup := by
          simpa [x', z'] using hfullNodup
        have hq2' : G.FacePath (G.face (G.edge z)) q2 := by
          simpa [z'] using hq2
        have hlastq2' :
            (G.face (G.edge z) :: q2).getLastD
                (G.face (G.edge z)) =
              G.edge x := by
          simpa [z'] using hlastq2.trans hlast
        exact G.diskE_of_split_suffix_prior_ring_hit
          (hr := hr.2) hzR hfullNodup' hyQ1 hyR hzy hq2' hlastq2'
      · have hDiskRot : G.DiskN (y :: r1) x :=
          (DiskN.perm (G := G) hperm).2 hx.1
        exact False.elim
          (SimpleRLinkCycle.not_tail_hit_for_diskE_edge_split
            (G := G) hJ hr1 (x := x) (x' := x') (z' := z')
            (q1 := q1) (q2 := q2) (by rfl) (by rfl)
            hq1 hfaceq1 hq2 hyTail hfullNodup hyz' hDiskRot)
  · have havoid :
        ∀ y : G.Dart, y ∈ x' :: q → y ∉ r := by
      intro y hy hyR
      exact hhit ⟨y, hy, hyR⟩
    exact G.diskE_edge_of_facePath_avoids_ring hx
      (by simpa [x'] using hq)
      (by simpa [x'] using hlast)
      (by
        intro y hy
        exact havoid y (by simpa [x'] using hy))

theorem SimpleRLinkCycle.eq_of_same_rlink_source
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x y z : G.Dart}
    (hy : y ∈ r)
    (hz : z ∈ r)
    (hxy : G.RLink x y)
    (hxz : G.RLink x z) :
    y = z := by
  exact FaceSimple.eq_of_faceReachable_of_mem (G := G) hr.2 hy hz
    (PermReachable.trans G.face (PermReachable.symm G.face hxy) hxz)

theorem SimpleRLinkCycle.tail_eq_singleton_edge_of_mem_edge_head
    (hPlain : G.Plain)
    {x : G.Dart} {r1 : List G.Dart}
    (hr : G.SimpleRLinkCycle (x :: r1))
    (hedge : G.edge x ∈ r1) :
    r1 = [G.edge x] := by
  cases r1 with
  | nil =>
      cases hedge
  | cons y p =>
      have hyMem : y ∈ x :: y :: p := by simp
      have hedgeMem : G.edge x ∈ x :: y :: p := by
        simp [hedge]
      have hxy : G.RLink x y := by
        exact hr.1.1.1
      have hxe : G.RLink x (G.edge x) :=
        RLink.self_edge (G := G) x
      have hy_eq : y = G.edge x :=
        SimpleRLinkCycle.eq_of_same_rlink_source
          (G := G) hr hyMem hedgeMem hxy hxe
      subst y
      cases p with
      | nil =>
          rfl
      | cons z qs =>
          have hzMem : z ∈ x :: G.edge x :: z :: qs := by simp
          have hxMem : x ∈ x :: G.edge x :: z :: qs := by simp
          have hez : G.RLink (G.edge x) z := by
            exact hr.1.1.2.1
          have hex : G.RLink (G.edge x) x :=
            RLink.edge_self_of_plain (G := G) hPlain x
          have hz_eq : z = x :=
            SimpleRLinkCycle.eq_of_same_rlink_source
              (G := G) hr hzMem hxMem hez hex
          have hnodup : (x :: G.edge x :: z :: qs).Nodup :=
            FaceSimple.nodup (G := G) hr.2
          have hxNotTail : x ∉ G.edge x :: z :: qs :=
            (List.nodup_cons.mp hnodup).1
          exact False.elim (hxNotTail (by simp [hz_eq]))

theorem SimpleRLinkCycle.not_mem_edge_of_proper_plain
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    (hproper : G.ProperRing r)
    {x : G.Dart}
    (hx : x ∈ r) :
    G.edge x ∉ r := by
  intro hedge
  rcases (List.mem_iff_append).1 hx with ⟨pre, post, hsplit⟩
  have hrot :
      r.rotate pre.length = x :: (post ++ pre) := by
    rw [hsplit]
    rw [List.rotate_append_length_eq]
    simp
  have hrRot : G.SimpleRLinkCycle (x :: (post ++ pre)) := by
    have hcycle := SimpleRLinkCycle.rotate (G := G) pre.length hr
    simpa [hrot] using hcycle
  have hproperRot : G.ProperRing (x :: (post ++ pre)) := by
    have hproper' :
        G.ProperRing (r.rotate pre.length) :=
      (properRing_rotate_iff_of_plain (G := G) hPlain pre.length r).2 hproper
    simpa [hrot] using hproper'
  have hedgeRot0 : G.edge x ∈ r.rotate pre.length := by
    simpa [List.mem_rotate] using hedge
  have hedgeRot : G.edge x ∈ x :: (post ++ pre) := by
    simpa [hrot] using hedgeRot0
  have hedgeTail : G.edge x ∈ post ++ pre := by
    rw [List.mem_cons] at hedgeRot
    rcases hedgeRot with hedgeHead | hedgeTail
    · exact False.elim ((Plain.edge_ne (G := G) hPlain x) hedgeHead)
    · exact hedgeTail
  have htail :
      post ++ pre = [G.edge x] :=
    SimpleRLinkCycle.tail_eq_singleton_edge_of_mem_edge_head
      (G := G) hPlain hrRot hedgeTail
  rw [htail] at hproperRot
  simp [ProperRing, EdgePath] at hproperRot

theorem diskN_edge_ring
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    (hproper : G.ProperRing r)
    {x : G.Dart}
    (hx : x ∈ r) :
    ¬ G.DiskN r (G.edge x) := by
  intro hxDisk
  have hedgeNot : G.edge x ∉ r :=
    SimpleRLinkCycle.not_mem_edge_of_proper_plain
      (G := G) hPlain hr hproper hx
  have hxEdgeE : G.DiskE r (G.edge x) :=
    ⟨hxDisk, hedgeNot⟩
  have hxE : G.DiskE r x := by
    have h := G.diskE_edge hJ hr hxEdgeE
    simpa [Plain.edge_edge (G := G) hPlain x] using h
  exact hxE.2 hx

theorem SimpleRLinkCycle.not_diskN_edge_head_of_proper_plain
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {x : G.Dart} {r₁ : List G.Dart}
    (hr : G.SimpleRLinkCycle (x :: r₁))
    (hproper : G.ProperRing (x :: r₁)) :
    ¬ G.DiskN (x :: r₁) (G.edge x) :=
  G.diskN_edge_ring hJ hPlain hr hproper (by simp)

theorem SimpleRLinkCycle.not_diskN_source_of_edge_head_proper_plain
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {x : G.Dart} {r₁ : List G.Dart}
    (hr : G.SimpleRLinkCycle (G.edge x :: r₁))
    (hproper : G.ProperRing (G.edge x :: r₁)) :
    ¬ G.DiskN (G.edge x :: r₁) x := by
  simpa [Plain.edge_edge (G := G) hPlain x] using
    SimpleRLinkCycle.not_diskN_edge_head_of_proper_plain
      (G := G) hJ hPlain hr hproper

theorem SimpleRLinkCycle.not_diskN_edge_of_chord_prefix
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart} {x y₂ : G.Dart} {p₁ : List G.Dart}
    (hEdgeDisk : G.DiskE r (G.edge x))
    (hy₂r : y₂ ∈ r)
    (hr : G.SimpleRLinkCycle (x :: y₂ :: p₁)) :
    ¬ G.DiskN (x :: y₂ :: p₁) (G.edge x) := by
  have hproper :
      G.ProperRing (x :: y₂ :: p₁) :=
    G.properRing_chord_prefix_of_diskE_edge hEdgeDisk hy₂r
  exact
    SimpleRLinkCycle.not_diskN_edge_head_of_proper_plain
      (G := G) hJ hPlain hr hproper

theorem SimpleRLinkCycle.not_diskN_source_of_edge_chord_prefix
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart} {x y₁ : G.Dart} {q₁ : List G.Dart}
    (hDisk : G.DiskE r x)
    (hy₁r : y₁ ∈ r)
    (hr : G.SimpleRLinkCycle (G.edge x :: y₁ :: q₁)) :
    ¬ G.DiskN (G.edge x :: y₁ :: q₁) x := by
  have hEdgeEdgeDisk : G.DiskE r (G.edge (G.edge x)) := by
    simpa [Plain.edge_edge (G := G) hPlain x] using hDisk
  have hproper :
      G.ProperRing (G.edge x :: y₁ :: q₁) :=
    G.properRing_chord_prefix_of_diskE_edge
      (x := G.edge x) hEdgeEdgeDisk hy₁r
  exact
    SimpleRLinkCycle.not_diskN_source_of_edge_head_proper_plain
      (G := G) hJ hPlain hr hproper

/-- Base case of Coq `diskN_chord_ring` at the source dart `x`.  The first
chord ring contains `x`, while the second chord ring excludes `x` from its
disk by properness. -/
theorem diskN_chord_prefix_base_source
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart} {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hxDisk : G.DiskE r x)
    (hy₁r : y₁ ∈ r)
    (hcr₂ : G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂)) :
    G.DiskN (x :: y₂ :: p₁) x ↔
      G.DiskN r x ∧ ¬ G.DiskN (G.edge x :: y₁ :: p₂) x := by
  constructor
  · intro _hx
    exact ⟨hxDisk.1,
      SimpleRLinkCycle.not_diskN_source_of_edge_chord_prefix
        (G := G) hJ hPlain hxDisk hy₁r hcr₂⟩
  · intro _hx
    exact G.diskN_of_mem (by simp)

/-- Base case of Coq `diskN_chord_ring` at `edge x`.  The first chord ring
excludes `edge x`, while the second chord ring contains it at the head. -/
theorem diskN_chord_prefix_base_edge
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart} {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hEdgeDisk : G.DiskE r (G.edge x))
    (hy₂r : y₂ ∈ r)
    (hcr₁ : G.SimpleRLinkCycle (x :: y₂ :: p₁)) :
    G.DiskN (x :: y₂ :: p₁) (G.edge x) ↔
      G.DiskN r (G.edge x) ∧
        ¬ G.DiskN (G.edge x :: y₁ :: p₂) (G.edge x) := by
  constructor
  · intro hx
    exact False.elim
      (SimpleRLinkCycle.not_diskN_edge_of_chord_prefix
        (G := G) hJ hPlain hEdgeDisk hy₂r hcr₁ hx)
  · rintro ⟨_hx, hnot₂⟩
    exact False.elim (hnot₂ (G.diskN_of_mem (by simp)))

theorem diskE_edge_iff
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x : G.Dart} :
    G.DiskE r (G.edge x) ↔ G.DiskE r x := by
  constructor
  · intro hx
    have h := G.diskE_edge hJ hr hx
    simpa [Plain.edge_edge (G := G) hPlain x] using h
  · exact G.diskE_edge hJ hr

theorem diskN_edge_face_iff
    [Fintype G.Dart]
    (hPlain : G.Plain)
    {r : List G.Dart} {x : G.Dart} :
    G.DiskN r (G.edge x) ↔ G.DiskN r (G.face x) := by
  have hEdgeNode : G.edge x = G.node (G.face x) := by
    apply G.edge.injective
    calc
      G.edge (G.edge x) = x :=
        Plain.edge_edge (G := G) hPlain x
      _ = G.edge (G.node (G.face x)) :=
        (G.edge_node_face x).symm
  rw [hEdgeNode]
  exact diskN_node_iff (G := G) (r := r)

theorem diskN_edge_iff_of_not_mem
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x : G.Dart}
    (hx : x ∉ r)
    (hex : G.edge x ∉ r) :
    G.DiskN r (G.edge x) ↔ G.DiskN r x := by
  constructor
  · intro hEdge
    exact ((G.diskE_edge_iff hJ hPlain hr).1 ⟨hEdge, hex⟩).1
  · intro h
    exact ((G.diskE_edge_iff hJ hPlain hr).2 ⟨h, hx⟩).1

/-- Face-link induction step for Coq `revsnip.v::diskN_chord_ring`.
Away from the two chord heads, `cr₁` and `cr₂` partition the source ring as
lists.  The proof follows Coq's three ring-membership branches and transports
the exclusive `DiskN` partition from `face z` back to `z`. -/
theorem diskNPartition_face_step_of_mem_partition
    [Fintype G.Dart]
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {r cr₁ cr₂ : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    (hproper : G.ProperRing r)
    (hcr₁ : G.SimpleRLinkCycle cr₁)
    (hcr₂ : G.SimpleRLinkCycle cr₂)
    {c z w : G.Dart}
    (hwz : w = G.face z)
    (hbaseC : G.DiskNPartition r cr₁ cr₂ c)
    (hbaseEdgeC : G.DiskNPartition r cr₁ cr₂ (G.edge c))
    (hmem :
      ∀ u : G.Dart, u ≠ c → u ≠ G.edge c →
        (((u ∈ cr₁ ∨ u ∈ cr₂) ↔ u ∈ r) ∧
          ¬ (u ∈ cr₁ ∧ u ∈ cr₂)))
    (hw : G.DiskNPartition r cr₁ cr₂ w) :
    G.DiskNPartition r cr₁ cr₂ z := by
  subst w
  by_cases hzc : z = c
  · simpa [hzc] using hbaseC
  by_cases hzEdgeC : z = G.edge c
  · simpa [hzEdgeC] using hbaseEdgeC
  have hEdgeZC : G.edge z ≠ c := by
    intro h
    apply hzEdgeC
    calc
      z = G.edge (G.edge z) :=
        (Plain.edge_edge (G := G) hPlain z).symm
      _ = G.edge c := congrArg G.edge h
  have hEdgeZEdgeC : G.edge z ≠ G.edge c := by
    intro h
    exact hzc (G.edge.injective h)
  have hmemZ := hmem z hzc hzEdgeC
  have hmemEdgeZ := hmem (G.edge z) hEdgeZC hEdgeZEdgeC
  have hEdgePartition :
      G.DiskNPartition r cr₁ cr₂ (G.edge z) :=
    DiskNPartition.congr (G := G)
      (G.diskN_edge_face_iff hPlain)
      (G.diskN_edge_face_iff hPlain)
      (G.diskN_edge_face_iff hPlain)
      hw
  by_cases hzR : z ∈ r
  · have hzNR : G.DiskN r z := G.diskN_of_mem hzR
    have hEdgeNotNR : ¬ G.DiskN r (G.edge z) :=
      G.diskN_edge_ring hJ hPlain hr hproper hzR
    have hEdgeNotN₁ : ¬ G.DiskN cr₁ (G.edge z) := by
      intro h
      exact hEdgeNotNR (hEdgePartition.1.1 (Or.inl h))
    have hEdgeNotN₂ : ¬ G.DiskN cr₂ (G.edge z) := by
      intro h
      exact hEdgeNotNR (hEdgePartition.1.1 (Or.inr h))
    rcases hmemZ.1.2 hzR with hzCr₁ | hzCr₂
    · have hzNotCr₂ : z ∉ cr₂ := by
        intro hzCr₂
        exact hmemZ.2 ⟨hzCr₁, hzCr₂⟩
      have hzNotN₂ : ¬ G.DiskN cr₂ z := by
        intro hzN₂
        rcases (G.diskN_E (r := cr₂) (x := z)).1 hzN₂ with
          hzMem₂ | hzE₂
        · exact hzNotCr₂ hzMem₂
        · exact hEdgeNotN₂
            ((G.diskE_edge_iff hJ hPlain hcr₂).2 hzE₂).1
      refine ⟨?_, ?_⟩
      · constructor
        · intro _
          exact hzNR
        · intro _
          exact Or.inl (G.diskN_of_mem hzCr₁)
      · rintro ⟨_, hzN₂⟩
        exact hzNotN₂ hzN₂
    · have hzNotCr₁ : z ∉ cr₁ := by
        intro hzCr₁
        exact hmemZ.2 ⟨hzCr₁, hzCr₂⟩
      have hzNotN₁ : ¬ G.DiskN cr₁ z := by
        intro hzN₁
        rcases (G.diskN_E (r := cr₁) (x := z)).1 hzN₁ with
          hzMem₁ | hzE₁
        · exact hzNotCr₁ hzMem₁
        · exact hEdgeNotN₁
            ((G.diskE_edge_iff hJ hPlain hcr₁).2 hzE₁).1
      refine ⟨?_, ?_⟩
      · constructor
        · intro _
          exact hzNR
        · intro _
          exact Or.inr (G.diskN_of_mem hzCr₂)
      · rintro ⟨hzN₁, _⟩
        exact hzNotN₁ hzN₁
  · have hzNotCr₁ : z ∉ cr₁ := by
      intro hzCr₁
      exact hzR (hmemZ.1.1 (Or.inl hzCr₁))
    have hzNotCr₂ : z ∉ cr₂ := by
      intro hzCr₂
      exact hzR (hmemZ.1.1 (Or.inr hzCr₂))
    by_cases hEdgeZR : G.edge z ∈ r
    · have hzNotNR : ¬ G.DiskN r z := by
        intro hzNR
        have hzER : G.DiskE r z := ⟨hzNR, hzR⟩
        exact ((G.diskE_edge_iff hJ hPlain hr).2 hzER).2 hEdgeZR
      rcases hmemEdgeZ.1.2 hEdgeZR with hEdgeZCr₁ | hEdgeZCr₂
      · have hEdgeZN₁ : G.DiskN cr₁ (G.edge z) :=
          G.diskN_of_mem hEdgeZCr₁
        have hEdgeZNotN₂ : ¬ G.DiskN cr₂ (G.edge z) := by
          intro hEdgeZN₂
          exact hEdgePartition.2 ⟨hEdgeZN₁, hEdgeZN₂⟩
        have hzNotN₁ : ¬ G.DiskN cr₁ z := by
          intro hzN₁
          have hzE₁ : G.DiskE cr₁ z := ⟨hzN₁, hzNotCr₁⟩
          exact ((G.diskE_edge_iff hJ hPlain hcr₁).2 hzE₁).2
            hEdgeZCr₁
        have hzNotN₂ : ¬ G.DiskN cr₂ z := by
          intro hzN₂
          have hzE₂ : G.DiskE cr₂ z := ⟨hzN₂, hzNotCr₂⟩
          exact hEdgeZNotN₂
            ((G.diskE_edge_iff hJ hPlain hcr₂).2 hzE₂).1
        exact
          ⟨⟨fun h => False.elim (h.elim hzNotN₁ hzNotN₂),
              fun h => False.elim (hzNotNR h)⟩,
            fun h => hzNotN₁ h.1⟩
      · have hEdgeZN₂ : G.DiskN cr₂ (G.edge z) :=
          G.diskN_of_mem hEdgeZCr₂
        have hEdgeZNotN₁ : ¬ G.DiskN cr₁ (G.edge z) := by
          intro hEdgeZN₁
          exact hEdgePartition.2 ⟨hEdgeZN₁, hEdgeZN₂⟩
        have hzNotN₁ : ¬ G.DiskN cr₁ z := by
          intro hzN₁
          have hzE₁ : G.DiskE cr₁ z := ⟨hzN₁, hzNotCr₁⟩
          exact hEdgeZNotN₁
            ((G.diskE_edge_iff hJ hPlain hcr₁).2 hzE₁).1
        have hzNotN₂ : ¬ G.DiskN cr₂ z := by
          intro hzN₂
          have hzE₂ : G.DiskE cr₂ z := ⟨hzN₂, hzNotCr₂⟩
          exact ((G.diskE_edge_iff hJ hPlain hcr₂).2 hzE₂).2
            hEdgeZCr₂
        exact
          ⟨⟨fun h => False.elim (h.elim hzNotN₁ hzNotN₂),
              fun h => False.elim (hzNotNR h)⟩,
            fun h => hzNotN₁ h.1⟩
    · have hEdgeZNotCr₁ : G.edge z ∉ cr₁ := by
        intro h
        exact hEdgeZR (hmemEdgeZ.1.1 (Or.inl h))
      have hEdgeZNotCr₂ : G.edge z ∉ cr₂ := by
        intro h
        exact hEdgeZR (hmemEdgeZ.1.1 (Or.inr h))
      exact DiskNPartition.congr (G := G)
        (G.diskN_edge_iff_of_not_mem hJ hPlain hr hzR hEdgeZR).symm
        (G.diskN_edge_iff_of_not_mem
          hJ hPlain hcr₁ hzNotCr₁ hEdgeZNotCr₁).symm
        (G.diskN_edge_iff_of_not_mem
          hJ hPlain hcr₂ hzNotCr₂ hEdgeZNotCr₂).symm
        hEdgePartition

/-- Fixed-decomposition form of Coq `revsnip.v::diskN_chord_ring`.
The two chord rings exclusively partition the source ring's `DiskN`. -/
theorem diskNPartition_chord_prefix
    [Fintype G.Dart]
    (hConn : G.Connected)
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hr : G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂))
    (hproper : G.ProperRing (y₂ :: p₁ ++ y₁ :: p₂))
    (hxDisk : G.DiskE (y₂ :: p₁ ++ y₁ :: p₂) x)
    (hy₁r : y₁ ∈ y₂ :: p₁ ++ y₁ :: p₂)
    (hy₂r : y₂ ∈ y₂ :: p₁ ++ y₁ :: p₂)
    (hcr₁ : G.SimpleRLinkCycle (x :: y₂ :: p₁))
    (hcr₂ : G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂))
    (u : G.Dart) :
    G.DiskNPartition
      (y₂ :: p₁ ++ y₁ :: p₂)
      (x :: y₂ :: p₁)
      (G.edge x :: y₁ :: p₂)
      u := by
  let r : List G.Dart := y₂ :: p₁ ++ y₁ :: p₂
  let cr₁ : List G.Dart := x :: y₂ :: p₁
  let cr₂ : List G.Dart := G.edge x :: y₁ :: p₂
  have hEdgeDisk : G.DiskE r (G.edge x) :=
    (G.diskE_edge_iff hJ hPlain hr).2 hxDisk
  have hbaseX : G.DiskNPartition r cr₁ cr₂ x := by
    have hxN₁ : G.DiskN cr₁ x := G.diskN_of_mem (by simp [cr₁])
    have hxNotN₂ : ¬ G.DiskN cr₂ x :=
      SimpleRLinkCycle.not_diskN_source_of_edge_chord_prefix
        (G := G) hJ hPlain hxDisk hy₁r hcr₂
    exact
      ⟨⟨fun _ => hxDisk.1, fun _ => Or.inl hxN₁⟩,
        fun h => hxNotN₂ h.2⟩
  have hbaseEdgeX :
      G.DiskNPartition r cr₁ cr₂ (G.edge x) := by
    have hEdgeNotN₁ : ¬ G.DiskN cr₁ (G.edge x) :=
      SimpleRLinkCycle.not_diskN_edge_of_chord_prefix
        (G := G) hJ hPlain hEdgeDisk hy₂r hcr₁
    have hEdgeN₂ : G.DiskN cr₂ (G.edge x) :=
      G.diskN_of_mem (by simp [cr₂])
    exact
      ⟨⟨fun _ => hEdgeDisk.1, fun _ => Or.inr hEdgeN₂⟩,
        fun h => hEdgeNotN₁ h.1⟩
  have hArcNodup :
      (y₂ :: p₁ ++ y₁ :: p₂).Nodup :=
    FaceSimple.nodup (G := G) hr.2
  have hArcDisjoint :
      List.Disjoint (y₂ :: p₁) (y₁ :: p₂) := by
    exact hArcNodup.disjoint
  have hmem :
      ∀ z : G.Dart, z ≠ x → z ≠ G.edge x →
        (((z ∈ cr₁ ∨ z ∈ cr₂) ↔ z ∈ r) ∧
          ¬ (z ∈ cr₁ ∧ z ∈ cr₂)) := by
    intro z hzx hzEdgeX
    have hcover :
        (z ∈ cr₁ ∨ z ∈ cr₂) ↔ z ∈ r := by
      simp only [cr₁, cr₂, r, List.mem_cons, List.mem_append]
      tauto
    refine ⟨hcover, ?_⟩
    rintro ⟨hzCr₁, hzCr₂⟩
    have hzLeft : z ∈ y₂ :: p₁ := by
      simpa [cr₁, hzx] using hzCr₁
    have hzRight : z ∈ y₁ :: p₂ := by
      simpa [cr₂, hzEdgeX] using hzCr₂
    exact (List.disjoint_left.mp hArcDisjoint hzLeft) hzRight
  rcases Connected.exists_cPath (G := G) hConn u x with
    ⟨p, hp, hlast⟩
  induction p generalizing u with
  | nil =>
      have hux : u = x := by
        simpa [List.getLastD] using hlast
      simpa [r, cr₁, cr₂, hux] using hbaseX
  | cons z p ih =>
      have hp' : G.CLink u z ∧ G.CPath z p := by
        simpa [CPath] using hp
      have hlastTail : (z :: p).getLastD z = x := by
        simpa [List.getLastD] using hlast
      have hzPartition :
          G.DiskNPartition r cr₁ cr₂ z :=
        ih z hp'.2 hlastTail
      rcases hp'.1 with hnode | hface
      · exact G.diskNPartition_node_symm_step hnode hzPartition
      · exact G.diskNPartition_face_step_of_mem_partition
          hJ hPlain hr hproper hcr₁ hcr₂ hface
          hbaseX hbaseEdgeX hmem hzPartition

/-- Set-difference projection of `diskNPartition_chord_prefix`, matching the
statement of Coq `diskN_chord_ring`. -/
theorem diskN_chord_prefix
    [Fintype G.Dart]
    (hConn : G.Connected)
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {x y₁ y₂ u : G.Dart} {p₁ p₂ : List G.Dart}
    (hr : G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂))
    (hproper : G.ProperRing (y₂ :: p₁ ++ y₁ :: p₂))
    (hxDisk : G.DiskE (y₂ :: p₁ ++ y₁ :: p₂) x)
    (hy₁r : y₁ ∈ y₂ :: p₁ ++ y₁ :: p₂)
    (hy₂r : y₂ ∈ y₂ :: p₁ ++ y₁ :: p₂)
    (hcr₁ : G.SimpleRLinkCycle (x :: y₂ :: p₁))
    (hcr₂ : G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂)) :
    G.DiskN (x :: y₂ :: p₁) u ↔
      G.DiskN (y₂ :: p₁ ++ y₁ :: p₂) u ∧
        ¬ G.DiskN (G.edge x :: y₁ :: p₂) u :=
  (G.diskNPartition_chord_prefix
    hConn hJ hPlain hr hproper hxDisk hy₁r hy₂r hcr₁ hcr₂ u).left_iff

/-- Fixed-decomposition form of Coq `revsnip.v::diskF_chord_ring`, obtained
from the completed `DiskN` partition and the exact chord face-band union. -/
theorem diskF_chord_prefix
    [Fintype G.Dart]
    (hConn : G.Connected)
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {x y₁ y₂ u : G.Dart} {p₁ p₂ : List G.Dart}
    (hr : G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂))
    (hproper : G.ProperRing (y₂ :: p₁ ++ y₁ :: p₂))
    (hxDisk : G.DiskE (y₂ :: p₁ ++ y₁ :: p₂) x)
    (hy₁r : y₁ ∈ y₂ :: p₁ ++ y₁ :: p₂)
    (hy₂r : y₂ ∈ y₂ :: p₁ ++ y₁ :: p₂)
    (hy₁x : PermReachable G.face y₁ x)
    (hy₂ex : PermReachable G.face y₂ (G.edge x))
    (hcr₁ : G.SimpleRLinkCycle (x :: y₂ :: p₁))
    (hcr₂ : G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂)) :
    G.DiskF (x :: y₂ :: p₁) u ↔
      G.DiskF (y₂ :: p₁ ++ y₁ :: p₂) u ∧
        ¬ G.DiskF (G.edge x :: y₁ :: p₂) u :=
  G.diskF_chord_prefix_of_diskN_split hy₁x hy₂ex
    (fun v =>
      G.diskN_chord_prefix hConn hJ hPlain hr hproper hxDisk
        hy₁r hy₂r hcr₁ hcr₂ (u := v))

/-- Fixed-decomposition form of Coq
`revsnip.v::nontrivial_chord_ring`.  A nonempty complementary arc supplies a
strict outside witness for the first chord ring and also forces the ring-size
drop. -/
theorem nontrivialRing_zero_chord_prefix
    [Fintype G.Dart]
    (hConn : G.Connected)
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hr : G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂))
    (hproper : G.ProperRing (y₂ :: p₁ ++ y₁ :: p₂))
    (hxDisk : G.DiskE (y₂ :: p₁ ++ y₁ :: p₂) x)
    (hy₁r : y₁ ∈ y₂ :: p₁ ++ y₁ :: p₂)
    (hy₂r : y₂ ∈ y₂ :: p₁ ++ y₁ :: p₂)
    (hy₁x : PermReachable G.face y₁ x)
    (hcr₁ : G.SimpleRLinkCycle (x :: y₂ :: p₁))
    (hcr₂ : G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂))
    (hp₂ : p₂ ≠ [])
    (hInside : ∃ u : G.Dart, G.DiskF (x :: y₂ :: p₁) u) :
    G.NontrivialRing 0 (x :: y₂ :: p₁) ∧
      (x :: y₂ :: p₁).length <
        (y₂ :: p₁ ++ y₁ :: p₂).length := by
  cases p₂ with
  | nil =>
      exact False.elim (hp₂ rfl)
  | cons z q =>
      have hNodup :
          (y₂ :: p₁ ++ y₁ :: z :: q).Nodup :=
        FaceSimple.nodup (G := G) hr.2
      have hArcDisjoint :
          List.Disjoint (y₂ :: p₁) (y₁ :: z :: q) :=
        hNodup.disjoint
      have hzRight : z ∈ y₁ :: z :: q := by simp
      have hzR : z ∈ y₂ :: p₁ ++ y₁ :: z :: q :=
        List.mem_append_right (y₂ :: p₁) hzRight
      have hzN₂ :
          G.DiskN (G.edge x :: y₁ :: z :: q) z :=
        G.diskN_of_mem (by simp)
      have hzPartition :=
        G.diskNPartition_chord_prefix hConn hJ hPlain hr hproper
          hxDisk hy₁r hy₂r hcr₁ hcr₂ z
      have hzNotN₁ :
          ¬ G.DiskN (x :: y₂ :: p₁) z := by
        intro hzN₁
        exact hzPartition.2 ⟨hzN₁, hzN₂⟩
      have hy₁NeZ : y₁ ≠ z := by
        have hRightNodup : (y₁ :: z :: q).Nodup :=
          hNodup.of_append_right
        exact fun h =>
          (List.nodup_cons.mp hRightNodup).1 (by simp [h])
      have hzNotBand :
          ¬ G.FaceBand (x :: y₂ :: p₁) z := by
        intro hzBand
        rcases (FaceBand.cons (G := G)).1 hzBand with hxz | hleft
        · have hy₁z : PermReachable G.face y₁ z :=
            PermReachable.trans G.face hy₁x hxz
          exact hy₁NeZ
            (FaceSimple.eq_of_faceReachable_of_mem
              (G := G) hr.2 hy₁r hzR hy₁z)
        · rcases hleft with ⟨s, hsLeft, hsz⟩
          have hsR : s ∈ y₂ :: p₁ ++ y₁ :: z :: q :=
            List.mem_append_left (y₁ :: z :: q) hsLeft
          have hszEq : s = z :=
            FaceSimple.eq_of_faceReachable_of_mem
              (G := G) hr.2 hsR hzR hsz
          exact
            (List.disjoint_left.mp hArcDisjoint hsLeft)
              (by simp [hszEq])
      have hOutside :
          ∃ u : G.Dart, G.DiskFC (x :: y₂ :: p₁) u :=
        ⟨z, hzNotN₁, hzNotBand⟩
      have hNontrivial :
          G.NontrivialRing 0 (x :: y₂ :: p₁) :=
        (G.nontrivialRing_zero_iff).2 ⟨hInside, hOutside⟩
      have hLength :
          (x :: y₂ :: p₁).length <
            (y₂ :: p₁ ++ y₁ :: z :: q).length :=
        G.length_chord_prefix_lt_of_decomposition
          (r := y₂ :: p₁ ++ y₁ :: z :: q)
          (x := x) (y₁ := y₁) (y₂ := y₂)
          (p₁ := p₁) (p₂ := z :: q) (i := 0)
          (by simp) (by simp)
      exact ⟨hNontrivial, hLength⟩

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
