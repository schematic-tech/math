import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.FacialCycles

/-! Transport of cycle darts through graph inclusions. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

@[simp]
theorem walkMapLe_length
    {V : Type u} {G H : SimpleGraph V} {x y : V}
    (h : G ≤ H) (p : G.Walk x y) :
    (p.mapLe h).length = p.length := by
  change (p.map (.ofLE h)).length = p.length
  exact SimpleGraph.Walk.length_map (.ofLE h) p

@[simp]
theorem walkMapLe_getVert
    {V : Type u} {G H : SimpleGraph V} {x y : V}
    (h : G ≤ H) (p : G.Walk x y) (i : Nat) :
    (p.mapLe h).getVert i = p.getVert i := by
  change (p.map (.ofLE h)).getVert i = p.getVert i
  rw [SimpleGraph.Walk.getVert_map]
  rfl

/-- Include an oriented edge into a supergraph without changing its
endpoints. -/
def liftOrientedEdge
    {V : Type u} {G H : SimpleGraph V}
    (h : G ≤ H) (e : OrientedEdge G) :
    OrientedEdge H :=
  ⟨(e.tail, e.head), h e.adj⟩

@[simp]
theorem liftOrientedEdge_tail
    {V : Type u} {G H : SimpleGraph V}
    (h : G ≤ H) (e : OrientedEdge G) :
    (liftOrientedEdge h e).tail = e.tail :=
  rfl

@[simp]
theorem liftOrientedEdge_head
    {V : Type u} {G H : SimpleGraph V}
    (h : G ≤ H) (e : OrientedEdge G) :
    (liftOrientedEdge h e).head = e.head :=
  rfl

@[simp]
theorem liftOrientedEdge_symm
    {V : Type u} {G H : SimpleGraph V}
    (h : G ≤ H) (e : OrientedEdge G) :
    liftOrientedEdge h e.symm = (liftOrientedEdge h e).symm := by
  rfl

theorem liftOrientedEdge_injective
    {V : Type u} {G H : SimpleGraph V}
    (h : G ≤ H) :
    Function.Injective (liftOrientedEdge h) := by
  intro e f hef
  apply Subtype.ext
  exact congrArg (fun z : OrientedEdge H => z.1) hef

/-- Inclusion into a supergraph preserves the forward cycle orientation. -/
theorem cycleForwardDart_liftOrientedEdge_iff
    {V : Type u} {C G : SimpleGraph V} {u : V}
    (h : C ≤ G) (c : C.Walk u u) (e : OrientedEdge C) :
    CycleForwardDart (c.mapLe h) (liftOrientedEdge h e) ↔
      CycleForwardDart c e := by
  constructor <;> rintro ⟨i, hi, htail, hhead⟩
  · refine ⟨i, by simpa using hi, ?_, ?_⟩
    · simpa using htail
    · simpa using hhead
  · refine ⟨i, by simpa using hi, ?_, ?_⟩
    · simpa using htail
    · simpa using hhead

/-- A dart oriented along an included cycle is an edge of the original cycle
graph. -/
theorem common_adj_of_cycleForwardDart
    {V : Type u} {C G : SimpleGraph V} {u : V}
    (h : C ≤ G) {c : C.Walk u u} {e : OrientedEdge G}
    (he : CycleForwardDart (c.mapLe h) e) :
    C.Adj e.tail e.head := by
  rcases he with ⟨i, hi, htail, hhead⟩
  rw [htail, hhead]
  simpa using
    c.adj_getVert_succ (by
      simpa using hi)

theorem common_adj_of_cycleBackwardDart
    {V : Type u} {C G : SimpleGraph V} {u : V}
    (h : C ≤ G) {c : C.Walk u u} {e : OrientedEdge G}
    (he : CycleBackwardDart (c.mapLe h) e) :
    C.Adj e.tail e.head := by
  exact C.symm (common_adj_of_cycleForwardDart h he)

/-- Transfer a dart known to belong to a common graph into either summand. -/
def transferCommonDart
    {V : Type u} {G H C : SimpleGraph V}
    (hC : C ≤ H) (e : OrientedEdge G)
    (heC : C.Adj e.tail e.head) :
    OrientedEdge H :=
  liftOrientedEdge hC ⟨(e.tail, e.head), heC⟩

@[simp]
theorem transferCommonDart_tail
    {V : Type u} {G H C : SimpleGraph V}
    (hC : C ≤ H) (e : OrientedEdge G)
    (heC : C.Adj e.tail e.head) :
    (transferCommonDart hC e heC).tail = e.tail :=
  rfl

@[simp]
theorem transferCommonDart_head
    {V : Type u} {G H C : SimpleGraph V}
    (hC : C ≤ H) (e : OrientedEdge G)
    (heC : C.Adj e.tail e.head) :
    (transferCommonDart hC e heC).head = e.head :=
  rfl

@[simp]
theorem transferCommonDart_symm
    {V : Type u} {G H C : SimpleGraph V}
    (hC : C ≤ H) (e : OrientedEdge G)
    (heC : C.Adj e.tail e.head) :
    transferCommonDart hC e.symm (C.symm heC) =
      (transferCommonDart hC e heC).symm := by
  rfl

theorem transferCommonDart_injective
    {V : Type u} {G H C : SimpleGraph V}
    (hC : C ≤ H)
    {e f : OrientedEdge G}
    (heC : C.Adj e.tail e.head)
    (hfC : C.Adj f.tail f.head)
    (hef :
      transferCommonDart hC e heC =
        transferCommonDart hC f hfC) :
    e = f := by
  apply Subtype.ext
  exact congrArg (fun z : OrientedEdge H => z.1) hef

/-- Transfer of a common dart between two supergraphs preserves forward cycle
orientation. -/
theorem cycleForwardDart_transferCommonDart
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    {c : C.Walk u u} {e : OrientedEdge G₁}
    (he : CycleForwardDart (c.mapLe hC₁) e) :
    CycleForwardDart (c.mapLe hC₂)
      (transferCommonDart hC₂ e
        (common_adj_of_cycleForwardDart hC₁ he)) := by
  rcases he with ⟨i, hi, htail, hhead⟩
  refine ⟨i, by simpa using hi, ?_, ?_⟩
  · simpa using htail
  · simpa using hhead

theorem cycleBackwardDart_transferCommonDart
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    {c : C.Walk u u} {e : OrientedEdge G₁}
    (he : CycleBackwardDart (c.mapLe hC₁) e) :
    CycleBackwardDart (c.mapLe hC₂)
      (transferCommonDart hC₂ e
        (common_adj_of_cycleBackwardDart hC₁ he)) := by
  exact cycleForwardDart_transferCommonDart hC₁ hC₂ he

/-- Every common dart in a supergraph has one of the two cycle
orientations. -/
theorem cycleForward_or_backward_of_common
    {V : Type u} {G C : SimpleGraph V} {u : V}
    (hC : C ≤ G) {c : C.Walk u u}
    (hspan : c.toSubgraph.spanningCoe = C)
    (e : OrientedEdge G)
    (heC : C.Adj e.tail e.head) :
    CycleForwardDart (c.mapLe hC) e ∨
      CycleBackwardDart (c.mapLe hC) e := by
  let eC : OrientedEdge C := ⟨(e.tail, e.head), heC⟩
  have hlift : liftOrientedEdge hC eC = e := by
    apply Subtype.ext
    rfl
  rcases cycleForward_or_backward_of_spanning c hspan eC with
    hforward | hbackward
  · left
    rw [← hlift]
    exact (cycleForwardDart_liftOrientedEdge_iff hC c eC).mpr
      hforward
  · right
    rw [← hlift]
    exact (cycleForwardDart_liftOrientedEdge_iff hC c eC.symm).mpr
      hbackward


end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
