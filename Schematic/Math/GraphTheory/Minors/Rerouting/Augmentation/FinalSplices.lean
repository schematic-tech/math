import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.ChainBridges

/-! Final one- and two-path splice cases yielding a full linkage. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem PartialThreeVertexLinkage.hasPartial_two_of_one_path_adjacent_first_last_hits
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3} {l : List (VertexSplitState V)}
    {idxF idxL : Nat}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hidxL_eq : idxL = idxF + 1)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    {vHit wHit : V}
    (husedF : (l[idxF]'hidxF).vertex ∈ L.usedVertices)
    (husedL : (l[idxL]'hidxL).vertex ∈ L.usedVertices)
    (hfirst : forall j : Nat, j < idxF ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices)
    (hafter : forall j : Nat, idxL < j ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices)
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hstateL : l[idxL]'hidxL = VertexSplitState.out wHit) :
    HasPartialThreeVertexLinkage G left right 2 := by
  classical
  subst idxL
  have hvHit : vHit ∈ L.usedVertices := by
    simpa [hstateF] using husedF
  have hwHit : wHit ∈ L.usedVertices := by
    simpa [hstateL] using husedL
  have hv0 : vHit ∈ (L.path 0).support :=
    L.mem_path_zero_of_usedVertices_one hvHit
  obtain ⟨w, hstateW, _hw0, horderW⟩ :=
    L.first_used_splitResidualChain_backward_block
      hidxF hidxL (by omega) hstateF hchain hv0
  have hstateW' :
      l[idxF + 1]'hidxL = VertexSplitState.out w := by
    simpa using hstateW
  have hww : w = wHit := by
    have hEq : VertexSplitState.out w = VertexSplitState.out wHit :=
      hstateW'.symm.trans hstateL
    injection hEq
  have horder :
      (L.path 0).support.idxOf wHit <
        (L.path 0).support.idxOf vHit := by
    simpa [hww] using horderW
  obtain ⟨pIn, hpIn, hInAvoid⟩ :=
    L.exists_path_to_first_used_of_splitResidualChain
      hidxF hhead hstateF hchain hfirst
  have hvertexL : (l[idxF + 1]'hidxL).vertex = wHit := by
    simp [hstateL]
  obtain ⟨pOut, hpOut, hOutAvoid⟩ :=
    L.exists_path_from_last_used_to_target_of_splitResidualChain
      hidxL hvertexL hlast hchain hafter
  exact
    L.hasPartial_two_of_one_path_ordered_splice_or_direct
      hiNew hjNew hvHit hwHit horder pIn hpIn hInAvoid pOut hpOut
      hOutAvoid

theorem PartialThreeVertexLinkage.hasPartial_three_of_two_paths_adjacent_first_last_hits
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3} {l : List (VertexSplitState V)}
    {idxF idxL : Nat}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hidxL_eq : idxL = idxF + 1)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    {vHit wHit : V}
    (husedF : (l[idxF]'hidxF).vertex ∈ L.usedVertices)
    (hfirst : forall j : Nat, j < idxF ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices)
    (hafter : forall j : Nat, idxL < j ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices)
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hstateL : l[idxL]'hidxL = VertexSplitState.out wHit) :
    HasPartialThreeVertexLinkage G left right 3 := by
  classical
  subst idxL
  have hvHit : vHit ∈ L.usedVertices := by
    simpa [hstateF] using husedF
  obtain ⟨pIn, hpIn, hInAvoid⟩ :=
    L.exists_path_to_first_used_of_splitResidualChain
      hidxF hhead hstateF hchain hfirst
  have hvertexL : (l[idxF + 1]'hidxL).vertex = wHit := by
    simp [hstateL]
  obtain ⟨pOut, hpOut, hOutAvoid⟩ :=
    L.exists_path_from_last_used_to_target_of_splitResidualChain
      hidxL hvertexL hlast hchain hafter
  rcases L.mem_path_zero_or_one_of_usedVertices_two hvHit with hv0 | hv1
  · obtain ⟨w, hstateW, hw0, horderW⟩ :=
      L.first_used_splitResidualChain_backward_block
        hidxF hidxL (by omega) hstateF hchain hv0
    have hstateW' :
        l[idxF + 1]'hidxL = VertexSplitState.out w := by
      simpa using hstateW
    have hww : w = wHit := by
      have hEq : VertexSplitState.out w = VertexSplitState.out wHit :=
        hstateW'.symm.trans hstateL
      injection hEq
    have hw0' : wHit ∈ (L.path 0).support := by
      simpa [hww] using hw0
    have horder :
        (L.path 0).support.idxOf wHit <
          (L.path 0).support.idxOf vHit := by
      simpa [hww] using horderW
    exact
      L.hasPartial_three_of_first_path_ordered_splice_or_direct
        hiNew hjNew hv0 hw0' horder pIn hpIn hInAvoid pOut hpOut
        hOutAvoid
  · obtain ⟨w, hstateW, hw1, horderW⟩ :=
      L.first_used_splitResidualChain_backward_block
        hidxF hidxL (by omega) hstateF hchain hv1
    have hstateW' :
        l[idxF + 1]'hidxL = VertexSplitState.out w := by
      simpa using hstateW
    have hww : w = wHit := by
      have hEq : VertexSplitState.out w = VertexSplitState.out wHit :=
        hstateW'.symm.trans hstateL
      injection hEq
    have hw1' : wHit ∈ (L.path 1).support := by
      simpa [hww] using hw1
    have horder :
        (L.path 1).support.idxOf wHit <
          (L.path 1).support.idxOf vHit := by
      simpa [hww] using horderW
    exact
      L.hasPartial_three_of_second_path_ordered_splice_or_direct
        hiNew hjNew hv1 hw1' horder pIn hpIn hInAvoid pOut hpOut
        hOutAvoid

theorem PartialThreeVertexLinkage.hasPartial_two_of_one_path_first_last_ordered_or_adjacent
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3} {l : List (VertexSplitState V)}
    {idxF idxL : Nat}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    {vHit wHit : V}
    (husedF : (l[idxF]'hidxF).vertex ∈ L.usedVertices)
    (husedL : (l[idxL]'hidxL).vertex ∈ L.usedVertices)
    (hfirst : forall j : Nat, j < idxF ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices)
    (hafter : forall j : Nat, idxL < j ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices)
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hstateL : l[idxL]'hidxL = VertexSplitState.out wHit)
    (hcase :
      idxL = idxF + 1 ∨
        (L.path 0).support.idxOf wHit <
          (L.path 0).support.idxOf vHit) :
    HasPartialThreeVertexLinkage G left right 2 := by
  classical
  rcases hcase with hidxL_eq | horder
  · exact
      L.hasPartial_two_of_one_path_adjacent_first_last_hits
        hiNew hjNew hidxF hidxL hidxL_eq hhead hlast hchain husedF husedL
        hfirst hafter hstateF hstateL
  · have hvHit : vHit ∈ L.usedVertices := by
      simpa [hstateF] using husedF
    have hwHit : wHit ∈ L.usedVertices := by
      simpa [hstateL] using husedL
    obtain ⟨pIn, hpIn, hInAvoid⟩ :=
      L.exists_path_to_first_used_of_splitResidualChain
        hidxF hhead hstateF hchain hfirst
    have hvertexL : (l[idxL]'hidxL).vertex = wHit := by
      simp [hstateL]
    obtain ⟨pOut, hpOut, hOutAvoid⟩ :=
      L.exists_path_from_last_used_to_target_of_splitResidualChain
        hidxL hvertexL hlast hchain hafter
    exact
      L.hasPartial_two_of_one_path_ordered_splice_or_direct
        hiNew hjNew hvHit hwHit horder pIn hpIn hInAvoid pOut hpOut
        hOutAvoid

theorem PartialThreeVertexLinkage.hasPartial_three_of_two_paths_first_last_same_path_ordered_or_adjacent
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3} {l : List (VertexSplitState V)}
    {idxF idxL : Nat}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    {vHit wHit : V}
    (husedF : (l[idxF]'hidxF).vertex ∈ L.usedVertices)
    (hfirst : forall j : Nat, j < idxF ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices)
    (hafter : forall j : Nat, idxL < j ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices)
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hstateL : l[idxL]'hidxL = VertexSplitState.out wHit)
    (hcase :
      idxL = idxF + 1 ∨
        Exists fun k : Fin 2 =>
          vHit ∈ (L.path k).support ∧
            wHit ∈ (L.path k).support ∧
              (L.path k).support.idxOf wHit <
                (L.path k).support.idxOf vHit) :
    HasPartialThreeVertexLinkage G left right 3 := by
  classical
  rcases hcase with hidxL_eq | hordered
  · exact
      L.hasPartial_three_of_two_paths_adjacent_first_last_hits
        hiNew hjNew hidxF hidxL hidxL_eq hhead hlast hchain husedF hfirst
        hafter hstateF hstateL
  · rcases hordered with ⟨k, hvk, hwk, horder⟩
    obtain ⟨pIn, hpIn, hInAvoid⟩ :=
      L.exists_path_to_first_used_of_splitResidualChain
        hidxF hhead hstateF hchain hfirst
    have hvertexL : (l[idxL]'hidxL).vertex = wHit := by
      simp [hstateL]
    obtain ⟨pOut, hpOut, hOutAvoid⟩ :=
      L.exists_path_from_last_used_to_target_of_splitResidualChain
        hidxL hvertexL hlast hchain hafter
    fin_cases k
    · exact
        L.hasPartial_three_of_first_path_ordered_splice_or_direct
          hiNew hjNew hvk hwk horder pIn hpIn hInAvoid pOut hpOut
          hOutAvoid
    · exact
        L.hasPartial_three_of_second_path_ordered_splice_or_direct
          hiNew hjNew hvk hwk horder pIn hpIn hInAvoid pOut hpOut
          hOutAvoid

noncomputable def PartialThreeVertexLinkage.leftEquiv
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 3) :
    Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective L.leftIndex L.leftIndex_injective.bijective_of_finite

noncomputable def PartialThreeVertexLinkage.rightEquiv
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 3) :
    Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective L.rightIndex L.rightIndex_injective.bijective_of_finite

noncomputable def PartialThreeVertexLinkage.toThreeVertexLinkage
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 3) :
    ThreeVertexLinkage G left right where
  targetEquiv := L.leftEquiv.symm.trans L.rightEquiv
  path i := (L.path (L.leftEquiv.symm i)).copy (by
      change left (L.leftEquiv (L.leftEquiv.symm i)) = left i
      rw [Equiv.apply_symm_apply]) (by
      change right (L.rightEquiv (L.leftEquiv.symm i)) =
        right ((L.leftEquiv.symm.trans L.rightEquiv) i)
      rfl)
  isPath i := by
    simpa using L.isPath (L.leftEquiv.symm i)
  pairwise_vertex_disjoint := by
    intro i j hij
    simpa using
      L.pairwise_vertex_disjoint (L.leftEquiv.symm i)
        (L.leftEquiv.symm j) (by
          intro h
          exact hij (by simpa using congrArg L.leftEquiv h))

theorem PartialThreeVertexLinkage.hasThreeVertexLinkage
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 3) :
    HasThreeVertexLinkage G left right :=
  ⟨L.toThreeVertexLinkage⟩


end Schematic.Math.GraphTheory
