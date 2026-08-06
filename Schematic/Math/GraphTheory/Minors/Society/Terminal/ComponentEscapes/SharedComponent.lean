import Schematic.Math.GraphTheory.Minors.Society.Terminal.ComponentEscapes.LegCollapse
import Schematic.Math.GraphTheory.Minors.Society.Terminal.ComponentEscapes.EndpointEscapes
import Schematic.Math.GraphTheory.Minors.Society.Terminal.ComponentEscapes.ArcCrossings

/-!
Reduction of the common-endpoint branch to one outside component.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- In the source-clean no-hidden branch, ambient cross-freeness forces the
two old common ends into one component of `G - V(P)`.

All three side legs first collapse by the checked ordered-foot argument.  If
the common ends belonged to distinct components, the preceding normalized
splice theorem would produce the forbidden ambient cross.  The returned
paths retain their exact component support for the remaining common-component
tripod construction. -/
theorem left_side_tripod_common_endpoints_same_outsideComponent_of_no_hidden_contact
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    Exists fun C : (S.graph.induce P.outside).ConnectedComponent =>
      Exists fun hleftOutside : T.left ∈ P.outside =>
        (⟨T.left, hleftOutside⟩ : P.outside) ∈ C.supp ∧
          Exists fun a : V =>
            Exists fun qLeft : S.graph.Walk T.left a =>
              a ∈ P.leftBoundaryArc ∧ qLeft.IsPath ∧
                (forall z : V, z ∈ qLeft.support ->
                  z ∈ induceComponentSupport (G := S.graph) C) ∧
                  Exists fun hrightOutside : T.right ∈ P.outside =>
                    (⟨T.right, hrightOutside⟩ : P.outside) ∈ C.supp ∧
                      Exists fun b : V =>
                        Exists fun qRight : S.graph.Walk T.right b =>
                          b ∈ P.leftBoundaryArc ∧ qRight.IsPath ∧
                            forall z : V, z ∈ qRight.support ->
                              z ∈ induceComponentSupport (G := S.graph) C := by
  classical
  let hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hsource_clean hno_hidden
  have hall : forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  have hlegs_nil : forall r : Fin 3, (T.leg r).Nil :=
    left_side_tripod_all_legs_nil_of_source_clean_no_hidden_contact
      hno_cross hno_tripod P T hsource_clean hno_hidden
  rcases
      left_side_tripod_common_endpoint_component_escape_dichotomy_of_no_hidden_contact
        (S := S) hno_cross P T hno_hidden with
    ⟨hleftOutside, Cleft, hleftC, a, qLeft, ha, hqLeftPath,
      hqLeftComponent, hrightOutside, Cright, hrightC, b, qRight, hb,
      hqRightPath, hqRightComponent, _hcomponentDichotomy⟩
  by_cases hcomponents : Cleft = Cright
  · refine
      ⟨Cleft, hleftOutside, hleftC, a, qLeft, ha, hqLeftPath,
        hqLeftComponent, hrightOutside, ?_, b, qRight, hb,
        hqRightPath, ?_⟩
    · simpa [hcomponents] using hrightC
    · intro z hz
      simpa [hcomponents] using hqRightComponent z hz
  · exact False.elim
      (hno_cross
        (GMIX24SourceProof.Tripod.crossOfDistinctCommonEndpointComponents
          hno_cross P T (hall i) (hall k)
          (hlegs_nil i) (hlegs_nil k) hij_order hjk_order hpath_contacts
          Cleft hleftOutside hleftC qLeft ha hqLeftPath hqLeftComponent
          Cright hrightOutside hrightC qRight hb hqRightPath
          hqRightComponent hcomponents))

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
