import MagnitudeConjecture.Algebra.BiserialModule
import MagnitudeConjecture.Algebra.BiserialCoordinateThinLocal
import MagnitudeConjecture.Algebra.BiserialRadicalTop
import MagnitudeConjecture.Algebra.SocleModule
import MagnitudeConjecture.Algebra.BiserialRadicalTruncation
import MagnitudeConjecture.Algebra.BiserialRadicalSquareTruncation
import MagnitudeConjecture.Algebra.BiserialRadicalSquareZeroObstruction
import MagnitudeConjecture.Algebra.BiserialLocalSubmoduleLift
import MagnitudeConjecture.Algebra.BiserialSemisimpleSubmodule
import MagnitudeConjecture.Algebra.BiserialIndecomposableCriterion
import MagnitudeConjecture.Algebra.BiserialKernelObstruction
import MagnitudeConjecture.Algebra.BiserialQuotientBranchElementCalculation
import MagnitudeConjecture.Algebra.FiniteLengthSemisimple
import MagnitudeConjecture.Algebra.BiserialBranchPlacement
import MagnitudeConjecture.Algebra.RightModuleAlmostSplit
import MagnitudeConjecture.Algebra.RightModulePrimitiveIdempotent
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary

/-!
# Direct biserial induction from coordinate thinness

This file follows only the biserial part of Pogorzały--Skowroński,
Proposition 1.  Representation-finiteness and the Schurian conclusion of that
proposition are not part of the magnitude proof and are not formalized here.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} {ι : Type w}
variable [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- Induction statement for local modules strictly below a composition
length bound. -/
def LocalBiserialBelow (n : ℕ∞) : Prop :=
  ∀ W : FinitelyGeneratedCategory A,
    Module.length Aᵐᵒᵖ W < n →
      IsSimpleModule Aᵐᵒᵖ
        (W ⧸ Module.jacobson Aᵐᵒᵖ W) →
      IsBiserialModule Aᵐᵒᵖ W

/-- A local biserial induction hypothesis makes a smaller local module
uniserial as soon as its radical is again local. -/
theorem LocalBiserialBelow.uniserial_of_jacobson_simpleTop
    {n : ℕ∞} (H : LocalBiserialBelow (A := A) n)
    (W : FinitelyGeneratedCategory A)
    (hlength : Module.length Aᵐᵒᵖ W < n)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (W ⧸ Module.jacobson Aᵐᵒᵖ W))
    (hJacTop : IsSimpleModule Aᵐᵒᵖ
      ((Module.jacobson Aᵐᵒᵖ W) ⧸
        Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ W))) :
    IsUniserialModule Aᵐᵒᵖ W :=
  IsBiserialModule.uniserial_of_biserial_of_simple_top_of_jacobson
    htop (H W hlength htop) hJacTop

/-- For a nonsimple local module, quotienting by the nonzero socle gives a
strictly smaller local module, so the local biserial induction hypothesis
applies to it. -/
theorem LocalBiserialBelow.biserial_quotient_moduleSocle
    [IsArtinianRing Aᵐᵒᵖ]
    {n : ℕ∞} (H : LocalBiserialBelow (A := A) n)
    (L : FinitelyGeneratedCategory A)
    (hlength : Module.length Aᵐᵒᵖ L ≤ n)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (L ⧸ Module.jacobson Aᵐᵒᵖ L))
    (hnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L) :
    IsBiserialModule Aᵐᵒᵖ
      (quotientFGObj L (moduleSocle Aᵐᵒᵖ L)) := by
  let R := Aᵐᵒᵖ
  have hnotSimple : ¬ IsSimpleModule R L := by
    intro hsimple
    exact hnotuni (IsBiserialModule.uniserial_of_simple hsimple)
  have hsocleLe : moduleSocle R L ≤ Module.jacobson R L :=
    moduleSocle_le_jacobson_of_simpleTop_of_not_simple htop hnotSimple
  have hLnontrivial : Nontrivial L :=
    (IsUniserialModule.isIndecomposableModule_of_simpleTop htop).nontrivial
  letI : Nontrivial L := hLnontrivial
  have hsocleNe : moduleSocle R L ≠ ⊥ := moduleSocle_ne_bot
  apply H
  · exact (moduleSocle R L).length_quotient_lt hsocleNe |>.trans_le hlength
  · exact isSimpleModule_top_quotient_of_le_jacobson
      (moduleSocle R L) hsocleLe htop

/-- A coordinate-thin biserial local module with two disjoint simple
submodules becomes length three when quotienting by either simple makes it
uniserial.  The two simples are forced to be the two radical branches. -/
theorem jacobson_eq_sup_and_length_eq_three_of_biserial_of_disjoint_simple_quotients_uniserial
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (M : FinitelyGeneratedCategory A)
    (hMthin : IsCoordinateThin (k := k) e M)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hMbis : IsBiserialModule Aᵐᵒᵖ M)
    (I S : Submodule Aᵐᵒᵖ M)
    (hI : IsSimpleModule Aᵐᵒᵖ I)
    (hS : IsSimpleModule Aᵐᵒᵖ S)
    (hinf : I ⊓ S = ⊥)
    (hIquot : IsUniserialModule Aᵐᵒᵖ (M ⧸ I))
    (hSquot : IsUniserialModule Aᵐᵒᵖ (M ⧸ S)) :
    Module.jacobson Aᵐᵒᵖ M = I ⊔ S ∧
      Module.length Aᵐᵒᵖ M = 3 := by
  letI : Nontrivial I := hI.nontrivial
  letI : Nontrivial S := hS.nontrivial
  have hIne : I ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp inferInstance
  have hSne : S ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp inferInstance
  have hIneTop : I ≠ ⊤ := by
    intro hItop
    have hSleI : S ≤ I := hItop.symm ▸ le_top
    have hInfEq : I ⊓ S = S := inf_eq_right.mpr hSleI
    exact hSne (hInfEq.symm.trans hinf)
  have hSneTop : S ≠ ⊤ := by
    intro hStop
    have hIleS : I ≤ S := hStop.symm ▸ le_top
    have hInfEq : I ⊓ S = I := inf_eq_left.mpr hIleS
    exact hIne (hInfEq.symm.trans hinf)
  have hIjac : I ≤ Module.jacobson Aᵐᵒᵖ M :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hMtop hIneTop
  have hSjac : S ≤ Module.jacobson Aᵐᵒᵖ M :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hMtop hSneTop
  rcases hMbis with ⟨U, V, hUVsup, hUuni, hVuni, hUVsimpleZero⟩
  have hItop : IsSimpleModule Aᵐᵒᵖ
      (I ⧸ Module.jacobson Aᵐᵒᵖ I) :=
    (IsBiserialModule.uniserial_of_simple hI).top_isSimple
  have hStop : IsSimpleModule Aᵐᵒᵖ
      (S ⧸ Module.jacobson Aᵐᵒᵖ S) :=
    (IsBiserialModule.uniserial_of_simple hS).top_isSimple
  let jI : submoduleFGObj M I →ₗ[Aᵐᵒᵖ] M := {
    toFun := fun x ↦ x.1
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hjIrange : jI.range = I := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact i.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  let jS : submoduleFGObj M S →ₗ[Aᵐᵒᵖ] M := {
    toFun := fun x ↦ x.1
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hjSrange : jS.range = S := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hIplace : I ≤ U ∨ I ≤ V := by
    have h :=
      linearMap_range_le_left_or_le_right_of_coordinateThin_sup_of_simpleTop
        e hall M hMthin U V (submoduleFGObj M I) jI (by
          rw [hjIrange, hUVsup]
          exact hIjac) hItop
    simpa [hjIrange] using h
  have hSplace : S ≤ U ∨ S ≤ V := by
    have h :=
      linearMap_range_le_left_or_le_right_of_coordinateThin_sup_of_simpleTop
        e hall M hMthin U V (submoduleFGObj M S) jS (by
          rw [hjSrange, hUVsup]
          exact hSjac) hStop
    simpa [hjSrange] using h
  have sameBranchFalse (T : Submodule Aᵐᵒᵖ M)
      (hTuni : IsUniserialModule Aᵐᵒᵖ T)
      (hIT : I ≤ T) (hST : S ≤ T) : False := by
    have hIS : I = S :=
      hTuni.eq_of_simple_submodules_le hI hS hIT hST
    have hInfEq : I ⊓ S = I := by rw [hIS, inf_idem]
    exact hIne (hInfEq.symm.trans hinf)
  have closeBranches (U V : Submodule Aᵐᵒᵖ M)
      (hUuni : IsUniserialModule Aᵐᵒᵖ U)
      (hVuni : IsUniserialModule Aᵐᵒᵖ V)
      (hUVsimpleZero : IsSimpleOrZeroModule Aᵐᵒᵖ
        ↥(U ⊓ V : Submodule Aᵐᵒᵖ M))
      (hIU : I ≤ U) (hSV : S ≤ V) :
      U = I ∧ V = S := by
    have hUVinf : U ⊓ V = ⊥ := by
      rcases hUVsimpleZero with hzero | hsimple
      · exact Submodule.subsingleton_iff_eq_bot.mp hzero
      · by_contra hne
        have hIK : I = U ⊓ V :=
          hUuni.eq_of_simple_submodules_le hI hsimple hIU inf_le_left
        have hSK : S = U ⊓ V :=
          hVuni.eq_of_simple_submodules_le hS hsimple hSV inf_le_right
        have hIS : I = S := hIK.trans hSK.symm
        have hInfEq : I ⊓ S = I := by rw [hIS, inf_idem]
        exact hIne (hInfEq.symm.trans hinf)
    have hUVmap : U.map I.mkQ ≤ V.map I.mkQ := by
      rcases hIquot.total (U.map I.mkQ) (V.map I.mkQ) with hle | hle
      · exact hle
      · exfalso
        have hSleU : S ≤ U := by
          calc
            S ≤ (S.map I.mkQ).comap I.mkQ :=
              Submodule.le_comap_map (f := I.mkQ) (p := S)
            _ ≤ (V.map I.mkQ).comap I.mkQ :=
              Submodule.comap_mono (Submodule.map_mono hSV)
            _ ≤ (U.map I.mkQ).comap I.mkQ := Submodule.comap_mono hle
            _ = I ⊔ U := Submodule.comap_map_mkQ I U
            _ = U := sup_eq_right.mpr hIU
        exact sameBranchFalse U hUuni hIU hSleU
    have hUle : U ≤ I ⊔ V := by
      calc
        U ≤ (U.map I.mkQ).comap I.mkQ :=
          Submodule.le_comap_map (f := I.mkQ) (p := U)
        _ ≤ (V.map I.mkQ).comap I.mkQ := Submodule.comap_mono hUVmap
        _ = I ⊔ V := Submodule.comap_map_mkQ I V
    have hUeq : U = I := by
      calc
        U = (I ⊔ V) ⊓ U :=
          (inf_eq_right.mpr hUle).symm
        _ = I ⊔ V ⊓ U := sup_inf_assoc_of_le V hIU
        _ = I := by rw [inf_comm, hUVinf, sup_bot_eq]
    have hVUmap : V.map S.mkQ ≤ U.map S.mkQ := by
      rcases hSquot.total (V.map S.mkQ) (U.map S.mkQ) with hle | hle
      · exact hle
      · exfalso
        have hIleV : I ≤ V := by
          calc
            I ≤ (I.map S.mkQ).comap S.mkQ :=
              Submodule.le_comap_map (f := S.mkQ) (p := I)
            _ ≤ (U.map S.mkQ).comap S.mkQ :=
              Submodule.comap_mono (Submodule.map_mono hIU)
            _ ≤ (V.map S.mkQ).comap S.mkQ := Submodule.comap_mono hle
            _ = S ⊔ V := Submodule.comap_map_mkQ S V
            _ = V := sup_eq_right.mpr hSV
        exact sameBranchFalse V hVuni hIleV hSV
    have hVle : V ≤ S ⊔ U := by
      calc
        V ≤ (V.map S.mkQ).comap S.mkQ :=
          Submodule.le_comap_map (f := S.mkQ) (p := V)
        _ ≤ (U.map S.mkQ).comap S.mkQ := Submodule.comap_mono hVUmap
        _ = S ⊔ U := Submodule.comap_map_mkQ S U
    have hVeq : V = S := by
      calc
        V = (S ⊔ U) ⊓ V :=
          (inf_eq_right.mpr hVle).symm
        _ = S ⊔ U ⊓ V := sup_inf_assoc_of_le U hSV
        _ = S := by rw [hUVinf, sup_bot_eq]
    exact ⟨hUeq, hVeq⟩
  have hJ : Module.jacobson Aᵐᵒᵖ M = I ⊔ S := by
    rcases hIplace with hIU | hIV <;>
      rcases hSplace with hSU | hSV
    · exact (sameBranchFalse U hUuni hIU hSU).elim
    · obtain ⟨hU, hV⟩ :=
        closeBranches U V hUuni hVuni hUVsimpleZero hIU hSV
      rw [← hU, ← hV, hUVsup]
    · have hVUsimpleZero : IsSimpleOrZeroModule Aᵐᵒᵖ
          ↥(V ⊓ U : Submodule Aᵐᵒᵖ M) := by
        rw [inf_comm]
        exact hUVsimpleZero
      obtain ⟨hV, hU⟩ :=
        closeBranches V U hVuni hUuni hVUsimpleZero hIV hSU
      rw [← hV, ← hU, sup_comm, hUVsup]
    · exact (sameBranchFalse V hVuni hIV hSV).elim
  have hJlength : Module.length Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ M) = 2 := by
    rw [hJ]
    exact length_sup_eq_two_of_disjoint_simple I S hinf hI hS
  have htopLength : Module.length Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M) = 1 :=
    Module.length_eq_one_iff.mpr hMtop
  have hexact : Module.length Aᵐᵒᵖ M =
      Module.length Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ M) +
        Module.length Aᵐᵒᵖ (M ⧸ Module.jacobson Aᵐᵒᵖ M) :=
    Module.length_eq_add_of_exact
      (Module.jacobson Aᵐᵒᵖ M).subtype (Module.jacobson Aᵐᵒᵖ M).mkQ
      (Module.jacobson Aᵐᵒᵖ M).subtype_injective
      (Module.jacobson Aᵐᵒᵖ M).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (Module.jacobson Aᵐᵒᵖ M))
  have hMlength : Module.length Aᵐᵒᵖ M = 3 := by
    rw [hJlength, htopLength] at hexact
    norm_num at hexact ⊢
    exact hexact
  exact ⟨hJ, hMlength⟩

/-- If the radical of a coordinate-thin local module is the sum of two
uniserial branches containing the same simple submodule, that submodule is
the whole ambient socle. -/
theorem moduleSocle_eq_shared_simple_of_coordinateThin_uniserial_branches
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (X : FinitelyGeneratedCategory A)
    (hXthin : IsCoordinateThin (k := k) e X)
    (hXtop : IsSimpleModule Aᵐᵒᵖ
      (X ⧸ Module.jacobson Aᵐᵒᵖ X))
    (U V I : Submodule Aᵐᵒᵖ X)
    (hUV : U ⊔ V = Module.jacobson Aᵐᵒᵖ X)
    (hUuni : IsUniserialModule Aᵐᵒᵖ U)
    (hVuni : IsUniserialModule Aᵐᵒᵖ V)
    (hIsimple : IsSimpleModule Aᵐᵒᵖ I)
    (hIU : I ≤ U) (hIV : I ≤ V) :
    moduleSocle Aᵐᵒᵖ X = I := by
  have hIne : I ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hIsimple.nontrivial
  have hIleJ : I ≤ Module.jacobson Aᵐᵒᵖ X := by
    rw [← hUV]
    exact hIU.trans le_sup_left
  have hXnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ X := by
    intro hXsimple
    letI : IsSimpleModule Aᵐᵒᵖ X := hXsimple
    have hJbot : Module.jacobson Aᵐᵒᵖ X = ⊥ :=
      IsSemisimpleModule.jacobson_eq_bot Aᵐᵒᵖ X
    apply hIne
    apply le_antisymm
    · rw [← hJbot]
      exact hIleJ
    · exact bot_le
  have hsocleJ : moduleSocle Aᵐᵒᵖ X ≤
      Module.jacobson Aᵐᵒᵖ X :=
    moduleSocle_le_jacobson_of_simpleTop_of_not_simple
      hXtop hXnotSimple
  apply le_antisymm
  · unfold moduleSocle
    apply sSup_le
    intro P hPsimple
    letI : IsSimpleModule Aᵐᵒᵖ P := hPsimple
    letI : Nontrivial P := hPsimple.nontrivial
    have hPleJ : P ≤ Module.jacobson Aᵐᵒᵖ X :=
      (le_moduleSocle_of_simple P hPsimple).trans hsocleJ
    let jP : submoduleFGObj X P →ₗ[Aᵐᵒᵖ] X := P.subtype
    have hjPrange : jP.range = P := Submodule.range_subtype P
    have hPtop : IsSimpleModule Aᵐᵒᵖ
        (P ⧸ Module.jacobson Aᵐᵒᵖ P) :=
      (IsBiserialModule.uniserial_of_simple hPsimple).top_isSimple
    have hplace : P ≤ U ∨ P ≤ V := by
      have h :=
        linearMap_range_le_left_or_le_right_of_coordinateThin_sup_of_simpleTop
          e hall X hXthin U V (submoduleFGObj X P) jP (by
            rw [hjPrange, hUV]
            exact hPleJ) hPtop
      simpa [hjPrange] using h
    rcases hplace with hPU | hPV
    · rw [hUuni.eq_of_simple_submodules_le
        hPsimple hIsimple hPU hIU]
    · rw [hVuni.eq_of_simple_submodules_le
        hPsimple hIsimple hPV hIV]
  · exact le_moduleSocle_of_simple I hIsimple

/-- Under coordinate thinness, the two complementary simple summands in the
top of the radical of a nonuniserial local biserial module are nonisomorphic.
Otherwise that radical layer itself is a repeated self-subquotient of the
original module. -/
theorem exists_nonisomorphic_complementary_simple_top_jacobson
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (M : FinitelyGeneratedCategory A)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hbis : IsBiserialModule Aᵐᵒᵖ M)
    (hnotuni : ¬ IsUniserialModule Aᵐᵒᵖ M) :
    ∃ S T : Submodule Aᵐᵒᵖ
        (Module.jacobson Aᵐᵒᵖ M ⧸
          Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ M)),
      IsSimpleModule Aᵐᵒᵖ S ∧
        IsSimpleModule Aᵐᵒᵖ T ∧ IsCompl S T ∧
        ¬ Nonempty (S ≃ₗ[Aᵐᵒᵖ] T) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  obtain ⟨S, T, hSsimple, hTsimple, hcompl⟩ :=
    exists_complementary_simple_top_jacobson_of_biserial_of_not_uniserial
      htop hbis hnotuni
  refine ⟨S, T, hSsimple, hTsimple, hcompl, ?_⟩
  rintro ⟨hST⟩
  let J : Submodule Aᵐᵒᵖ M := Module.jacobson Aᵐᵒᵖ M
  let Q : Submodule Aᵐᵒᵖ (submoduleFGObj M J) :=
    Module.jacobson Aᵐᵒᵖ J
  let TopJ := quotientFGObj (submoduleFGObj M J) Q
  let F := submoduleFGObj TopJ S
  have hFnontrivial : Nontrivial F := hSsimple.nontrivial
  letI : Nontrivial F := hFnontrivial
  let eProd : TopJ ≃ₗ[Aᵐᵒᵖ] (F × F) :=
    (S.prodEquivOfIsCompl T hcompl).symm.trans
      (LinearEquiv.prodCongr (LinearEquiv.refl Aᵐᵒᵖ S) hST.symm)
  have hRepeated : HasRepeatedSelfSubquotient M := by
    refine ⟨F, inferInstance, J, Q, ?_⟩
    exact ⟨
      QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
        Aᵐᵒᵖ eProd⟩
  exact no_repeatedSelfSubquotient_of_simpleTop_of_all_coordinateThin
    (k := k) e hall H M htop hRepeated

/-- A finitely generated module with simple socle is one of the
indecomposables controlled by the all-coordinate-thin premise. -/
theorem coordinateThin_of_simpleSocle
    (e : ι → A)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (W : FinitelyGeneratedCategory A)
    (hsocle : IsSimpleModule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ W)) :
    IsCoordinateThin (k := k) e W := by
  have hfiniteLength : IsFiniteLength Aᵐᵒᵖ W :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) W
  letI : IsArtinian Aᵐᵒᵖ W :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  have hindModule :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ W :=
    isIndecomposableModule_of_simpleSocle hsocle
  exact H W
    ((FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) W).mp hindModule)

/-- Under a complete coordinate family, a simple-socle module cannot
contain a repeated self-subquotient.  This is the dual induction endpoint
used in the indecomposability arguments of the direct biserial proof. -/
theorem no_repeatedSelfSubquotient_of_simpleSocle_of_all_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (W : FinitelyGeneratedCategory A)
    (hsocle : IsSimpleModule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ W)) :
    ¬ HasRepeatedSelfSubquotient W := by
  have hfiniteLength : IsFiniteLength Aᵐᵒᵖ W :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) W
  letI : IsArtinian Aᵐᵒᵖ W :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  have hindModule :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ W :=
    isIndecomposableModule_of_simpleSocle hsocle
  have hind : Indecomposable W :=
    (FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) W).mp hindModule
  exact no_repeatedSelfSubquotient_of_all_coordinateThin
    (k := k) e hall H W hind

include k in
/-- A fiber kernel with two nonisomorphic simple coordinate socles is
indecomposable if every submodule escaping the product of the branch
radicals contains a vector with two nonzero socle coordinates.  In a
hypothetical direct sum, the two coordinate socles must split between the
summands, while the summand carrying the common top contains such a mixed
vector. -/
theorem fiberKernel_indec_of_mixed_outside_radicalPreimage
    (Y Z T : FinitelyGeneratedCategory A) [Nontrivial T]
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hYsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hSocleNoniso : ¬ Nonempty
      (moduleSocle Aᵐᵒᵖ Y ≃ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    (hYrad : Module.jacobson Aᵐᵒᵖ Y ≤ f.ker)
    (hmixed : ∀ P : Submodule Aᵐᵒᵖ
        (fiberKernelFGObj Y Z T f g),
      ¬ P ≤ fiberKernelRadicalPreimage Y Z T f g →
        HasMixedSocleCoordinates Y Z T f g P) :
    Indecomposable (fiberKernelFGObj Y Z T f g) := by
  let W := fiberKernelFGObj Y Z T f g
  let J : Submodule Aᵐᵒᵖ W :=
    fiberKernelRadicalPreimage Y Z T f g
  have hJ : J ≠ ⊤ :=
    fiberKernelRadicalPreimage_ne_top Y Z T f g hf hg hYrad
  have hfiniteLength : IsFiniteLength Aᵐᵒᵖ W :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) W
  letI : IsArtinian Aᵐᵒᵖ W :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  have hWnontrivial : Nontrivial W := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hW
    apply hJ
    exact Subsingleton.elim _ _
  letI : Nontrivial W := hWnontrivial
  have hWsocleLength : Module.length Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ W) = 2 :=
    length_moduleSocle_fiberKernel_eq_two
      Y Z T f g hYsocle hZsocle hYkill hZkill
  have hindModule :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ W := by
    apply
      QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl
    intro P Q hPQ
    by_cases hP : P = ⊥
    · exact Or.inl hP
    by_cases hQ : Q = ⊥
    · exact Or.inr hQ
    exfalso
    obtain ⟨hPsocle, hQsocle⟩ :=
      simple_moduleSocles_of_isCompl_of_length_eq_two
        P Q hPQ hP hQ hWsocleLength
    have houtside : ¬ P ≤ J ∨ ¬ Q ≤ J := by
      by_contra h
      simp only [not_or, not_not] at h
      apply hJ
      apply top_unique
      rw [← hPQ.sup_eq_top]
      exact sup_le h.1 h.2
    have contradiction_of_mixed
        (U V : Submodule Aᵐᵒᵖ W) (hUV : IsCompl U V)
        (hV : V ≠ ⊥)
        (hUsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ U))
        (hUJ : ¬ U ≤ J) : False := by
      have hsocleU : moduleSocle Aᵐᵒᵖ W ≤ U :=
        moduleSocle_fiberKernel_le_of_hasMixed_of_nonisomorphic
          Y Z T f g hYsocle hZsocle hSocleNoniso hYkill hZkill
            U hUsocle (hmixed U hUJ)
      letI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
      obtain ⟨S, hSsimple, -⟩ :=
        exists_simple_submodule_le
          (R := Aᵐᵒᵖ) (M := V) (⊤ : Submodule Aᵐᵒᵖ V) top_ne_bot
      let Sbar : Submodule Aᵐᵒᵖ W := S.map V.subtype
      have hSbarSimple : IsSimpleModule Aᵐᵒᵖ Sbar :=
        IsBiserialModule.simple_map_of_injective
          V.subtype V.subtype_injective S hSsimple
      have hSbarSocle : Sbar ≤ moduleSocle Aᵐᵒᵖ W :=
        le_moduleSocle_of_simple Sbar hSbarSimple
      have hSbarV : Sbar ≤ V := Submodule.map_subtype_le V S
      have hSbarBot : Sbar ≤ ⊥ := by
        rw [← hUV.inf_eq_bot]
        exact le_inf (hSbarSocle.trans hsocleU) hSbarV
      exact (isSimpleModule_iff_isAtom.mp hSbarSimple).ne_bot
        (bot_unique hSbarBot)
    rcases houtside with hPJ | hQJ
    · exact contradiction_of_mixed P Q hPQ hQ hPsocle hPJ
    · exact contradiction_of_mixed Q P hPQ.symm hP hQsocle hQJ
  exact
    (FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) W).mp hindModule

/-- If the ambient next socle layer is two copies of one simple module, a
complement with no repeated self-subquotient can contribute at most one copy.
Indeed, a length-two contribution leaves the other complement with zero next
socle, so the product decomposition identifies that contribution with the
whole homogeneous ambient layer. -/
theorem nextSocle_length_le_one_of_isCompl_of_homogeneous
    (W F : FinitelyGeneratedCategory A) [Nontrivial F]
    (P Q : Submodule Aᵐᵒᵖ W) (hPQ : IsCompl P Q)
    (hFsimple : IsSimpleModule Aᵐᵒᵖ F)
    (hhomogeneous : moduleSocle Aᵐᵒᵖ
      (W ⧸ moduleSocle Aᵐᵒᵖ W) ≃ₗ[Aᵐᵒᵖ] (F × F))
    (hnoRepeated : ¬ HasRepeatedSelfSubquotient (submoduleFGObj W P)) :
    Module.length Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ (P ⧸ moduleSocle Aᵐᵒᵖ P)) ≤ 1 := by
  let pNext := Module.length Aᵐᵒᵖ
    (moduleSocle Aᵐᵒᵖ (P ⧸ moduleSocle Aᵐᵒᵖ P))
  let qNext := Module.length Aᵐᵒᵖ
    (moduleSocle Aᵐᵒᵖ (Q ⧸ moduleSocle Aᵐᵒᵖ Q))
  have hFlength : Module.length Aᵐᵒᵖ F = 1 :=
    Module.length_eq_one_iff.mpr hFsimple
  have hnextLength : Module.length Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ (W ⧸ moduleSocle Aᵐᵒᵖ W)) = 2 := by
    calc
      Module.length Aᵐᵒᵖ
          (moduleSocle Aᵐᵒᵖ (W ⧸ moduleSocle Aᵐᵒᵖ W)) =
          Module.length Aᵐᵒᵖ (F × F) := hhomogeneous.length_eq
      _ = Module.length Aᵐᵒᵖ F + Module.length Aᵐᵒᵖ F :=
        Module.length_prod Aᵐᵒᵖ F F
      _ = 2 := by rw [hFlength]; norm_num
  have hsum : pNext + qNext = 2 := by
    rw [← length_quotientModuleSocleLayer_eq_add_of_isCompl P Q hPQ]
    exact hnextLength
  by_contra hp
  have hpLeTwo : pNext ≤ 2 := by
    calc
      pNext ≤ pNext + qNext := self_le_add_right pNext qNext
      _ = 2 := hsum
  have hpEqTwo : pNext = 2 := by
    apply le_antisymm hpLeTwo
    have hpLt : 1 < pNext := lt_of_not_ge hp
    show (1 : ℕ∞) + 1 ≤ pNext
    exact Order.add_one_le_of_lt hpLt
  have hqEqZero : qNext = 0 := by
    apply WithTop.add_left_cancel (by norm_num : (2 : ℕ∞) ≠ ⊤)
    calc
      2 + qNext = 2 := by simpa [hpEqTwo] using hsum
      _ = 2 + 0 := by norm_num
  let Qnext := moduleSocle Aᵐᵒᵖ (Q ⧸ moduleSocle Aᵐᵒᵖ Q)
  letI : Unique Qnext := by
    have hsub : Subsingleton Qnext :=
      Module.length_eq_zero_iff.mp hqEqZero
    exact ⟨⟨0⟩, fun x ↦ hsub.elim x 0⟩
  let eP : moduleSocle Aᵐᵒᵖ (P ⧸ moduleSocle Aᵐᵒᵖ P) ≃ₗ[Aᵐᵒᵖ]
      moduleSocle Aᵐᵒᵖ (W ⧸ moduleSocle Aᵐᵒᵖ W) :=
    (LinearEquiv.prodUnique
      (R := Aᵐᵒᵖ)
      (M := moduleSocle Aᵐᵒᵖ (P ⧸ moduleSocle Aᵐᵒᵖ P))
      (M₂ := Qnext)).symm.trans
        (quotientModuleSocleLayerProdLinearEquivOfIsCompl P Q hPQ)
  let ePF : moduleSocle Aᵐᵒᵖ (P ⧸ moduleSocle Aᵐᵒᵖ P) ≃ₗ[Aᵐᵒᵖ]
      (F × F) := eP.trans hhomogeneous
  apply hnoRepeated
  exact hasRepeatedSelfSubquotient_of_quotient_submodule_prod_self
    (submoduleFGObj W P) F
    (moduleSocle Aᵐᵒᵖ P)
    (moduleSocle Aᵐᵒᵖ (P ⧸ moduleSocle Aᵐᵒᵖ P)) ePF

include k in
/-- The source-shaped indecomposability package for the fiber kernels in
the direct proof.  The standard branch-radical preimage is proper, the two
successive socle layers force hypothetical complements to be uniserial, and
`hcomplementCapture` is precisely the paper's calculation for the uniserial
complement escaping the ambient radical.
-/
theorem fiberKernel_indec_of_two_socle_layers_of_complement_capture
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (Y Z T F : FinitelyGeneratedCategory A) [Nontrivial T] [Nontrivial F]
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hYlength : Module.length Aᵐᵒᵖ Y = 3)
    (hZlength : Module.length Aᵐᵒᵖ Z = 3)
    (hTlength : Module.length Aᵐᵒᵖ T = 1)
    (hYsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    (hFsimple : IsSimpleModule Aᵐᵒᵖ F)
    (eYnext : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)) ≃ₗ[Aᵐᵒᵖ] F)
    (eZnext : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) ≃ₗ[Aᵐᵒᵖ] F)
    (hcomplementCapture : ∀ P : Submodule Aᵐᵒᵖ
        (fiberKernelFGObj Y Z T f g),
      P ≠ ⊥ → IsUniserialModule Aᵐᵒᵖ P →
        ¬ P ≤ fiberKernelRadicalPreimage Y Z T f g →
          moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) ≤ P) :
    Indecomposable (fiberKernelFGObj Y Z T f g) := by
  let W := fiberKernelFGObj Y Z T f g
  let J : Submodule Aᵐᵒᵖ W :=
    fiberKernelRadicalPreimage Y Z T f g
  have hTsimple : IsSimpleModule Aᵐᵒᵖ T :=
    Module.length_eq_one_iff.mp hTlength
  letI : IsSimpleModule Aᵐᵒᵖ T := hTsimple
  have hYrad : Module.jacobson Aᵐᵒᵖ Y ≤ f.ker :=
    IsSemisimpleModule.jacobson_le_ker Aᵐᵒᵖ Aᵐᵒᵖ Y T f
  have hJ : J ≠ ⊤ :=
    fiberKernelRadicalPreimage_ne_top Y Z T f g hf hg hYrad
  have hfiniteLength : IsFiniteLength Aᵐᵒᵖ W :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) W
  letI : IsArtinian Aᵐᵒᵖ W :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  have hWnontrivial : Nontrivial W := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hW
    apply hJ
    exact Subsingleton.elim _ _
  letI : Nontrivial W := hWnontrivial
  have hWlength : Module.length Aᵐᵒᵖ W = 5 :=
    length_fiberKernel_eq_five
      Y Z T f g hf hYlength hZlength hTlength
  have hWsocleLength : Module.length Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ W) = 2 :=
    length_moduleSocle_fiberKernel_eq_two
      Y Z T f g hYsocle hZsocle hYkill hZkill
  let hnextHomogeneous : moduleSocle Aᵐᵒᵖ
      (W ⧸ moduleSocle Aᵐᵒᵖ W) ≃ₗ[Aᵐᵒᵖ] (F × F) :=
    fiberKernelNextSocleLinearEquivOfLengthThree
      (k := k) Y Z T F f g hf hg hYlength hZlength hTlength
        hYsocle hZsocle hYkill hZkill hFsimple eYnext eZnext
  have hFlength : Module.length Aᵐᵒᵖ F = 1 :=
    Module.length_eq_one_iff.mpr hFsimple
  have hnextLength : Module.length Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ (W ⧸ moduleSocle Aᵐᵒᵖ W)) = 2 := by
    calc
      Module.length Aᵐᵒᵖ
          (moduleSocle Aᵐᵒᵖ (W ⧸ moduleSocle Aᵐᵒᵖ W)) =
          Module.length Aᵐᵒᵖ (F × F) := hnextHomogeneous.length_eq
      _ = Module.length Aᵐᵒᵖ F + Module.length Aᵐᵒᵖ F :=
        Module.length_prod Aᵐᵒᵖ F F
      _ = 2 := by rw [hFlength]; norm_num
  have hcomplements : ∀ P Q : Submodule Aᵐᵒᵖ W,
      IsCompl P Q → P ≠ ⊥ → Q ≠ ⊥ →
        IsUniserialModule Aᵐᵒᵖ P ∧ IsUniserialModule Aᵐᵒᵖ Q :=
    fun P Q hPQ hP hQ ↦ by
      obtain ⟨hPsocle, hQsocle⟩ :=
        simple_moduleSocles_of_isCompl_of_length_eq_two
          P Q hPQ hP hQ hWsocleLength
      have hPnoRepeated :
          ¬ HasRepeatedSelfSubquotient (submoduleFGObj W P) :=
        no_repeatedSelfSubquotient_of_simpleSocle_of_all_coordinateThin
          (k := k) e hall H (submoduleFGObj W P) hPsocle
      have hQnoRepeated :
          ¬ HasRepeatedSelfSubquotient (submoduleFGObj W Q) :=
        no_repeatedSelfSubquotient_of_simpleSocle_of_all_coordinateThin
          (k := k) e hall H (submoduleFGObj W Q) hQsocle
      have hPnextBound :=
        nextSocle_length_le_one_of_isCompl_of_homogeneous
          W F P Q hPQ hFsimple hnextHomogeneous hPnoRepeated
      have hQnextBound :=
        nextSocle_length_le_one_of_isCompl_of_homogeneous
          W F Q P hPQ.symm hFsimple hnextHomogeneous hQnoRepeated
      exact
      complement_uniserial_of_length_five_of_two_socle_layers
        hWlength hWsocleLength hnextLength P Q hPQ hP hQ
          hPnextBound hQnextBound
  have hindModule :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ W :=
    isIndecomposableModule_of_complement_uniserial_of_capture_socle
      J hJ hcomplements hcomplementCapture
  exact
    (FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) W).mp hindModule

/-- Complete coordinate thinness contradicts a fiber kernel satisfying the
source's two-socle-layer, element-capture, and equal-branch data.  This
assembles the first and last kernel contradictions of Proposition 1. -/
theorem false_of_fiberKernel_induction_obstruction
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (Y Z T F : FinitelyGeneratedCategory A) [Nontrivial T] [Nontrivial F]
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hYlength : Module.length Aᵐᵒᵖ Y = 3)
    (hZlength : Module.length Aᵐᵒᵖ Z = 3)
    (hTlength : Module.length Aᵐᵒᵖ T = 1)
    (hYsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    (hFsimple : IsSimpleModule Aᵐᵒᵖ F)
    (eYnext : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)) ≃ₗ[Aᵐᵒᵖ] F)
    (eZnext : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) ≃ₗ[Aᵐᵒᵖ] F)
    (hcomplementCapture : ∀ P : Submodule Aᵐᵒᵖ
        (fiberKernelFGObj Y Z T f g),
      P ≠ ⊥ → IsUniserialModule Aᵐᵒᵖ P →
        ¬ P ≤ fiberKernelRadicalPreimage Y Z T f g →
          moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) ≤ P) :
    False := by
  let W := fiberKernelFGObj Y Z T f g
  let hnextHomogeneous : moduleSocle Aᵐᵒᵖ
      (W ⧸ moduleSocle Aᵐᵒᵖ W) ≃ₗ[Aᵐᵒᵖ] (F × F) :=
    fiberKernelNextSocleLinearEquivOfLengthThree
      (k := k) Y Z T F f g hf hg hYlength hZlength hTlength
        hYsocle hZsocle hYkill hZkill hFsimple eYnext eZnext
  have hRepeated : HasRepeatedSelfSubquotient W :=
    hasRepeatedSelfSubquotient_of_quotient_submodule_prod_self
      W F (moduleSocle Aᵐᵒᵖ W)
        (moduleSocle Aᵐᵒᵖ (W ⧸ moduleSocle Aᵐᵒᵖ W))
          hnextHomogeneous
  have hind : Indecomposable W :=
    fiberKernel_indec_of_two_socle_layers_of_complement_capture
      (k := k) e hall H Y Z T F f g hf hg hYlength hZlength
        hTlength hYsocle hZsocle hYkill hZkill hFsimple
        eYnext eZnext hcomplementCapture
  exact no_repeatedSelfSubquotient_of_all_coordinateThin
    (k := k) e hall H W hind hRepeated

/-- The first source obstruction with its literal quotient branches.  Two
disjoint simple layers `S,T ⊆ X` give `Y=X/S` and `Z=X/T`; their common
next socle is constructed through the third isomorphism theorem, and their
maps to the simple top of `X` are the canonical nested-quotient maps.  The
second radical layer `S ⊕ T` and vanishing third radical layer now drive
the source's element calculation internally, so no complement-capture
hypothesis remains. -/
theorem false_of_quotientBranch_fiberKernel_induction_obstruction
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (X : FinitelyGeneratedCategory A)
    (S T : Submodule Aᵐᵒᵖ X)
    (hinf : S ⊓ T = ⊥)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hSTnoniso : ¬ Nonempty (S ≃ₗ[Aᵐᵒᵖ] T))
    (hXlength : Module.length Aᵐᵒᵖ X = 4)
    (hXtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj X (Module.jacobson Aᵐᵒᵖ X)))
    (hradicalSquare : Ring.jacobson Aᵐᵒᵖ ^ 2 •
      (⊤ : Submodule Aᵐᵒᵖ X) = S ⊔ T)
    (hradicalCube : Ring.jacobson Aᵐᵒᵖ ^ 3 •
      (⊤ : Submodule Aᵐᵒᵖ X) = ⊥)
    (hYuniserial : IsUniserialModule Aᵐᵒᵖ (quotientFGObj X S))
    (hZuniserial : IsUniserialModule Aᵐᵒᵖ (quotientFGObj X T)) :
    False := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := S ⊔ T
  let J := Module.jacobson Aᵐᵒᵖ X
  have hSTJ : S ⊔ T ≤ J := by
    rw [← hradicalSquare]
    change Ring.jacobson Aᵐᵒᵖ ^ 2 •
      (⊤ : Submodule Aᵐᵒᵖ X) ≤ Module.jacobson Aᵐᵒᵖ X
    rw [
      moduleJacobson_eq_ringJacobson_smul_top (R := Aᵐᵒᵖ) (M := X)]
    exact Submodule.smul_mono_left
      (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0))
  let Y := quotientFGObj X S
  let Z := quotientFGObj X T
  let Top := quotientFGObj X J
  let F := quotientBranchCommonNextSocleFGObj X R
  let f := quotientFGMapQ X S J (le_sup_left.trans hSTJ)
  let g := quotientFGMapQ X T J (le_sup_right.trans hSTJ)
  have hYlength : Module.length Aᵐᵒᵖ Y = 3 :=
    length_quotient_eq_three_of_length_eq_four_of_simple
      S hXlength hSsimple
  have hZlength : Module.length Aᵐᵒᵖ Z = 3 :=
    length_quotient_eq_three_of_length_eq_four_of_simple
      T hXlength hTsimple
  have hTopLength : Module.length Aᵐᵒᵖ Top = 1 :=
    Module.length_eq_one_iff.mpr hXtop
  letI : IsSimpleModule Aᵐᵒᵖ Top := hXtop
  letI : Nontrivial Top := hXtop.nontrivial
  have hYsocleEq : moduleSocle Aᵐᵒᵖ Y = R.map S.mkQ :=
    moduleSocle_quotient_eq_sup_map X S T hinf hTsimple hYuniserial
  have hZsocleEq : moduleSocle Aᵐᵒᵖ Z = R.map T.mkQ := by
    have hz := moduleSocle_quotient_eq_sup_map X T S
      (by simpa [inf_comm] using hinf) hSsimple hZuniserial
    simpa [R, sup_comm] using hz
  have hYsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y) := by
    rw [moduleSocle_quotient_eq_sup_map X S T hinf hTsimple hYuniserial,
      Submodule.map_sup, S.mkQ_map_self, bot_sup_eq]
    exact isSimpleModule_map_quotientMk_of_inf_eq_bot
      X S T hinf hTsimple
  have hZsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z) := by
    rw [moduleSocle_quotient_eq_sup_map X T S
      (by simpa [inf_comm] using hinf) hSsimple hZuniserial,
      Submodule.map_sup, T.mkQ_map_self, bot_sup_eq]
    exact isSimpleModule_map_quotientMk_of_inf_eq_bot
      X T S (by simpa [inf_comm] using hinf) hSsimple
  let eYsocle : T ≃ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ Y :=
    quotientBranchSocleLinearEquiv X S T hinf hTsimple hYuniserial
  let eZsocle : S ≃ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ Z :=
    quotientBranchSocleLinearEquiv X T S
      (by simpa [inf_comm] using hinf) hSsimple hZuniserial
  have hSocleNoniso : ¬ Nonempty
      (moduleSocle Aᵐᵒᵖ Y ≃ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ Z) := by
    rintro ⟨q⟩
    apply hSTnoniso
    exact ⟨eZsocle.trans (q.symm.trans eYsocle.symm)⟩
  have hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker := by
    rw [hYsocleEq, quotientFGMapQ_ker]
    exact Submodule.map_mono hSTJ
  have hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker := by
    rw [hZsocleEq, quotientFGMapQ_ker]
    exact Submodule.map_mono hSTJ
  let Yq := quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)
  have hYqLength : Module.length Aᵐᵒᵖ Yq = 2 :=
    length_quotient_moduleSocle_eq_two_of_length_eq_three
      hYsocle hYlength
  have hYqNontrivial : Nontrivial Yq :=
    Module.length_pos_iff.mp (by rw [hYqLength]; norm_num)
  letI : Nontrivial Yq := hYqNontrivial
  have hYqFiniteLength : IsFiniteLength Aᵐᵒᵖ Yq :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) Yq
  letI : IsArtinian Aᵐᵒᵖ Yq :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hYqFiniteLength).2
  have hYqUniserial : IsUniserialModule Aᵐᵒᵖ Yq :=
    hYuniserial.quotient (moduleSocle Aᵐᵒᵖ Y)
  have hYnextSimple : IsSimpleModule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ Yq) :=
    hYqUniserial.moduleSocle_isSimple
  let eYnext : moduleSocle Aᵐᵒᵖ Yq ≃ₗ[Aᵐᵒᵖ] F :=
    quotientBranchNextSocleLinearEquiv X S R le_sup_left hYsocleEq
  have hFsimple : IsSimpleModule Aᵐᵒᵖ F := by
    letI : IsSimpleModule Aᵐᵒᵖ
        (moduleSocle Aᵐᵒᵖ Yq) := hYnextSimple
    exact IsSimpleModule.congr eYnext.symm
  letI : Nontrivial F := hFsimple.nontrivial
  let eZnext : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) ≃ₗ[Aᵐᵒᵖ] F :=
    quotientBranchNextSocleLinearEquiv X T R le_sup_right hZsocleEq
  have hWfiniteLength : IsFiniteLength Aᵐᵒᵖ
      (fiberKernelFGObj Y Z Top f g) :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) (fiberKernelFGObj Y Z Top f g)
  letI : IsArtinian Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hWfiniteLength).2
  have hcomplementCapture : ∀ P : Submodule Aᵐᵒᵖ
      (fiberKernelFGObj Y Z Top f g),
      P ≠ ⊥ → IsUniserialModule Aᵐᵒᵖ P →
        ¬ P ≤ quotientBranchFiberKernelRadicalPreimage X S T J hSTJ →
          moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) ≤ P := by
    intro P hPne hPuniserial houtside
    letI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hPne
    exact moduleSocle_fiberKernel_le_of_hasMixed_of_nonisomorphic
      Y Z Top f g hYsocle hZsocle hSocleNoniso hYkill hZkill
        P hPuniserial.moduleSocle_isSimple
          (hasMixedSocleCoordinates_of_smulWitness
            Y Z Top f g P
              (quotientBranch_hasMixedSocleSmulWitness
                (k := k) X S T hinf hSsimple hTsimple hSTJ hXtop
                  hradicalSquare hradicalCube hYuniserial hZuniserial
                    P houtside))
  exact false_of_fiberKernel_induction_obstruction
    (k := k) e hall H Y Z Top F f g
      (quotientFGMapQ_surjective X S J (le_sup_left.trans hSTJ))
      (quotientFGMapQ_surjective X T J (le_sup_right.trans hSTJ))
      hYlength hZlength hTopLength hYsocle hZsocle hYkill hZkill
      hFsimple eYnext eZnext hcomplementCapture

include k in
/-- In the radical-square configuration of the first source obstruction,
quotienting by either simple branch produces a uniserial length-three
module.  The other branch is the simple radical of the branch radical. -/
theorem quotientBranch_uniserial_of_simple_radical_square
    (X : FinitelyGeneratedCategory A)
    (S T : Submodule Aᵐᵒᵖ X)
    (hinf : S ⊓ T = ⊥)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hSTJ : S ⊔ T ≤ Module.jacobson Aᵐᵒᵖ X)
    (hXtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj X (Module.jacobson Aᵐᵒᵖ X)))
    (hradicalSquare : Ring.jacobson Aᵐᵒᵖ ^ 2 •
      (⊤ : Submodule Aᵐᵒᵖ X) = S ⊔ T)
    (hXlength : Module.length Aᵐᵒᵖ X = 4) :
    IsUniserialModule Aᵐᵒᵖ (quotientFGObj X S) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := Aᵐᵒᵖ
  let J := Module.jacobson R X
  let Y := quotientFGObj X S
  let JY := Module.jacobson R Y
  have hSJ : S ≤ J := le_sup_left.trans hSTJ
  have hYjac : JY = J.map S.mkQ :=
    Module.jacobson_quotient_of_le hSJ
  let eTop : (Y ⧸ JY) ≃ₗ[R] (X ⧸ J) :=
    (Submodule.quotEquivOfEq _ _ hYjac).trans
      (Submodule.quotientQuotientEquivQuotient S J hSJ)
  have hYtop : IsSimpleModule R (Y ⧸ JY) := by
    letI : IsSimpleModule R (X ⧸ J) := hXtop
    exact IsSimpleModule.congr eTop
  have hmapJJY : (Module.jacobson R JY).map JY.subtype =
      T.map S.mkQ := by
    calc
      (Module.jacobson R JY).map JY.subtype =
          Ring.jacobson R ^ 2 • (⊤ : Submodule R Y) :=
        map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top
      _ = (Ring.jacobson R ^ 2 • (⊤ : Submodule R X)).map S.mkQ :=
        (map_ideal_smul_top_quotient (Ring.jacobson R ^ 2) S).symm
      _ = (S ⊔ T).map S.mkQ := by rw [hradicalSquare]
      _ = T.map S.mkQ := by
        rw [Submodule.map_sup, S.mkQ_map_self, bot_sup_eq]
  have hTmapSimple : IsSimpleModule R (T.map S.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot
      X S T hinf hTsimple
  have hJJYsimple : IsSimpleModule R (Module.jacobson R JY) := by
    apply isSimpleModule_of_map_of_injective
      JY.subtype JY.subtype_injective
    rw [hmapJJY]
    exact hTmapSimple
  have hYlength : Module.length R Y = 3 :=
    length_quotient_eq_three_of_length_eq_four_of_simple
      S hXlength hSsimple
  have hJYlength : Module.length R JY = 2 :=
    IsBiserialModule.jacobson_length_eq_two_of_simple_top_of_length_eq_three
      hYtop hYlength
  have hJJYlength : Module.length R (Module.jacobson R JY) = 1 :=
    Module.length_eq_one_iff.mpr hJJYsimple
  have hJYtopLength : Module.length R
      (JY ⧸ Module.jacobson R JY) = 1 := by
    have hexact : Module.length R JY =
        Module.length R (Module.jacobson R JY) +
          Module.length R (JY ⧸ Module.jacobson R JY) :=
      Module.length_eq_add_of_exact
        (Module.jacobson R JY).subtype (Module.jacobson R JY).mkQ
        (Module.jacobson R JY).subtype_injective
        (Module.jacobson R JY).mkQ_surjective
        (LinearMap.exact_subtype_mkQ (Module.jacobson R JY))
    rw [hJYlength, hJJYlength] at hexact
    apply WithTop.add_left_cancel ENat.one_ne_top
    calc
      1 + Module.length R (JY ⧸ Module.jacobson R JY) = 2 := hexact.symm
      _ = 1 + 1 := by norm_num
  have hJYuniserial : IsUniserialModule R JY := by
    apply IsUniserialModule.of_simpleTop_of_jacobson
    · exact Module.length_eq_one_iff.mp hJYtopLength
    · exact IsBiserialModule.uniserial_of_simple hJJYsimple
  exact IsUniserialModule.of_simpleTop_of_jacobson hYtop hJYuniserial

/-- The first source obstruction starting from the literal module `L`.
Here `X` is definitionally `L / rad³ L`; its simple top and vanishing third
radical layer are therefore conclusions of the truncation construction, not
premises supplied by the caller. -/
theorem false_of_radicalCubeTruncation_fiberKernel_induction_obstruction
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (S T : Submodule Aᵐᵒᵖ (radicalCubeTruncationFGObj L))
    (hinf : S ⊓ T = ⊥)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hSTnoniso : ¬ Nonempty (S ≃ₗ[Aᵐᵒᵖ] T))
    (hXlength : Module.length Aᵐᵒᵖ (radicalCubeTruncationFGObj L) = 4)
    (hradicalSquare : Ring.jacobson Aᵐᵒᵖ ^ 2 •
      (⊤ : Submodule Aᵐᵒᵖ (radicalCubeTruncationFGObj L)) = S ⊔ T)
    (hYuniserial : IsUniserialModule Aᵐᵒᵖ
      (quotientFGObj (radicalCubeTruncationFGObj L) S))
    (hZuniserial : IsUniserialModule Aᵐᵒᵖ
      (quotientFGObj (radicalCubeTruncationFGObj L) T)) :
    False := by
  apply false_of_quotientBranch_fiberKernel_induction_obstruction
    (k := k) e hall H (radicalCubeTruncationFGObj L) S T hinf
      hSsimple hTsimple hSTnoniso hXlength
  · exact (isSimpleModule_top_radicalCubeTruncation_iff (k := k) L).mpr hLtop
  · exact hradicalSquare
  · exact ringJacobson_cube_smul_top_radicalCubeTruncation_eq_bot L
  · exact hYuniserial
  · exact hZuniserial

/-- Complementary simple branches of `rad² L / rad³ L` embed as the
two exact second-radical branches of `X = L / rad³ L`.  If the intervening
layer `rad L / rad² L` is simple, the first fiber-kernel obstruction applies. -/
theorem false_of_radicalCubeTruncation_nestedRadicalBranches_induction_obstruction
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hJtop : IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ L ⧸
        Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L)))
    (S T : Submodule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L) ⧸
        Module.jacobson Aᵐᵒᵖ
          (Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L))))
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hcompl : IsCompl S T)
    (hSTnoniso : ¬ Nonempty (S ≃ₗ[Aᵐᵒᵖ] T)) :
    False := by
  let φ := radicalSecondTopToCubeTruncationMap (k := k) L
  let Sx := S.map φ
  let Tx := T.map φ
  have hφinj : Function.Injective φ :=
    radicalSecondTopToCubeTruncationMap_injective (k := k) L
  have hSxSimple : IsSimpleModule Aᵐᵒᵖ Sx :=
    isSimpleModule_map_of_injective φ hφinj S hSsimple
  have hTxSimple : IsSimpleModule Aᵐᵒᵖ Tx :=
    isSimpleModule_map_of_injective φ hφinj T hTsimple
  have hinf : Sx ⊓ Tx = ⊥ := by
    change S.map φ ⊓ T.map φ = ⊥
    rw [← Submodule.map_inf φ hφinj, hcompl.inf_eq_bot,
      Submodule.map_bot]
  have hradicalSquare : Ring.jacobson Aᵐᵒᵖ ^ 2 •
      (⊤ : Submodule Aᵐᵒᵖ (radicalCubeTruncationFGObj L)) =
      Sx ⊔ Tx := by
    change _ = S.map φ ⊔ T.map φ
    rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_top,
      radicalSecondTopToCubeTruncationMap_range]
  have hSTnonisoX : ¬ Nonempty (Sx ≃ₗ[Aᵐᵒᵖ] Tx) := by
    rintro ⟨hSTx⟩
    apply hSTnoniso
    exact ⟨
      (submoduleMapLinearEquivOfInjective φ hφinj S).trans
        (hSTx.trans
          (submoduleMapLinearEquivOfInjective φ hφinj T).symm)⟩
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  have hXtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj (radicalCubeTruncationFGObj L)
        (Module.jacobson Aᵐᵒᵖ (radicalCubeTruncationFGObj L))) :=
    (isSimpleModule_top_radicalCubeTruncation_iff (k := k) L).mpr hLtop
  have hSTJ : Sx ⊔ Tx ≤
      Module.jacobson Aᵐᵒᵖ (radicalCubeTruncationFGObj L) := by
    rw [← hradicalSquare,
      moduleJacobson_eq_ringJacobson_smul_top
        (R := Aᵐᵒᵖ) (M := radicalCubeTruncationFGObj L)]
    exact Submodule.smul_mono
      (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)) le_rfl
  have hRadicalLayerTop : IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (radicalCubeTruncationFGObj L) ⧸
        (Sx ⊔ Tx).comap
          (Module.jacobson Aᵐᵒᵖ
            (radicalCubeTruncationFGObj L)).subtype) := by
    rw [← hradicalSquare]
    exact isSimpleModule_radicalLayer_radicalCubeTruncation
      (k := k) L hJtop
  have hXlength : Module.length Aᵐᵒᵖ
      (radicalCubeTruncationFGObj L) = 4 :=
    length_eq_four_of_three_simple_radical_layers Sx Tx hinf
      hSxSimple hTxSimple hSTJ hRadicalLayerTop hXtop
  have hYuniserial : IsUniserialModule Aᵐᵒᵖ
      (quotientFGObj (radicalCubeTruncationFGObj L) Sx) :=
    quotientBranch_uniserial_of_simple_radical_square
      (k := k) (radicalCubeTruncationFGObj L) Sx Tx hinf
        hSxSimple hTxSimple hSTJ hXtop hradicalSquare hXlength
  have hZuniserial : IsUniserialModule Aᵐᵒᵖ
      (quotientFGObj (radicalCubeTruncationFGObj L) Tx) :=
    quotientBranch_uniserial_of_simple_radical_square
      (k := k) (radicalCubeTruncationFGObj L) Tx Sx
        (by simpa [inf_comm] using hinf) hTxSimple hSxSimple
        (by simpa [sup_comm] using hSTJ) hXtop
        (by simpa [sup_comm] using hradicalSquare) hXlength
  exact false_of_radicalCubeTruncation_fiberKernel_induction_obstruction
    (k := k) e hall H L hLtop Sx Tx hinf hSxSimple hTxSimple hSTnonisoX
      hXlength hradicalSquare hYuniserial hZuniserial

/-- A biserial but nonuniserial radical cannot itself have simple top under
the coordinate-thin hypothesis. -/
theorem false_of_biserial_nonuniserial_jacobson_simpleTop
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hJtop : IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ L ⧸
        Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L)))
    (hJbis : IsBiserialModule Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L))
    (hJnotuni : ¬ IsUniserialModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ L)) :
    False := by
  let J : Submodule Aᵐᵒᵖ L := Module.jacobson Aᵐᵒᵖ L
  obtain ⟨S, T, hSsimple, hTsimple, hcompl, hSTnoniso⟩ :=
    exists_nonisomorphic_complementary_simple_top_jacobson
      (k := k) e hall H (submoduleFGObj L J) hJtop hJbis hJnotuni
  exact false_of_radicalCubeTruncation_nestedRadicalBranches_induction_obstruction
    (k := k) e hall H L hLtop hJtop S T hSsimple hTsimple hcompl hSTnoniso

/-- In the direct induction, a nonuniserial local module cannot have a local
radical: the induction hypothesis makes that radical biserial, and the first
Pogorzały--Skowroński obstruction gives the contradiction. -/
theorem LocalBiserialBelow.not_jacobson_simpleTop_of_not_uniserial
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L) :
    ¬ IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ L ⧸
        Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L)) := by
  intro hJtop
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  have hfiniteLength : IsFiniteLength R L :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) L
  letI : IsArtinian R L :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  letI : Nontrivial (L ⧸ J) := hLtop.nontrivial
  letI : Nontrivial L := J.mkQ_surjective.nontrivial
  have hJlength : Module.length R J < Module.length R L :=
    J.length_lt (Module.jacobson_lt_top R L).ne
  have hJbis : IsBiserialModule R J :=
    Hbelow (submoduleFGObj L J) hJlength hJtop
  have hJnotuni : ¬ IsUniserialModule R J := by
    intro hJuni
    exact hLnotuni
      (IsUniserialModule.of_simpleTop_of_jacobson hLtop hJuni)
  exact false_of_biserial_nonuniserial_jacobson_simpleTop
    (k := k) e hall Hthin L hLtop hJtop hJbis hJnotuni

/-- If `rad² L` is nonzero, the smaller local quotient `L / rad² L`
allows the induction hypothesis to split `rad L / rad² L` into two
nonisomorphic simple summands. -/
theorem LocalBiserialBelow.exists_nonisomorphic_complementary_simple_top_jacobson_of_radicalSquare_ne_bot
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (hradicalSquare : radicalSquareSubmodule L ≠ ⊥) :
    ∃ S T : Submodule Aᵐᵒᵖ
        (Module.jacobson Aᵐᵒᵖ L ⧸
          Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L)),
      IsSimpleModule Aᵐᵒᵖ S ∧
        IsSimpleModule Aᵐᵒᵖ T ∧ IsCompl S T ∧
        ¬ Nonempty (S ≃ₗ[Aᵐᵒᵖ] T) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  let TopJ := J ⧸ Module.jacobson R J
  let Q := radicalSquareTruncationFGObj L
  let JQ := Module.jacobson R Q
  let TopJQ := JQ ⧸ Module.jacobson R JQ
  let E : TopJ ≃ₗ[R] TopJQ :=
    radicalTopSquareTruncationLinearEquiv (k := k) L
  have hQlength : Module.length R Q < Module.length R L :=
    (radicalSquareSubmodule L).length_quotient_lt hradicalSquare
  have hQtop : IsSimpleModule R (Q ⧸ Module.jacobson R Q) :=
    (isSimpleModule_top_radicalSquareTruncation_iff (k := k) L).mpr hLtop
  have hQbis : IsBiserialModule R Q :=
    Hbelow Q hQlength hQtop
  have hJnotSimple : ¬ IsSimpleModule R TopJ :=
    LocalBiserialBelow.not_jacobson_simpleTop_of_not_uniserial
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni
  have hJnontrivial : Nontrivial J := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hJzero
    apply hLnotuni
    exact IsUniserialModule.of_simpleTop_of_jacobson hLtop
      (IsUniserialModule.of_subsingleton (R := R) (M := J))
  letI : Nontrivial J := hJnontrivial
  have hTopJnontrivial : Nontrivial TopJ :=
    Submodule.Quotient.nontrivial_iff.mpr
      (Module.jacobson_lt_top R J).ne
  letI : Nontrivial TopJ := hTopJnontrivial
  have hQnotuni : ¬ IsUniserialModule R Q := by
    intro hQuni
    letI : Nontrivial TopJQ := E.injective.nontrivial
    letI : Nontrivial JQ := (Module.jacobson R JQ).mkQ_surjective.nontrivial
    have hJQtop : IsSimpleModule R TopJQ :=
      (hQuni.submodule JQ).top_isSimple
    exact hJnotSimple (E.isSimpleModule_iff.mpr hJQtop)
  obtain ⟨S, T, hSsimple, hTsimple, hcompl, hSTnoniso⟩ :=
    exists_nonisomorphic_complementary_simple_top_jacobson
      (k := k) e hall Hthin Q hQtop hQbis hQnotuni
  let S' : Submodule R TopJ := S.map E.symm.toLinearMap
  let T' : Submodule R TopJ := T.map E.symm.toLinearMap
  have hS'simple : IsSimpleModule R S' :=
    isSimpleModule_map_of_injective E.symm.toLinearMap E.symm.injective S hSsimple
  have hT'simple : IsSimpleModule R T' :=
    isSimpleModule_map_of_injective E.symm.toLinearMap E.symm.injective T hTsimple
  have hcompl' : IsCompl S' T' := by
    constructor
    · rw [disjoint_iff]
      change S.map E.symm.toLinearMap ⊓ T.map E.symm.toLinearMap = ⊥
      rw [← Submodule.map_inf E.symm.toLinearMap E.symm.injective,
        hcompl.inf_eq_bot, Submodule.map_bot]
    · rw [codisjoint_iff]
      change S.map E.symm.toLinearMap ⊔ T.map E.symm.toLinearMap = ⊤
      rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_top,
        LinearEquiv.range]
  have hSTnoniso' : ¬ Nonempty (S' ≃ₗ[R] T') := by
    rintro ⟨hST⟩
    apply hSTnoniso
    exact ⟨
      (submoduleMapLinearEquivOfInjective
          E.symm.toLinearMap E.symm.injective S).trans
        (hST.trans
          (submoduleMapLinearEquivOfInjective
            E.symm.toLinearMap E.symm.injective T).symm)⟩
  exact ⟨S', T', hS'simple, hT'simple, hcompl', hSTnoniso'⟩

/-- In the nonzero radical-square branch, the two simple factors of
`rad L / rad² L` lift to proper nonisomorphic local submodules which span
`rad L`. -/
theorem LocalBiserialBelow.exists_spanning_nonisomorphic_local_jacobson_submodules_of_radicalSquare_ne_bot
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (hradicalSquare : radicalSquareSubmodule L ≠ ⊥) :
    ∃ M N : Submodule Aᵐᵒᵖ L,
      M ⊔ N = Module.jacobson Aᵐᵒᵖ L ∧
        M ≠ ⊤ ∧ N ≠ ⊤ ∧
        IsSimpleModule Aᵐᵒᵖ (M ⧸ Module.jacobson Aᵐᵒᵖ M) ∧
        IsSimpleModule Aᵐᵒᵖ (N ⧸ Module.jacobson Aᵐᵒᵖ N) ∧
        (¬ Nonempty
          ((M ⧸ Module.jacobson Aᵐᵒᵖ M) ≃ₗ[Aᵐᵒᵖ]
            (N ⧸ Module.jacobson Aᵐᵒᵖ N))) ∧
        ¬ Nonempty (M ≃ₗ[Aᵐᵒᵖ] N) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  obtain ⟨S, T, hSsimple, hTsimple, hcompl, hSTnoniso⟩ :=
    LocalBiserialBelow.exists_nonisomorphic_complementary_simple_top_jacobson_of_radicalSquare_ne_bot
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni hradicalSquare
  obtain ⟨P, Q, hPQsup, hPtop, hQtop, -, -,
      hPQtopNoniso, hPQnoniso⟩ :=
    exists_spanning_local_lifts_of_complementary_simples
      S T hSsimple hTsimple hcompl hSTnoniso
  let M : Submodule R L := P.map J.subtype
  let N : Submodule R L := Q.map J.subtype
  have hJinjective : Function.Injective J.subtype := J.subtype_injective
  let eP : P ≃ₗ[R] M :=
    submoduleMapLinearEquivOfInjective J.subtype hJinjective P
  let eQ : Q ≃ₗ[R] N :=
    submoduleMapLinearEquivOfInjective J.subtype hJinjective Q
  have hMNsup : M ⊔ N = J := by
    change P.map J.subtype ⊔ Q.map J.subtype = J
    rw [← Submodule.map_sup, hPQsup, Submodule.map_top,
      Submodule.range_subtype]
  have hMtop : IsSimpleModule R (M ⧸ Module.jacobson R M) :=
    isSimpleModule_top_congr eP hPtop
  have hNtop : IsSimpleModule R (N ⧸ Module.jacobson R N) :=
    isSimpleModule_top_congr eQ hQtop
  have hMNtopNoniso : ¬ Nonempty
      ((M ⧸ Module.jacobson R M) ≃ₗ[R]
        (N ⧸ Module.jacobson R N)) := by
    rintro ⟨eMNtop⟩
    apply hPQtopNoniso
    exact ⟨(moduleTopLinearEquiv eP).trans
      (eMNtop.trans (moduleTopLinearEquiv eQ).symm)⟩
  have hMNnoniso : ¬ Nonempty (M ≃ₗ[R] N) := by
    rintro ⟨eMN⟩
    exact hPQnoniso ⟨eP.trans (eMN.trans eQ.symm)⟩
  letI : Nontrivial (L ⧸ J) := hLtop.nontrivial
  letI : Nontrivial L := J.mkQ_surjective.nontrivial
  have hJlt : J < ⊤ := Module.jacobson_lt_top R L
  have hMproper : M ≠ ⊤ := by
    intro hMtop'
    apply hJlt.ne
    exact top_unique (hMtop' ▸ Submodule.map_subtype_le J P)
  have hNproper : N ≠ ⊤ := by
    intro hNtop'
    apply hJlt.ne
    exact top_unique (hNtop' ▸ Submodule.map_subtype_le J Q)
  exact ⟨M, N, hMNsup, hMproper, hNproper, hMtop, hNtop,
    hMNtopNoniso, hMNnoniso⟩

include k in
/-- If the two local submodules spanning `rad L` are disjoint, the smaller
quotients by the opposite branches make both submodules uniserial. -/
theorem LocalBiserialBelow.uniserial_branches_of_disjoint_spanning_jacobson
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMNinf : M ⊓ N = ⊥)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N)) :
    IsUniserialModule Aᵐᵒᵖ M ∧ IsUniserialModule Aᵐᵒᵖ N := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  change M ⊔ N = J at hMNsup
  have hMJ : M ≤ J := by
    rw [← hMNsup]
    exact le_sup_left
  have hNJ : N ≤ J := by
    rw [← hMNsup]
    exact le_sup_right
  have hMnontrivial : Nontrivial M := by
    letI : Nontrivial (M ⧸ Module.jacobson R M) := hMtop.nontrivial
    exact (Module.jacobson R M).mkQ_surjective.nontrivial
  have hNnontrivial : Nontrivial N := by
    letI : Nontrivial (N ⧸ Module.jacobson R N) := hNtop.nontrivial
    exact (Module.jacobson R N).mkQ_surjective.nontrivial
  have hMneBot : M ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp hMnontrivial
  have hNneBot : N ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp hNnontrivial
  let Y := quotientFGObj L M
  let Z := quotientFGObj L N
  let JY := Module.jacobson R Y
  let JZ := Module.jacobson R Z
  have hYlength : Module.length R Y < Module.length R L :=
    M.length_quotient_lt hMneBot
  have hZlength : Module.length R Z < Module.length R L :=
    N.length_quotient_lt hNneBot
  have hYtop : IsSimpleModule R (Y ⧸ JY) :=
    isSimpleModule_top_quotient_of_le_jacobson M hMJ hLtop
  have hZtop : IsSimpleModule R (Z ⧸ JZ) :=
    isSimpleModule_top_quotient_of_le_jacobson N hNJ hLtop
  have hYjac : JY = J.map M.mkQ :=
    Module.jacobson_quotient_of_le hMJ
  have hZjac : JZ = J.map N.mkQ :=
    Module.jacobson_quotient_of_le hNJ
  let fN : N →ₗ[R] Y :=
    IsBiserialModule.submoduleToQuotientLinearMap N M
  have hfN : Function.Injective fN :=
    IsBiserialModule.submoduleToQuotientLinearMap_injective_of_inf_eq_bot
      N M (by simpa [inf_comm] using hMNinf)
  have hfNrange : LinearMap.range fN = JY := by
    have hrange : LinearMap.range fN = N.map M.mkQ := by
      ext x
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, n.2, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, hn⟩, rfl⟩
    rw [hYjac]
    change LinearMap.range fN = J.map M.mkQ
    rw [hrange, ← hMNsup, Submodule.map_sup,
      M.mkQ_map_self, bot_sup_eq]
  let eNY : N ≃ₗ[R] JY :=
    (LinearEquiv.ofInjective fN hfN).trans
      (LinearEquiv.ofEq _ _ hfNrange)
  have hJYtop : IsSimpleModule R (JY ⧸ Module.jacobson R JY) :=
    isSimpleModule_top_congr eNY hNtop
  have hYuni : IsUniserialModule R Y :=
    LocalBiserialBelow.uniserial_of_jacobson_simpleTop
      Hbelow Y hYlength hYtop hJYtop
  let fM : M →ₗ[R] Z :=
    IsBiserialModule.submoduleToQuotientLinearMap M N
  have hfM : Function.Injective fM :=
    IsBiserialModule.submoduleToQuotientLinearMap_injective_of_inf_eq_bot
      M N hMNinf
  have hfMrange : LinearMap.range fM = JZ := by
    have hrange : LinearMap.range fM = M.map N.mkQ := by
      ext x
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨m, m.2, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hm⟩, rfl⟩
    rw [hZjac]
    change LinearMap.range fM = J.map N.mkQ
    rw [hrange, ← hMNsup, Submodule.map_sup,
      N.mkQ_map_self, sup_bot_eq]
  let eMZ : M ≃ₗ[R] JZ :=
    (LinearEquiv.ofInjective fM hfM).trans
      (LinearEquiv.ofEq _ _ hfMrange)
  have hJZtop : IsSimpleModule R (JZ ⧸ Module.jacobson R JZ) :=
    isSimpleModule_top_congr eMZ hMtop
  have hZuni : IsUniserialModule R Z :=
    LocalBiserialBelow.uniserial_of_jacobson_simpleTop
      Hbelow Z hZlength hZtop hJZtop
  exact ⟨hZuni.of_injective fM hfM, hYuni.of_injective fN hfN⟩

include k in
/-- If a local branch `M` is proper and not contained in the other branch
`N`, induction and biseriality bound a semisimple intersection by length
two. -/
theorem LocalBiserialBelow.length_inf_le_two_of_semisimple_of_not_le
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hMproper : M ≠ ⊤)
    (hMnotleN : ¬ M ≤ N)
    [IsSemisimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)] :
    Module.length Aᵐᵒᵖ ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) ≤ 2 := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := Aᵐᵒᵖ
  let I : Submodule R L := M ⊓ N
  let IM : Submodule R M := I.comap M.subtype
  have hIleM : I ≤ M := inf_le_left
  let eIM : IM ≃ₗ[R] I := Submodule.comapSubtypeEquivOfLe hIleM
  letI : IsSemisimpleModule R IM := IsSemisimpleModule.congr eIM
  have hMlength : Module.length R M < Module.length R L :=
    M.length_lt hMproper
  have hMbis : IsBiserialModule R M :=
    Hbelow (submoduleFGObj L M) hMlength hMtop
  have hIMproper : IM ≠ ⊤ := by
    intro hIM
    apply hMnotleN
    intro x hx
    have hxIM : (⟨x, hx⟩ : M) ∈ IM := hIM.symm ▸ Submodule.mem_top
    change x ∈ I at hxIM
    exact hxIM.2
  have hIMjac : IM ≤ Module.jacobson R M :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hMtop hIMproper
  calc
    Module.length R I = Module.length R IM := eIM.length_eq.symm
    _ ≤ 2 :=
      semisimple_submodule_length_le_two_of_biserial_of_le_jacobson
        hMbis IM hIMjac

/-- The two local branches spanning `rad L` are incomparable.  Otherwise
one branch would be the whole radical, contrary to the already established
nonlocality of `rad L`. -/
theorem LocalBiserialBelow.spanning_local_jacobson_submodules_incomparable
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N)) :
    ¬ M ≤ N ∧ ¬ N ≤ M := by
  have hJnotlocal :=
    LocalBiserialBelow.not_jacobson_simpleTop_of_not_uniserial
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni
  constructor
  · intro hMN
    have hNJ : N = Module.jacobson Aᵐᵒᵖ L := by
      apply le_antisymm
      · rw [← hMNsup]
        exact le_sup_right
      · rw [← hMNsup]
        exact sup_le hMN le_rfl
    rw [hNJ] at hNtop
    exact hJnotlocal hNtop
  · intro hNM
    have hMJ : M = Module.jacobson Aᵐᵒᵖ L := by
      apply le_antisymm
      · rw [← hMNsup]
        exact le_sup_left
      · rw [← hMNsup]
        exact sup_le le_rfl hNM
    rw [hMJ] at hMtop
    exact hJnotlocal hMtop

/-- The intersection of the two nonisomorphic local submodules spanning the
radical is semisimple.  A hypothetical nonsemisimple intersection supplies
a maximal nonsimple uniserial submodule.  Biseriality of the two smaller
sides and of `L / soc L` produces the ambient-or-quotient carriers, whose
diagonal cokernel gives the coordinate-thin contradiction. -/
theorem LocalBiserialBelow.inf_isSemisimple
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hPQsup : P ⊔ Q = Module.jacobson Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q))
    (hPQtop : ¬ Nonempty
      ((P ⧸ Module.jacobson Aᵐᵒᵖ P) ≃ₗ[Aᵐᵒᵖ]
        (Q ⧸ Module.jacobson Aᵐᵒᵖ Q))) :
    IsSemisimpleModule Aᵐᵒᵖ
      ↥(P ⊓ Q : Submodule Aᵐᵒᵖ L) := by
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  let S : Submodule R L := moduleSocle R L
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  have hnotle :=
    LocalBiserialBelow.spanning_local_jacobson_submodules_incomparable
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni
        P Q hPQsup hPtop hQtop
  have hIP : P ⊓ Q < P := by
    apply lt_of_le_of_ne inf_le_left
    intro hinf
    apply hnotle.1
    rw [← hinf]
    exact inf_le_right
  have hIQ : P ⊓ Q < Q := by
    apply lt_of_le_of_ne inf_le_right
    intro hinf
    apply hnotle.2
    rw [← hinf]
    exact inf_le_left
  have hPJ : P ≤ J := by
    change P ≤ Module.jacobson Aᵐᵒᵖ L
    rw [← hPQsup]
    exact le_sup_left
  have hQJ : Q ≤ J := by
    change Q ≤ Module.jacobson Aᵐᵒᵖ L
    rw [← hPQsup]
    exact le_sup_right
  letI : Nontrivial (L ⧸ J) := hLtop.nontrivial
  letI : Nontrivial L := J.mkQ_surjective.nontrivial
  have hPproper : P ≠ ⊤ :=
    (lt_of_le_of_lt hPJ (Module.jacobson_lt_top R L)).ne
  have hQproper : Q ≠ ⊤ :=
    (lt_of_le_of_lt hQJ (Module.jacobson_lt_top R L)).ne
  have hPbis : IsBiserialModule R P :=
    Hbelow (submoduleFGObj L P) (P.length_lt hPproper) hPtop
  have hQbis : IsBiserialModule R Q :=
    Hbelow (submoduleFGObj L Q) (Q.length_lt hQproper) hQtop
  have hLnotSimple : ¬ IsSimpleModule R L := by
    intro hsimple
    exact hLnotuni (IsBiserialModule.uniserial_of_simple hsimple)
  have hSJ : S ≤ J :=
    moduleSocle_le_jacobson_of_simpleTop_of_not_simple
      hLtop hLnotSimple
  have hLbarBis : IsBiserialModule R (quotientFGObj L S) :=
    Hbelow.biserial_quotient_moduleSocle
      L le_rfl hLtop hLnotuni
  have hLthin : IsCoordinateThin (k := k) e L :=
    coordinateThin_of_simpleTop e Hthin L hLtop
  have hPbar : IsUniserialModule R (P.map S.mkQ) :=
    uniserial_map_quotient_of_simpleTop_submodule_of_coordinateThin_of_biserial
      e hall L hLthin S P hSJ hPJ hPtop hLbarBis
  have hQbar : IsUniserialModule R (Q.map S.mkQ) :=
    uniserial_map_quotient_of_simpleTop_submodule_of_coordinateThin_of_biserial
      e hall L hLthin S Q hSJ hQJ hQtop hLbarBis
  by_contra hInot
  exact false_of_not_semisimple_inf_of_biserial_sides
    e hall Hthin L hLthin P Q hIP hIQ hPtop hQtop hPQtop
      hPbis hQbis hPbar hQbar hInot

/-- Once the nonzero intersection in the source proof is known to be
semisimple, it has composition length at most two. -/
theorem LocalBiserialBelow.length_inf_le_two_of_semisimple
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    [IsSemisimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)] :
    Module.length Aᵐᵒᵖ ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) ≤ 2 := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  have hnotle :=
    LocalBiserialBelow.spanning_local_jacobson_submodules_incomparable
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni M N hMNsup hMtop hNtop
  letI : Nontrivial (L ⧸ J) := hLtop.nontrivial
  letI : Nontrivial L := J.mkQ_surjective.nontrivial
  have hMJ : M ≤ J := by
    change M ≤ Module.jacobson Aᵐᵒᵖ L
    rw [← hMNsup]
    exact le_sup_left
  have hMproper : M ≠ ⊤ :=
    (lt_of_le_of_lt hMJ (Module.jacobson_lt_top R L)).ne
  exact LocalBiserialBelow.length_inf_le_two_of_semisimple_of_not_le
    (k := k) L Hbelow M N hMtop hMproper hnotle.1


/-- If the semisimple branch intersection has composition length two, its
images inside both local branches are exactly their socles. -/
theorem LocalBiserialBelow.inf_eq_mapped_socles_of_semisimple_of_length_eq_two
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    [IsSemisimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)]
    (hlength : Module.length Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) = 2) :
    M ⊓ N = (moduleSocle Aᵐᵒᵖ M).map M.subtype ∧
      M ⊓ N = (moduleSocle Aᵐᵒᵖ N).map N.subtype := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  let I : Submodule R L := M ⊓ N
  have hnotle :=
    LocalBiserialBelow.spanning_local_jacobson_submodules_incomparable
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni M N hMNsup hMtop hNtop
  letI : Nontrivial (L ⧸ J) := hLtop.nontrivial
  letI : Nontrivial L := J.mkQ_surjective.nontrivial
  have hMJ : M ≤ J := by
    change M ≤ Module.jacobson Aᵐᵒᵖ L
    rw [← hMNsup]
    exact le_sup_left
  have hNJ : N ≤ J := by
    change N ≤ Module.jacobson Aᵐᵒᵖ L
    rw [← hMNsup]
    exact le_sup_right
  have hMproper : M ≠ ⊤ :=
    (lt_of_le_of_lt hMJ (Module.jacobson_lt_top R L)).ne
  have hNproper : N ≠ ⊤ :=
    (lt_of_le_of_lt hNJ (Module.jacobson_lt_top R L)).ne
  have hMlength : Module.length R M < Module.length R L :=
    M.length_lt hMproper
  have hNlength : Module.length R N < Module.length R L :=
    N.length_lt hNproper
  have hMbis : IsBiserialModule R M :=
    Hbelow (submoduleFGObj L M) hMlength hMtop
  have hNbis : IsBiserialModule R N :=
    Hbelow (submoduleFGObj L N) hNlength hNtop
  let IM : Submodule R M := I.comap M.subtype
  let IN : Submodule R N := I.comap N.subtype
  have hIleM : I ≤ M := inf_le_left
  have hIleN : I ≤ N := inf_le_right
  let eIM : IM ≃ₗ[R] I := Submodule.comapSubtypeEquivOfLe hIleM
  let eIN : IN ≃ₗ[R] I := Submodule.comapSubtypeEquivOfLe hIleN
  letI : IsSemisimpleModule R IM := IsSemisimpleModule.congr eIM
  letI : IsSemisimpleModule R IN := IsSemisimpleModule.congr eIN
  have hIMproper : IM ≠ ⊤ := by
    intro hIM
    apply hnotle.1
    intro x hx
    have hxIM : (⟨x, hx⟩ : M) ∈ IM := hIM.symm ▸ Submodule.mem_top
    change x ∈ I at hxIM
    exact hxIM.2
  have hINproper : IN ≠ ⊤ := by
    intro hIN
    apply hnotle.2
    intro x hx
    have hxIN : (⟨x, hx⟩ : N) ∈ IN := hIN.symm ▸ Submodule.mem_top
    change x ∈ I at hxIN
    exact hxIN.1
  have hIMjac : IM ≤ Module.jacobson R M :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hMtop hIMproper
  have hINjac : IN ≤ Module.jacobson R N :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hNtop hINproper
  have hIMlength : Module.length R IM = 2 := eIM.length_eq.trans hlength
  have hINlength : Module.length R IN = 2 := eIN.length_eq.trans hlength
  have hIMsoc : IM = moduleSocle R M :=
    semisimple_submodule_eq_moduleSocle_of_biserial_of_simple_top_of_length_eq_two
      hMbis hMtop IM hIMjac hIMlength
  have hINsoc : IN = moduleSocle R N :=
    semisimple_submodule_eq_moduleSocle_of_biserial_of_simple_top_of_length_eq_two
      hNbis hNtop IN hINjac hINlength
  constructor
  · calc
      I = IM.map M.subtype := by
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr hIleM]
      _ = (moduleSocle R M).map M.subtype := by rw [hIMsoc]
  · calc
      I = IN.map N.subtype := by
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr hIleN]
      _ = (moduleSocle R N).map N.subtype := by rw [hINsoc]




/-- A semisimple length-two intersection splits into complementary
nonisomorphic simples.  Isomorphic summands would themselves be a repeated
self-subquotient of the indecomposable local ambient module. -/
theorem exists_nonisomorphic_complementary_simple_inf_of_semisimple_of_length_eq_two
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    [IsSemisimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)]
    (hlength : Module.length Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) = 2) :
    ∃ S T : Submodule Aᵐᵒᵖ
        ↥(M ⊓ N : Submodule Aᵐᵒᵖ L),
      IsSimpleModule Aᵐᵒᵖ S ∧
        IsSimpleModule Aᵐᵒᵖ T ∧ IsCompl S T ∧
        ¬ Nonempty (S ≃ₗ[Aᵐᵒᵖ] T) := by
  let I : Submodule Aᵐᵒᵖ L := M ⊓ N
  obtain ⟨S, T, hSsimple, hTsimple, hcompl⟩ :=
    exists_complementary_simple_of_semisimple_of_length_eq_two hlength
  refine ⟨S, T, hSsimple, hTsimple, hcompl, ?_⟩
  rintro ⟨hST⟩
  let F := submoduleFGObj (submoduleFGObj L I) S
  letI : Nontrivial F := hSsimple.nontrivial
  let eProd : I ≃ₗ[Aᵐᵒᵖ] (F × F) :=
    (S.prodEquivOfIsCompl T hcompl).symm.trans
      (LinearEquiv.prodCongr (LinearEquiv.refl Aᵐᵒᵖ S) hST.symm)
  have hRepeated : HasRepeatedSelfSubquotient L :=
    hasRepeatedSelfSubquotient_of_submodule_linearEquiv_prod_self
      L F I eProd
  exact no_repeatedSelfSubquotient_of_simpleTop_of_all_coordinateThin
    (k := k) e hall Hthin L hLtop hRepeated


/-- In the nonzero-intersection branch, semisimplicity and exclusion of
composition length two reduce the intersection to a simple module. -/
theorem LocalBiserialBelow.simple_inf_of_semisimple_of_length_ne_two
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    [IsSemisimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)]
    (hinfNe : M ⊓ N ≠ ⊥)
    (hlengthNe : Module.length Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) ≠ 2) :
    IsSimpleModule Aᵐᵒᵖ ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) := by
  letI : Nontrivial ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) :=
    Submodule.nontrivial_iff_ne_bot.mpr hinfNe
  exact isSimpleModule_of_nontrivial_of_length_le_two_of_ne_two
    (R := Aᵐᵒᵖ)
    (LocalBiserialBelow.length_inf_le_two_of_semisimple
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni M N
        hMNsup hMtop hNtop)
    hlengthNe

/-- Every summand of an intersection identified with the left branch socle
maps into the left branch radical, provided the branches are incomparable. -/
theorem infSummand_map_left_le_jacobson_of_eq_mapped_socle
    (L : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hPnotleQ : ¬ P ≤ Q)
    (hinfSoc : P ⊓ Q =
      (moduleSocle Aᵐᵒᵖ P).map P.subtype)
    (T : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    T.map (infToLeftLinearMap P Q) ≤ Module.jacobson Aᵐᵒᵖ P := by
  have hsocNeTop : moduleSocle Aᵐᵒᵖ P ≠ ⊤ := by
    intro hsocTop
    apply hPnotleQ
    intro x hxP
    have hInfEqP : P ⊓ Q = P := by
      rw [hinfSoc, hsocTop, Submodule.map_top,
        Submodule.range_subtype]
    have hxInf : x ∈ P ⊓ Q := hInfEqP.symm ▸ hxP
    exact hxInf.2
  have hsocJ : moduleSocle Aᵐᵒᵖ P ≤ Module.jacobson Aᵐᵒᵖ P :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
      hPtop hsocNeTop
  refine le_trans ?_ hsocJ
  rintro y ⟨t, -, hty⟩
  have htMap : t.1 ∈ (moduleSocle Aᵐᵒᵖ P).map P.subtype :=
    hinfSoc ▸ t.2
  obtain ⟨z, hzSoc, hz⟩ := htMap
  have htz : infToLeftLinearMap P Q t = z := by
    apply Subtype.ext
    exact hz.symm
  rw [← hty]
  exact htz ▸ hzSoc

/-- Right-hand version of
`infSummand_map_left_le_jacobson_of_eq_mapped_socle`. -/
theorem infSummand_map_right_le_jacobson_of_eq_mapped_socle
    (L : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q))
    (hQnotleP : ¬ Q ≤ P)
    (hinfSoc : P ⊓ Q =
      (moduleSocle Aᵐᵒᵖ Q).map Q.subtype)
    (T : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    T.map (infToRightLinearMap P Q) ≤ Module.jacobson Aᵐᵒᵖ Q := by
  have hsocNeTop : moduleSocle Aᵐᵒᵖ Q ≠ ⊤ := by
    intro hsocTop
    apply hQnotleP
    intro x hxQ
    have hInfEqQ : P ⊓ Q = Q := by
      rw [hinfSoc, hsocTop, Submodule.map_top,
        Submodule.range_subtype]
    have hxInf : x ∈ P ⊓ Q := hInfEqQ.symm ▸ hxQ
    exact hxInf.1
  have hsocJ : moduleSocle Aᵐᵒᵖ Q ≤ Module.jacobson Aᵐᵒᵖ Q :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
      hQtop hsocNeTop
  refine le_trans ?_ hsocJ
  rintro y ⟨t, -, hty⟩
  have htMap : t.1 ∈ (moduleSocle Aᵐᵒᵖ Q).map Q.subtype :=
    hinfSoc ▸ t.2
  obtain ⟨z, hzSoc, hz⟩ := htMap
  have htz : infToRightLinearMap P Q t = z := by
    apply Subtype.ext
    exact hz.symm
  rw [← hty]
  exact htz ▸ hzSoc

/-- The semisimple length-two intersection branch is impossible.  Gluing
one simple intersection summand produces a cokernel which the ambient
coordinate argument makes indecomposable, while its repeated complementary
summand forbids indecomposability under the global thinness hypothesis. -/
theorem LocalBiserialBelow.false_of_semisimple_inf_length_eq_two
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hPQsup : P ⊔ Q = Module.jacobson Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q))
    [IsSemisimpleModule Aᵐᵒᵖ
      ↥(P ⊓ Q : Submodule Aᵐᵒᵖ L)]
    (hlength : Module.length Aᵐᵒᵖ
      ↥(P ⊓ Q : Submodule Aᵐᵒᵖ L) = 2) :
    False := by
  let I := submoduleFGObj L (P ⊓ Q)
  have hnotle :=
    LocalBiserialBelow.spanning_local_jacobson_submodules_incomparable
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni P Q
        hPQsup hPtop hQtop
  obtain ⟨hinfSocP, hinfSocQ⟩ :=
    LocalBiserialBelow.inf_eq_mapped_socles_of_semisimple_of_length_eq_two
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni P Q
        hPQsup hPtop hQtop hlength
  obtain ⟨K, T, hKsimple, hTsimple, hcompl, -⟩ :=
    exists_nonisomorphic_complementary_simple_inf_of_semisimple_of_length_eq_two
      (k := k) e hall Hthin L hLtop P Q hlength
  have hTPJ : T.map (infToLeftLinearMap P Q) ≤
      Module.jacobson Aᵐᵒᵖ P :=
    infSummand_map_left_le_jacobson_of_eq_mapped_socle
      L P Q hPtop hnotle.1 hinfSocP T
  have hTQJ : T.map (infToRightLinearMap P Q) ≤
      Module.jacobson Aᵐᵒᵖ Q :=
    infSummand_map_right_le_jacobson_of_eq_mapped_socle
      L P Q hQtop hnotle.2 hinfSocQ T
  have hTPsimple : IsSimpleModule Aᵐᵒᵖ
      (T.map (infToLeftLinearMap P Q)) :=
    isSimpleModule_map_of_injective (infToLeftLinearMap P Q)
      (infToLeftLinearMap_injective P Q) T hTsimple
  have hTQsimple : IsSimpleModule Aᵐᵒᵖ
      (T.map (infToRightLinearMap P Q)) :=
    isSimpleModule_map_of_injective (infToRightLinearMap P Q)
      (infToRightLinearMap_injective P Q) T hTsimple
  have hTopPTP : ¬ Nonempty
      ((P ⧸ Module.jacobson Aᵐᵒᵖ P) ≃ₗ[Aᵐᵒᵖ]
        T.map (infToLeftLinearMap P Q)) :=
    nonisomorphic_top_and_nonzero_jacobson_submodule_of_simpleTop
      (k := k) e hall Hthin (submoduleFGObj L P) hPtop _
        (Submodule.nontrivial_iff_ne_bot.mp hTPsimple.nontrivial) hTPJ
  have hTopQTQ : ¬ Nonempty
      ((Q ⧸ Module.jacobson Aᵐᵒᵖ Q) ≃ₗ[Aᵐᵒᵖ]
        T.map (infToRightLinearMap P Q)) :=
    nonisomorphic_top_and_nonzero_jacobson_submodule_of_simpleTop
      (k := k) e hall Hthin (submoduleFGObj L Q) hQtop _
        (Submodule.nontrivial_iff_ne_bot.mp hTQsimple.nontrivial) hTQJ
  let S := submoduleFGObj I K
  let C := submoduleFGObj L P
  let D := submoduleFGObj L Q
  let iC : I →ₗ[Aᵐᵒᵖ] C := infToLeftLinearMap P Q
  let iD : I →ₗ[Aᵐᵒᵖ] D := infToRightLinearMap P Q
  let sC : S →ₗ[Aᵐᵒᵖ] C := iC.comp K.subtype
  let sD : S →ₗ[Aᵐᵒᵖ] D := iD.comp K.subtype
  let h : S →ₗ[Aᵐᵒᵖ] (C × D) := sC.prod sD
  letI : Nontrivial S := hKsimple.nontrivial
  have hindModule :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ (cokernelFGObj S (prodFGObj C D) h) :=
    isIndecomposableModule_diagonalInfSummandCokernel_of_coordinateThin
      (k := k) e hall L
        (coordinateThin_of_simpleTop e Hthin L hLtop)
        P Q hPtop hQtop K T hKsimple hTsimple hcompl hTopPTP hTopQTQ
  have hind : Indecomposable
      (cokernelFGObj S (prodFGObj C D) h) :=
    (FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) (cokernelFGObj S (prodFGObj C D) h)).mp
        hindModule
  let eQuotT : ((submoduleFGObj L (P ⊓ Q)) ⧸ K) ≃ₗ[Aᵐᵒᵖ] T :=
    K.quotientEquivOfIsCompl T hcompl
  letI : Nontrivial T := hTsimple.nontrivial
  letI : Nontrivial ((submoduleFGObj L (P ⊓ Q)) ⧸ K) :=
    eQuotT.symm.injective.nontrivial
  have hquotNontrivial : Nontrivial
      ((submoduleFGObj L (P ⊓ Q)) ⧸ K) := inferInstance
  have hnot :=
    @not_indec_diagonalSubmoduleCokernel_of_all_coordinateThin
      k A _ _ _ _ _ ι _ e hall Hthin
      (submoduleFGObj L (P ⊓ Q)) (submoduleFGObj L P)
      (submoduleFGObj L Q) K iC iD
      (infToLeftLinearMap_injective P Q)
      (infToRightLinearMap_injective P Q) hquotNontrivial
  exact hnot hind

/-- Once the nonzero branch intersection is semisimple, it is simple.  The
only other possible positive length was two, and the diagonal-cokernel
obstruction excludes that case. -/
theorem LocalBiserialBelow.simple_inf_of_semisimple
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    [IsSemisimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)]
    (hinfNe : M ⊓ N ≠ ⊥) :
    IsSimpleModule Aᵐᵒᵖ ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) := by
  apply LocalBiserialBelow.simple_inf_of_semisimple_of_length_ne_two
    (k := k) e hall Hthin L Hbelow hLtop hLnotuni M N
      hMNsup hMtop hNtop hinfNe
  intro hlength
  exact LocalBiserialBelow.false_of_semisimple_inf_length_eq_two
    (k := k) e hall Hthin L Hbelow hLtop hLnotuni M N
      hMNsup hMtop hNtop hlength

/-- The nonzero intersection of the two local branches supplied by the
radical-top construction is simple.  Semisimplicity and the exclusion of
length two are both consequences rather than inputs. -/
theorem LocalBiserialBelow.simple_inf
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    (hMNtop : ¬ Nonempty
      ((M ⧸ Module.jacobson Aᵐᵒᵖ M) ≃ₗ[Aᵐᵒᵖ]
        (N ⧸ Module.jacobson Aᵐᵒᵖ N)))
    (hinfNe : M ⊓ N ≠ ⊥) :
    IsSimpleModule Aᵐᵒᵖ ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) := by
  letI : IsSemisimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) :=
    LocalBiserialBelow.inf_isSemisimple
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni
        M N hMNsup hMtop hNtop hMNtop
  exact LocalBiserialBelow.simple_inf_of_semisimple
    (k := k) e hall Hthin L Hbelow hLtop hLnotuni
      M N hMNsup hMtop hNtop hinfNe

/-- A nonzero radical submodule gives a smaller local quotient.  If induction
makes that quotient biserial, coordinate-thin branch placement makes the
image of any simple-top radical submodule uniserial. -/
theorem LocalBiserialBelow.uniserial_submodule_quotient_by_nonzero_radical
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (K P : Submodule Aᵐᵒᵖ L)
    (hKne : K ≠ ⊥)
    (hKleJ : K ≤ Module.jacobson Aᵐᵒᵖ L)
    (hPleJ : P ≤ Module.jacobson Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P)) :
    IsUniserialModule Aᵐᵒᵖ (P ⧸ K.comap P.subtype) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  have hKquotLength : Module.length Aᵐᵒᵖ (quotientFGObj L K) <
      Module.length Aᵐᵒᵖ L :=
    K.length_quotient_lt hKne
  have hKquotTop : IsSimpleModule Aᵐᵒᵖ
      ((quotientFGObj L K) ⧸
        Module.jacobson Aᵐᵒᵖ (quotientFGObj L K)) :=
    isSimpleModule_top_quotient_of_le_jacobson K hKleJ hLtop
  have hKquotBis : IsBiserialModule Aᵐᵒᵖ (quotientFGObj L K) :=
    Hbelow (quotientFGObj L K) hKquotLength hKquotTop
  have hLthin : IsCoordinateThin (k := k) e L :=
    coordinateThin_of_simpleTop e Hthin L hLtop
  have hPmap : IsUniserialModule Aᵐᵒᵖ (P.map K.mkQ) :=
    uniserial_map_quotient_of_simpleTop_submodule_of_coordinateThin_of_biserial
      e hall L hLthin K P hKleJ hPleJ hPtop hKquotBis
  exact IsUniserialModule.congr
    (submoduleQuotientLinearEquivMap P K).symm hPmap

/-- After the branch intersection has been proved simple, induction on the
quotient by that intersection makes both branch quotients uniserial. -/
theorem LocalBiserialBelow.uniserial_branch_quotients_by_simple_inf
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    (hinfSimple : IsSimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)) :
    IsUniserialModule Aᵐᵒᵖ
        (M ⧸ (M ⊓ N).comap M.subtype) ∧
      IsUniserialModule Aᵐᵒᵖ
        (N ⧸ (M ⊓ N).comap N.subtype) := by
  let R := Aᵐᵒᵖ
  let I : Submodule R L := M ⊓ N
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  have hIne : I ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hinfSimple.nontrivial
  have hIleJ : I ≤ Module.jacobson R L := by
    rw [← hMNsup]
    exact le_trans inf_le_left le_sup_left
  have hMleJ : M ≤ Module.jacobson R L := by
    rw [← hMNsup]
    exact le_sup_left
  have hNleJ : N ≤ Module.jacobson R L := by
    rw [← hMNsup]
    exact le_sup_right
  constructor
  · exact
      LocalBiserialBelow.uniserial_submodule_quotient_by_nonzero_radical
        (k := k) e hall Hthin L Hbelow hLtop I M hIne
          hIleJ hMleJ hMtop
  · exact
      LocalBiserialBelow.uniserial_submodule_quotient_by_nonzero_radical
        (k := k) e hall Hthin L Hbelow hLtop I N hIne
          hIleJ hNleJ hNtop

/-- If one branch is still nonuniserial after its quotient by the simple
intersection has become uniserial, it contains a second simple submodule
disjoint from the intersection, as in the final source obstruction. -/
theorem LocalBiserialBelow.exists_simple_branch_complement
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    (hinfSimple : IsSimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L))
    (hMnotuni : ¬ IsUniserialModule Aᵐᵒᵖ M) :
    ∃ S : Submodule Aᵐᵒᵖ L,
      IsSimpleModule Aᵐᵒᵖ S ∧ S ≤ M ∧ S ⊓ (M ⊓ N) = ⊥ ∧
        ¬ Nonempty (S ≃ₗ[Aᵐᵒᵖ] (M ⊓ N : Submodule Aᵐᵒᵖ L)) := by
  let R := Aᵐᵒᵖ
  let I : Submodule R L := M ⊓ N
  let IM : Submodule R M := I.comap M.subtype
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  have hIleM : I ≤ M := inf_le_left
  let eIM : IM ≃ₗ[R] I := Submodule.comapSubtypeEquivOfLe hIleM
  letI : IsSimpleModule R I := hinfSimple
  have hIMsimple : IsSimpleModule R IM := IsSimpleModule.congr eIM
  have hMquot : IsUniserialModule R (M ⧸ IM) :=
    (LocalBiserialBelow.uniserial_branch_quotients_by_simple_inf
      (k := k) e hall Hthin L Hbelow hLtop M N hMNsup
        hMtop hNtop hinfSimple).1
  obtain ⟨S, hSsimple, hSinf⟩ :=
    exists_disjoint_simple_submodule_of_simple_quotient_uniserial
      IM hIMsimple hMquot hMnotuni
  let S' : Submodule R L := S.map M.subtype
  have hS'simple : IsSimpleModule R S' :=
    isSimpleModule_map_of_injective M.subtype M.subtype_injective S hSsimple
  have hS'leM : S' ≤ M := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hImap : IM.map M.subtype = I := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hIleM]
  have hS'inf : S' ⊓ I = ⊥ := by
    change S.map M.subtype ⊓ I = ⊥
    rw [← hImap, ← Submodule.map_inf M.subtype M.subtype_injective,
      hSinf, Submodule.map_bot]
  refine ⟨S', hS'simple, hS'leM, hS'inf, ?_⟩
  exact nonisomorphic_disjoint_simple_submodules_of_simpleTop
    (k := k) e hall Hthin L hLtop S' I hS'simple hS'inf

/-- The two uniserial branch quotients attached to a simple intersection and
an auxiliary disjoint simple force the nonuniserial branch to have length
three. -/
theorem LocalBiserialBelow.branch_jacobson_eq_sup_and_length_eq_three_of_simple_complement
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hinfSimple : IsSimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L))
    (S : Submodule Aᵐᵒᵖ L)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hSleM : S ≤ M) (hSinf : S ⊓ (M ⊓ N) = ⊥) :
    (Module.jacobson Aᵐᵒᵖ M).map M.subtype = (M ⊓ N) ⊔ S ∧
      Module.length Aᵐᵒᵖ M = 3 := by
  let R := Aᵐᵒᵖ
  let I : Submodule R L := M ⊓ N
  let IM : Submodule R M := I.comap M.subtype
  let SM : Submodule R M := S.comap M.subtype
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  letI : Nontrivial (L ⧸ Module.jacobson R L) := hLtop.nontrivial
  letI : Nontrivial L := (Module.jacobson R L).mkQ_surjective.nontrivial
  have hMleJ : M ≤ Module.jacobson R L := by
    rw [← hMNsup]
    exact le_sup_left
  have hIleJ : I ≤ Module.jacobson R L :=
    inf_le_left.trans hMleJ
  have hSne : S ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hSsimple.nontrivial
  have hIne : I ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hinfSimple.nontrivial
  have hMnontrivial : Nontrivial M := by
    letI : Nontrivial (M ⧸ Module.jacobson R M) := hMtop.nontrivial
    exact (Module.jacobson R M).mkQ_surjective.nontrivial
  letI : Nontrivial M := hMnontrivial
  have hMproper : M ≠ ⊤ :=
    (lt_of_le_of_lt hMleJ (Module.jacobson_lt_top R L)).ne
  have hMbis : IsBiserialModule R M :=
    Hbelow (submoduleFGObj L M) (M.length_lt hMproper) hMtop
  have hMthin : IsCoordinateThin (k := k) e (submoduleFGObj L M) :=
    (coordinateThin_of_simpleTop e Hthin L hLtop).submodule M
  have hIleM : I ≤ M := inf_le_left
  let eIM : IM ≃ₗ[R] I := Submodule.comapSubtypeEquivOfLe hIleM
  let eSM : SM ≃ₗ[R] S := Submodule.comapSubtypeEquivOfLe hSleM
  letI : IsSimpleModule R I := hinfSimple
  letI : IsSimpleModule R S := hSsimple
  have hIMsimple : IsSimpleModule R IM := IsSimpleModule.congr eIM
  have hSMsimple : IsSimpleModule R SM := IsSimpleModule.congr eSM
  have hIMmap : IM.map M.subtype = I := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hIleM]
  have hSMmap : SM.map M.subtype = S := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hSleM]
  have hIMSM : IM ⊓ SM = ⊥ := by
    apply Submodule.map_injective_of_injective M.subtype_injective
    rw [Submodule.map_inf M.subtype M.subtype_injective,
      hIMmap, hSMmap, inf_comm, hSinf, Submodule.map_bot]
  have hIMquot : IsUniserialModule R (M ⧸ IM) :=
    LocalBiserialBelow.uniserial_submodule_quotient_by_nonzero_radical
      (k := k) e hall Hthin L Hbelow hLtop I M hIne hIleJ hMleJ hMtop
  have hSMquot : IsUniserialModule R (M ⧸ SM) :=
    LocalBiserialBelow.uniserial_submodule_quotient_by_nonzero_radical
      (k := k) e hall Hthin L Hbelow hLtop S M hSne
        (hSleM.trans hMleJ) hMleJ hMtop
  have hstructure :=
    jacobson_eq_sup_and_length_eq_three_of_biserial_of_disjoint_simple_quotients_uniserial
      (k := k) e hall (submoduleFGObj L M) hMthin hMtop hMbis
        IM SM hIMsimple hSMsimple hIMSM hIMquot hSMquot
  have hradM : Module.jacobson R M = IM ⊔ SM := hstructure.1
  constructor
  · rw [hradM, Submodule.map_sup, hIMmap, hSMmap]
  · exact hstructure.2

/-- Quotienting by the auxiliary simple submodule on one branch embeds the
other branch into a smaller biserial local module, so coordinate-thin branch
placement makes that other branch uniserial. -/
theorem LocalBiserialBelow.other_branch_uniserial_of_simple_complement
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    (S : Submodule Aᵐᵒᵖ L)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hSleM : S ≤ M) (hSinf : S ⊓ (M ⊓ N) = ⊥) :
    IsUniserialModule Aᵐᵒᵖ N := by
  let R := Aᵐᵒᵖ
  have hSleJ : S ≤ Module.jacobson R L := by
    rw [← hMNsup]
    exact hSleM.trans le_sup_left
  have hSne : S ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hSsimple.nontrivial
  have hNleJ : N ≤ Module.jacobson R L := by
    rw [← hMNsup]
    exact le_sup_right
  have hNSinf : N ⊓ S = ⊥ := by
    rw [inf_comm]
    apply le_antisymm
    · rw [← hSinf]
      exact le_inf inf_le_left
        (le_inf (inf_le_left.trans hSleM) inf_le_right)
    · exact bot_le
  let SN : Submodule R N := S.comap N.subtype
  have hSNbot : SN = ⊥ := by
    apply Submodule.map_injective_of_injective N.subtype_injective
    rw [Submodule.map_comap_subtype, hNSinf, Submodule.map_bot]
  have hNquot : IsUniserialModule R (N ⧸ SN) :=
    LocalBiserialBelow.uniserial_submodule_quotient_by_nonzero_radical
      (k := k) e hall Hthin L Hbelow hLtop S N hSne hSleJ hNleJ hNtop
  exact IsUniserialModule.congr (SN.quotEquivOfEqBot hSNbot) hNquot

/-- The two quotients in the final source fiber kernel have nonisomorphic
simple socles.  The long quotient `L/S` has two uniserial radical branches
with the same simple socle, while `L/N` is itself uniserial. -/
theorem LocalBiserialBelow.final_fiberKernel_branch_socles
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hinfSimple : IsSimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L))
    (S : Submodule Aᵐᵒᵖ L)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hSleM : S ≤ M) (hSinf : S ⊓ (M ⊓ N) = ⊥)
    (hNuni : IsUniserialModule Aᵐᵒᵖ N) :
    moduleSocle Aᵐᵒᵖ (quotientFGObj L S) =
        (M ⊓ N).map S.mkQ ∧
      IsUniserialModule Aᵐᵒᵖ (quotientFGObj L N) ∧
      moduleSocle Aᵐᵒᵖ (quotientFGObj L N) = S.map N.mkQ := by
  let R := Aᵐᵒᵖ
  let I : Submodule R L := M ⊓ N
  let Y := quotientFGObj L S
  let Z := quotientFGObj L N
  let MY : Submodule R Y := M.map S.mkQ
  let NY : Submodule R Y := N.map S.mkQ
  let IY : Submodule R Y := I.map S.mkQ
  let MZ : Submodule R Z := M.map N.mkQ
  let SZ : Submodule R Z := S.map N.mkQ
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  have hMleJ : M ≤ Module.jacobson R L := by
    rw [← hMNsup]
    exact le_sup_left
  have hNleJ : N ≤ Module.jacobson R L := by
    rw [← hMNsup]
    exact le_sup_right
  have hSleJ : S ≤ Module.jacobson R L := hSleM.trans hMleJ
  have hIleJ : I ≤ Module.jacobson R L := inf_le_left.trans hMleJ
  have hSne : S ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hSsimple.nontrivial
  have hIne : I ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hinfSimple.nontrivial
  have hNSinf : N ⊓ S = ⊥ := by
    rw [inf_comm]
    apply le_antisymm
    · rw [← hSinf]
      exact le_inf inf_le_left
        (le_inf (inf_le_left.trans hSleM) inf_le_right)
    · exact bot_le
  have hIMquot : IsUniserialModule R
      (M ⧸ I.comap M.subtype) :=
    LocalBiserialBelow.uniserial_submodule_quotient_by_nonzero_radical
      (k := k) e hall Hthin L Hbelow hLtop I M hIne
        hIleJ hMleJ hMtop
  have hSMquot : IsUniserialModule R
      (M ⧸ S.comap M.subtype) :=
    LocalBiserialBelow.uniserial_submodule_quotient_by_nonzero_radical
      (k := k) e hall Hthin L Hbelow hLtop S M hSne
        hSleJ hMleJ hMtop
  have hMYuni : IsUniserialModule R MY :=
    IsUniserialModule.congr (submoduleQuotientLinearEquivMap M S) hSMquot
  have hNYuni : IsUniserialModule R NY :=
    IsUniserialModule.congr
      (submoduleLinearEquivMapQuotientOfInfEqBot N S hNSinf) hNuni
  have hIYsimple : IsSimpleModule R IY :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot
      L S I hSinf hinfSimple
  have hIYleMY : IY ≤ MY := Submodule.map_mono inf_le_left
  have hIYleNY : IY ≤ NY := Submodule.map_mono inf_le_right
  have hMYNY : MY ⊔ NY = Module.jacobson R Y := by
    change M.map S.mkQ ⊔ N.map S.mkQ = Module.jacobson R (L ⧸ S)
    rw [← Submodule.map_sup, hMNsup,
      Module.jacobson_quotient_of_le hSleJ]
  have hYtop : IsSimpleModule R (Y ⧸ Module.jacobson R Y) :=
    isSimpleModule_top_quotient_of_le_jacobson S hSleJ hLtop
  have hYthin : IsCoordinateThin (k := k) e Y :=
    coordinateThin_of_simpleTop e Hthin Y hYtop
  have hYsocle : moduleSocle R Y = IY :=
    moduleSocle_eq_shared_simple_of_coordinateThin_uniserial_branches
      (k := k) e hall Y hYthin hYtop MY NY IY hMYNY
        hMYuni hNYuni hIYsimple hIYleMY hIYleNY
  have hNcomapM : N.comap M.subtype = I.comap M.subtype := by
    ext x
    constructor
    · intro hx
      exact ⟨x.property, hx⟩
    · intro hx
      exact hx.2
  have hMZuni : IsUniserialModule R MZ := by
    have hMNquot : IsUniserialModule R
        (M ⧸ N.comap M.subtype) := by
      rw [hNcomapM]
      exact hIMquot
    exact IsUniserialModule.congr
      (submoduleQuotientLinearEquivMap M N) hMNquot
  have hZrad : Module.jacobson R Z = MZ :=
    IsBiserialModule.jacobson_quotient_eq_map_of_jacobson_eq_sup
      M N hMNsup
  have hZtop : IsSimpleModule R (Z ⧸ Module.jacobson R Z) :=
    isSimpleModule_top_quotient_of_le_jacobson N hNleJ hLtop
  have hZuni : IsUniserialModule R Z := by
    apply IsUniserialModule.of_simpleTop_of_jacobson hZtop
    rw [hZrad]
    exact hMZuni
  have hSZsimple : IsSimpleModule R SZ :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot
      L N S hNSinf hSsimple
  have hZsocle : moduleSocle R Z = SZ :=
    hZuni.moduleSocle_eq_of_simple_submodule SZ hSZsimple
  exact ⟨hYsocle, hZuni, hZsocle⟩

include k in
/-- The element calculation in the final, asymmetric source fiber kernel.
The square of the ring radical sends a lift of the common top to one
nonzero vector in each simple summand of the short branch radical.  Its
action on the short branch itself vanishes, so the discrepancy between the
two lifts is killed after quotienting by the long branch. -/
theorem finalQuotientBranch_hasMixedSocleSmulWitness
    (L : FinitelyGeneratedCategory A)
    (M N S : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMleJ : M ≤ Module.jacobson Aᵐᵒᵖ L)
    (hNleJ : N ≤ Module.jacobson Aᵐᵒᵖ L)
    (hSleM : S ≤ M)
    (hSinf : S ⊓ (M ⊓ N) = ⊥)
    (hinfSimple : IsSimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L))
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hradM : (Module.jacobson Aᵐᵒᵖ M).map M.subtype =
      (M ⊓ N) ⊔ S)
    (hYsocle : moduleSocle Aᵐᵒᵖ (quotientFGObj L S) =
      (M ⊓ N).map S.mkQ)
    (hZsocle : moduleSocle Aᵐᵒᵖ (quotientFGObj L N) =
      S.map N.mkQ)
    (P : Submodule Aᵐᵒᵖ
      (quotientBranchFiberKernelFGObj L S N
        (Module.jacobson Aᵐᵒᵖ L) (sup_le
          (hSleM.trans hMleJ) hNleJ)))
    (houtside : ¬ P ≤ quotientBranchFiberKernelRadicalPreimage L S N
      (Module.jacobson Aᵐᵒᵖ L) (sup_le
        (hSleM.trans hMleJ) hNleJ)) :
    HasMixedSocleSmulWitness
      (quotientFGObj L S) (quotientFGObj L N)
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L))
      (quotientFGMapQ L S (Module.jacobson Aᵐᵒᵖ L)
        (hSleM.trans hMleJ))
      (quotientFGMapQ L N (Module.jacobson Aᵐᵒᵖ L) hNleJ) P := by
  let R := Aᵐᵒᵖ
  let I : Submodule R L := M ⊓ N
  let J := Module.jacobson R L
  let Y := quotientFGObj L S
  let Z := quotientFGObj L N
  let Top := quotientFGObj L J
  let f := quotientFGMapQ L S J (hSleM.trans hMleJ)
  let g := quotientFGMapQ L N J hNleJ
  let j := fiberKernelInclusion Y Z Top f g
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  have hSleJ : S ≤ J := hSleM.trans hMleJ
  have hYjac : Module.jacobson R Y = J.map S.mkQ :=
    Module.jacobson_quotient_of_le hSleJ
  have hZjac : Module.jacobson R Z = J.map N.mkQ :=
    Module.jacobson_quotient_of_le hNleJ
  have hYker : Module.jacobson R Y = f.ker := by
    rw [hYjac]
    exact (quotientFGMapQ_ker L S J hSleJ).symm
  have hZker : Module.jacobson R Z = g.ker := by
    rw [hZjac]
    exact (quotientFGMapQ_ker L N J hNleJ).symm
  obtain ⟨u, huP, huout⟩ := SetLike.not_le_iff_exists.mp houtside
  have huNotBoth : ¬
      ((j u).1 ∈ Module.jacobson R Y ∧
        (j u).2 ∈ Module.jacobson R Z) := by
    change ¬ ((j u).1 ∈ Module.jacobson R Y ∧
      (j u).2 ∈ Module.jacobson R Z) at huout
    exact huout
  have hfiber : f (j u).1 = g (j u).2 := by
    have huKer : fiberKernelMap Y Z Top f g (j u) = 0 :=
      LinearMap.mem_ker.mp
        ((fiberKernelFGObjLinearEquiv Y Z Top f g u).2)
    change f (j u).1 + -g (j u).2 = 0 at huKer
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using huKer
  have huY : (j u).1 ∉ Module.jacobson R Y := by
    intro huY
    apply huNotBoth
    refine ⟨huY, ?_⟩
    rw [hZker]
    apply LinearMap.mem_ker.mpr
    rw [← hfiber]
    exact LinearMap.mem_ker.mp (hYker ▸ huY)
  have huZ : (j u).2 ∉ Module.jacobson R Z := by
    intro huZ
    apply huNotBoth
    refine ⟨?_, huZ⟩
    rw [hYker]
    apply LinearMap.mem_ker.mpr
    rw [hfiber]
    exact LinearMap.mem_ker.mp (hZker ▸ huZ)
  obtain ⟨y, hy⟩ := quotientFGMkQ_surjective L S (j u).1
  obtain ⟨z, hz⟩ := quotientFGMkQ_surjective L N (j u).2
  have hyNotJ : y ∉ J := by
    intro hyJ
    apply huY
    rw [hYjac]
    exact ⟨y, hyJ, hy⟩
  have hyspan : Submodule.span R {y} = ⊤ := by
    by_contra hne
    have hspanJ : Submodule.span R {y} ≤ J :=
      IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hLtop hne
    exact hyNotJ (hspanJ (Submodule.subset_span (Set.mem_singleton y)))
  have hNSinf : N ⊓ S = ⊥ := by
    rw [inf_comm]
    apply le_antisymm
    · rw [← hSinf]
      exact le_inf inf_le_left
        (le_inf (inf_le_left.trans hSleM) inf_le_right)
    · exact bot_le
  letI : Nontrivial I := hinfSimple.nontrivial
  letI : Nontrivial S := hSsimple.nontrivial
  obtain ⟨i, hi⟩ := exists_ne (0 : I)
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  have hiNotS : (i.1 : L) ∉ S := by
    intro hiS
    have hiBot : (i.1 : L) ∈ (⊥ : Submodule R L) := by
      rw [← hSinf]
      exact ⟨hiS, i.2⟩
    apply hi
    apply Subtype.ext
    simpa using hiBot
  have hsNotN : (s.1 : L) ∉ N := by
    intro hsN
    have hsBot : (s.1 : L) ∈ (⊥ : Submodule R L) := by
      rw [← hNSinf]
      exact ⟨hsN, s.2⟩
    apply hs
    apply Subtype.ext
    simpa using hsBot
  have hradMleSquare :
      (Module.jacobson R M).map M.subtype ≤
        Ring.jacobson R ^ 2 • (⊤ : Submodule R L) := by
    rw [moduleJacobson_eq_ringJacobson_smul_top,
      Submodule.map_smul'', Submodule.map_top,
      Submodule.range_subtype]
    have hMaction : M ≤ Ring.jacobson R • (⊤ : Submodule R L) := by
      rw [← moduleJacobson_eq_ringJacobson_smul_top]
      exact hMleJ
    have hpow : Ring.jacobson R ^ 2 =
        Ring.jacobson R * Ring.jacobson R := by
      calc
        Ring.jacobson R ^ 2 =
            Ring.jacobson R * Ring.jacobson R ^ 1 :=
          Ideal.IsTwoSided.pow_succ (I := Ring.jacobson R) 1
        _ = Ring.jacobson R * Ring.jacobson R := by
          rw [Submodule.pow_one]
    rw [hpow, Submodule.mul_smul]
    exact smul_mono_right (Ring.jacobson R) hMaction
  have hisRadM : (i.1 : L) + s.1 ∈
      (Module.jacobson R M).map M.subtype := by
    rw [hradM]
    exact (I ⊔ S).add_mem
      ((show I ≤ I ⊔ S from le_sup_left) i.2)
      ((show S ≤ I ⊔ S from le_sup_right) s.2)
  have hisSquare : (i.1 : L) + s.1 ∈
      Ring.jacobson R ^ 2 • (⊤ : Submodule R L) :=
    hradMleSquare hisRadM
  have hisSpan : (i.1 : L) + s.1 ∈
      Ring.jacobson R ^ 2 • Submodule.span R {y} := by
    rw [hyspan]
    exact hisSquare
  obtain ⟨r, hr, hry⟩ :=
    Submodule.mem_smul_span_singleton.mp hisSpan
  let IM : Submodule R M := I.comap M.subtype
  let SM : Submodule R M := S.comap M.subtype
  have hIleM : I ≤ M := inf_le_left
  let eIM : IM ≃ₗ[R] I := Submodule.comapSubtypeEquivOfLe hIleM
  let eSM : SM ≃ₗ[R] S := Submodule.comapSubtypeEquivOfLe hSleM
  have hIMsimple : IsSimpleModule R IM :=
    IsSimpleModule.congr eIM
  have hSMsimple : IsSimpleModule R SM :=
    IsSimpleModule.congr eSM
  have hIMmap : IM.map M.subtype = I := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hIleM]
  have hSMmap : SM.map M.subtype = S := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hSleM]
  have hradMintrinsic : Module.jacobson R M = IM ⊔ SM := by
    apply Submodule.map_injective_of_injective M.subtype_injective
    rw [hradM, Submodule.map_sup, hIMmap, hSMmap]
  letI : IsSimpleModule R IM := hIMsimple
  letI : IsSimpleModule R SM := hSMsimple
  letI : IsSemisimpleModule R ↥(IM ⊔ SM : Submodule R M) :=
    IsSemisimpleModule.sup (R := R) inferInstance inferInstance
  have hradMsemisimple :
      IsSemisimpleModule R (Module.jacobson R M) := by
    rw [hradMintrinsic]
    infer_instance
  letI : IsSemisimpleModule R (Module.jacobson R M) :=
    hradMsemisimple
  have hJJMbot : Module.jacobson R (Module.jacobson R M) = ⊥ :=
    IsSemisimpleModule.jacobson_eq_bot R (Module.jacobson R M)
  have hradSqKillsM : Ring.jacobson R ^ 2 •
      (⊤ : Submodule R M) = ⊥ := by
    rw [← map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top,
      hJJMbot, Submodule.map_bot]
  have htopEq : quotientFGMkQ L J y = quotientFGMkQ L J z := by
    calc
      quotientFGMkQ L J y = f (quotientFGMkQ L S y) := by
        exact (quotientFGMapQ_apply_mkQ L S J hSleJ y).symm
      _ = f (j u).1 := by rw [hy]
      _ = g (j u).2 := hfiber
      _ = g (quotientFGMkQ L N z) := by rw [hz]
      _ = quotientFGMkQ L J z := by
        exact quotientFGMapQ_apply_mkQ L N J hNleJ z
  have hydiff : y - z ∈ J := by
    change J.mkQ y = J.mkQ z at htopEq
    rw [← J.ker_mkQ]
    apply LinearMap.mem_ker.mpr
    rw [map_sub, htopEq, sub_self]
  have hydiffMN : y - z ∈ M ⊔ N := hMNsup.symm ▸ hydiff
  obtain ⟨m, hm, n, hn, hmn⟩ := Submodule.mem_sup.mp hydiffMN
  let mM : M := ⟨m, hm⟩
  have hrmMem : r • mM ∈
      Ring.jacobson R ^ 2 • (⊤ : Submodule R M) :=
    Submodule.smul_mem_smul hr Submodule.mem_top
  have hrmM : r • mM = 0 := by
    rw [hradSqKillsM] at hrmMem
    simpa using hrmMem
  have hrm : r • m = 0 := congrArg Subtype.val hrmM
  have hrdiffN : r • (y - z) ∈ N := by
    rw [← hmn, smul_add, hrm, zero_add]
    exact N.smul_mem r hn
  have hryzQuot : N.mkQ (r • y) = N.mkQ (r • z) := by
    apply sub_eq_zero.mp
    rw [← map_sub, ← smul_sub]
    exact (Submodule.Quotient.mk_eq_zero N).mpr hrdiffN
  have hleft : r • (j u).1 = quotientFGMkQ L S i.1 := by
    rw [← hy, ← (quotientFGMkQ L S).map_smul, hry]
    rw [(quotientFGMkQ L S).map_add]
    have hsQuot : quotientFGMkQ L S s.1 = 0 := by
      change S.mkQ s.1 = 0
      exact (Submodule.Quotient.mk_eq_zero S).mpr s.2
    rw [hsQuot, add_zero]
  have hright : r • (j u).2 = quotientFGMkQ L N s.1 := by
    rw [← hz, ← (quotientFGMkQ L N).map_smul]
    calc
      quotientFGMkQ L N (r • z) =
          quotientFGMkQ L N (r • y) := hryzQuot.symm
      _ = quotientFGMkQ L N ((i.1 : L) + s.1) := by rw [hry]
      _ = quotientFGMkQ L N s.1 := by
        rw [(quotientFGMkQ L N).map_add]
        have hiQuot : quotientFGMkQ L N i.1 = 0 := by
          change N.mkQ i.1 = 0
          exact (Submodule.Quotient.mk_eq_zero N).mpr i.2.2
        rw [hiQuot, zero_add]
  have hleftNe : r • (j u).1 ≠ 0 := by
    rw [hleft]
    intro hzero
    apply hiNotS
    change S.mkQ i.1 = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero S).mp hzero
  have hrightNe : r • (j u).2 ≠ 0 := by
    rw [hright]
    intro hzero
    apply hsNotN
    change N.mkQ s.1 = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero N).mp hzero
  refine ⟨u, r, huP, hleftNe, hrightNe, ?_, ?_⟩
  · rw [hleft, hYsocle]
    exact ⟨i.1, i.2, rfl⟩
  · rw [hright, hZsocle]
    exact ⟨s.1, s.2, rfl⟩

/-- The final asymmetric fiber kernel is simultaneously indecomposable and
forbidden by coordinate thinness.  Indecomposability uses its two
nonisomorphic coordinate socles and the mixed-vector calculation; the
opposite conclusion uses the two copies of the short branch top. -/
theorem LocalBiserialBelow.false_of_simple_complement
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hinfSimple : IsSimpleModule Aᵐᵒᵖ
      ↥( M ⊓ N : Submodule Aᵐᵒᵖ L))
    (S : Submodule Aᵐᵒᵖ L)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hSleM : S ≤ M) (hSinf : S ⊓ (M ⊓ N) = ⊥)
    (hSInoniso : ¬ Nonempty
      (S ≃ₗ[Aᵐᵒᵖ] (M ⊓ N : Submodule Aᵐᵒᵖ L)))
    (hNuni : IsUniserialModule Aᵐᵒᵖ N) :
    False := by
  let R := Aᵐᵒᵖ
  let I : Submodule R L := M ⊓ N
  let J := Module.jacobson R L
  have hMleJ : M ≤ J := by
    change M ≤ Module.jacobson Aᵐᵒᵖ L
    rw [← hMNsup]
    exact le_sup_left
  have hNleJ : N ≤ J := by
    change N ≤ Module.jacobson Aᵐᵒᵖ L
    rw [← hMNsup]
    exact le_sup_right
  have hSleJ : S ≤ J := hSleM.trans hMleJ
  have hSNJ : S ⊔ N ≤ J := sup_le hSleJ hNleJ
  have hNSinf : N ⊓ S = ⊥ := by
    rw [inf_comm]
    apply le_antisymm
    · rw [← hSinf]
      exact le_inf inf_le_left
        (le_inf (inf_le_left.trans hSleM) inf_le_right)
    · exact bot_le
  have hISinf : I ⊓ S = ⊥ := by
    change (M ⊓ N) ⊓ S = ⊥
    rw [inf_comm, hSinf]
  have hstructure :=
    LocalBiserialBelow.branch_jacobson_eq_sup_and_length_eq_three_of_simple_complement
      (k := k) e hall Hthin L Hbelow hLtop M N hMNsup hMtop
        hinfSimple S hSsimple hSleM hSinf
  have hradM : (Module.jacobson R M).map M.subtype = I ⊔ S :=
    hstructure.1
  obtain ⟨hYsocle, hZuni, hZsocle⟩ :=
    LocalBiserialBelow.final_fiberKernel_branch_socles
      (k := k) e hall Hthin L Hbelow hLtop M N hMNsup hMtop
        hinfSimple S hSsimple hSleM hSinf hNuni
  let Y := quotientFGObj L S
  let Z := quotientFGObj L N
  let Top := quotientFGObj L J
  let f := quotientFGMapQ L S J hSleJ
  let g := quotientFGMapQ L N J hNleJ
  let W := fiberKernelFGObj Y Z Top f g
  have hIYsimple : IsSimpleModule R (I.map S.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot
      L S I (by simpa [inf_comm] using hSinf) hinfSimple
  have hSZsimple : IsSimpleModule R (S.map N.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot
      L N S hNSinf hSsimple
  have hYsocleSimple : IsSimpleModule R (moduleSocle R Y) := by
    rw [hYsocle]
    exact hIYsimple
  have hZsocleSimple : IsSimpleModule R (moduleSocle R Z) := by
    rw [hZsocle]
    exact hSZsimple
  let eIY : I ≃ₗ[R] moduleSocle R Y :=
    (submoduleLinearEquivMapQuotientOfInfEqBot I S hISinf).trans
        (LinearEquiv.ofEq _ _ hYsocle.symm)
  let eSZ : S ≃ₗ[R] moduleSocle R Z :=
    (submoduleLinearEquivMapQuotientOfInfEqBot S N
      (by simpa [inf_comm] using hNSinf)).trans
        (LinearEquiv.ofEq _ _ hZsocle.symm)
  have hSocleNoniso : ¬ Nonempty
      (moduleSocle R Y ≃ₗ[R] moduleSocle R Z) := by
    rintro ⟨q⟩
    apply hSInoniso
    exact ⟨eSZ.trans (q.symm.trans eIY.symm)⟩
  have hYkill : moduleSocle R Y ≤ f.ker := by
    rw [hYsocle, quotientFGMapQ_ker]
    exact Submodule.map_mono (inf_le_left.trans hMleJ)
  have hZkill : moduleSocle R Z ≤ g.ker := by
    rw [hZsocle, quotientFGMapQ_ker]
    exact Submodule.map_mono hSleJ
  have hYrad : Module.jacobson R Y ≤ f.ker := by
    have hYjac : Module.jacobson R Y = J.map S.mkQ :=
      Module.jacobson_quotient_of_le hSleJ
    rw [hYjac, quotientFGMapQ_ker]
  letI : Nontrivial Top := hLtop.nontrivial
  have hind : Indecomposable W := by
    apply fiberKernel_indec_of_mixed_outside_radicalPreimage
      (k := k) Y Z Top f g
      (quotientFGMapQ_surjective L S J hSleJ)
      (quotientFGMapQ_surjective L N J hNleJ)
      hYsocleSimple hZsocleSimple hSocleNoniso
      hYkill hZkill hYrad
    intro P hPoutside
    apply hasMixedSocleCoordinates_of_smulWitness Y Z Top f g P
    exact finalQuotientBranch_hasMixedSocleSmulWitness
      (k := k) L M N S hMNsup hMleJ hNleJ hSleM hSinf
        hinfSimple hSsimple hLtop hradM hYsocle hZsocle P hPoutside
  let IM : Submodule R M := I.comap M.subtype
  let SM : Submodule R M := S.comap M.subtype
  have hIleM : I ≤ M := inf_le_left
  have hIMmap : IM.map M.subtype = I := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hIleM]
  have hSMmap : SM.map M.subtype = S := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hSleM]
  have hradMintrinsic : Module.jacobson R M = IM ⊔ SM := by
    apply Submodule.map_injective_of_injective M.subtype_injective
    rw [hradM, Submodule.map_sup, hIMmap, hSMmap]
  have hSMleRad : S.comap M.subtype ≤ Module.jacobson R M := by
    change SM ≤ Module.jacobson R M
    rw [hradMintrinsic]
    exact le_sup_right
  have hNMleRad : N.comap M.subtype ≤ Module.jacobson R M := by
    rw [hradMintrinsic]
    intro x hxN
    exact (show IM ≤ IM ⊔ SM from le_sup_left) ⟨x.property, hxN⟩
  let PY : Submodule R Y := M.map S.mkQ
  let PZ : Submodule R Z := M.map N.mkQ
  let QY : Submodule R PY := Module.jacobson R PY
  let QZ : Submodule R PZ := Module.jacobson R PZ
  let F := quotientFGObj (submoduleFGObj L M) (Module.jacobson R M)
  letI : Nontrivial F := hMtop.nontrivial
  let eY : (PY ⧸ QY) ≃ₗ[R] F :=
    moduleTopOfMappedSubmoduleQuotientLinearEquiv M S hSMleRad
  let eZ : (PZ ⧸ QZ) ≃ₗ[R] F :=
    moduleTopOfMappedSubmoduleQuotientLinearEquiv M N hNMleRad
  have hPY : PY ≤ f.ker := by
    rw [quotientFGMapQ_ker]
    exact Submodule.map_mono hMleJ
  have hPZ : PZ ≤ g.ker := by
    rw [quotientFGMapQ_ker]
    exact Submodule.map_mono hMleJ
  have hnot : ¬ Indecomposable W :=
    not_indec_fiberKernel_of_all_coordinateThin
      (k := k) e hall Hthin Y Z Top F f g
        PY PZ hPY hPZ QY QZ eY eZ
  exact hnot hind

/-- The final fiber-kernel contradiction rules out a nonuniserial left
branch once the two spanning radical branches have simple intersection. -/
theorem LocalBiserialBelow.left_branch_uniserial_of_simple_inf
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    (hinfSimple : IsSimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)) :
    IsUniserialModule Aᵐᵒᵖ M := by
  by_contra hMnotuni
  obtain ⟨S, hSsimple, hSleM, hSinf, hSnoniso⟩ :=
    LocalBiserialBelow.exists_simple_branch_complement
      (k := k) e hall Hthin L Hbelow hLtop M N hMNsup
        hMtop hNtop hinfSimple hMnotuni
  have hNuni : IsUniserialModule Aᵐᵒᵖ N :=
    LocalBiserialBelow.other_branch_uniserial_of_simple_complement
      (k := k) e hall Hthin L Hbelow hLtop M N hMNsup hNtop
        S hSsimple hSleM hSinf
  exact LocalBiserialBelow.false_of_simple_complement
    (k := k) e hall Hthin L Hbelow hLtop M N hMNsup hMtop
      hinfSimple S hSsimple hSleM hSinf hSnoniso hNuni

/-- With simple nonzero intersection, both spanning radical branches are
uniserial.  The second conclusion is the first after interchanging the two
branches. -/
theorem LocalBiserialBelow.branches_uniserial_of_simple_inf
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (M N : Submodule Aᵐᵒᵖ L)
    (hMNsup : M ⊔ N = Module.jacobson Aᵐᵒᵖ L)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    (hinfSimple : IsSimpleModule Aᵐᵒᵖ
      ↥(M ⊓ N : Submodule Aᵐᵒᵖ L)) :
    IsUniserialModule Aᵐᵒᵖ M ∧
      IsUniserialModule Aᵐᵒᵖ N := by
  constructor
  · exact LocalBiserialBelow.left_branch_uniserial_of_simple_inf
      (k := k) e hall Hthin L Hbelow hLtop M N hMNsup
        hMtop hNtop hinfSimple
  · have hinfSimple' : IsSimpleModule Aᵐᵒᵖ
        ↥(N ⊓ M : Submodule Aᵐᵒᵖ L) := by
      letI : IsSimpleModule Aᵐᵒᵖ
          ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) := hinfSimple
      exact IsSimpleModule.congr
        (LinearEquiv.ofEq _ _ (inf_comm N M))
    exact LocalBiserialBelow.left_branch_uniserial_of_simple_inf
      (k := k) e hall Hthin L Hbelow hLtop N M
        (by simpa [sup_comm] using hMNsup) hNtop hMtop hinfSimple'

/-- The nonzero radical-square branch of the local induction is complete:
the radical-top construction supplies two local branches spanning the
radical.  If they are disjoint, induction makes both uniserial directly; if
they meet, the intersection obstruction makes the intersection simple and
the final fiber-kernel obstruction makes both branches uniserial. -/
theorem LocalBiserialBelow.biserial_of_radicalSquare_ne_bot
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hLnotuni : ¬ IsUniserialModule Aᵐᵒᵖ L)
    (hradicalSquare : radicalSquareSubmodule L ≠ ⊥) :
    IsBiserialModule Aᵐᵒᵖ L := by
  obtain ⟨M, N, hMNsup, -, -, hMtop, hNtop, hMNtop, -⟩ :=
    LocalBiserialBelow.exists_spanning_nonisomorphic_local_jacobson_submodules_of_radicalSquare_ne_bot
      (k := k) e hall Hthin L Hbelow hLtop hLnotuni hradicalSquare
  by_cases hinf : M ⊓ N = ⊥
  · obtain ⟨hMuni, hNuni⟩ :=
      LocalBiserialBelow.uniserial_branches_of_disjoint_spanning_jacobson
        (k := k) L Hbelow hLtop M N hMNsup hinf hMtop hNtop
    exact ⟨M, N, hMNsup, hMuni, hNuni,
      Or.inl (hinf.symm ▸ inferInstance)⟩
  · have hinfSimple : IsSimpleModule Aᵐᵒᵖ
        ↥(M ⊓ N : Submodule Aᵐᵒᵖ L) :=
      LocalBiserialBelow.simple_inf
        (k := k) e hall Hthin L Hbelow hLtop hLnotuni M N
          hMNsup hMtop hNtop hMNtop hinf
    obtain ⟨hMuni, hNuni⟩ :=
      LocalBiserialBelow.branches_uniserial_of_simple_inf
        (k := k) e hall Hthin L Hbelow hLtop M N hMNsup
          hMtop hNtop hinfSimple
    exact ⟨M, N, hMNsup, hMuni, hNuni, Or.inr hinfSimple⟩

include k in
/-- In the square-zero branch, the only remaining input needed for
biseriality is the length bound on the radical.  Square-zero makes the
radical semisimple, and a semisimple radical of length at most two splits
into at most two simple (hence uniserial) summands. -/
theorem biserial_of_radicalSquare_eq_bot_of_jacobson_length_le_two
    (L : FinitelyGeneratedCategory A)
    (hradicalSquare : radicalSquareSubmodule L = ⊥)
    (hlength : Module.length Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L) ≤ 2) :
    IsBiserialModule Aᵐᵒᵖ L := by
  let R := Aᵐᵒᵖ
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  let J : Submodule R L := Module.jacobson R L
  have hfiniteLength : IsFiniteLength R L :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) L
  letI : IsArtinian R L :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  have hJrad : Module.jacobson R J = ⊥ := by
    apply Submodule.map_injective_of_injective J.subtype_injective
    rw [map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top,
      show Ring.jacobson R ^ 2 • (⊤ : Submodule R L) = ⊥ from
        hradicalSquare,
      Submodule.map_bot]
  letI : IsSemisimpleModule R J :=
    (IsArtinian.isSemisimpleModule_iff_jacobson R J).mpr hJrad
  exact IsBiserialModule.of_semisimple_jacobson_length_le_two hlength

/-- The radical-square-zero branch of the local induction.  The radical is
semisimple, while the `D₄` obstruction bounds its length by two. -/
theorem biserial_of_radicalSquare_eq_bot
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)))
    (hradicalSquare : radicalSquareSubmodule L = ⊥) :
    IsBiserialModule Aᵐᵒᵖ L := by
  let R := Aᵐᵒᵖ
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  let J : Submodule R L := Module.jacobson R L
  have hfiniteLength : IsFiniteLength R L :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) L
  letI : IsArtinian R L :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  have hJrad : Module.jacobson R J = ⊥ := by
    apply Submodule.map_injective_of_injective J.subtype_injective
    rw [map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top,
      show Ring.jacobson R ^ 2 • (⊤ : Submodule R L) = ⊥ from
        hradicalSquare,
      Submodule.map_bot]
  letI : IsSemisimpleModule R J :=
    (IsArtinian.isSemisimpleModule_iff_jacobson R J).mpr hJrad
  have hlength : Module.length R J ≤ 2 :=
    jacobson_length_le_two_of_semisimple_of_all_coordinateThin
      (k := k) e hall Hthin L hLtop
  exact biserial_of_radicalSquare_eq_bot_of_jacobson_length_le_two
    (k := k) L hradicalSquare hlength

/-- One local step of the direct biserial induction. -/
theorem LocalBiserialBelow.biserial
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (Hbelow : LocalBiserialBelow (A := A) (Module.length Aᵐᵒᵖ L))
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L))) :
    IsBiserialModule Aᵐᵒᵖ L := by
  by_cases hLuni : IsUniserialModule Aᵐᵒᵖ L
  · exact IsBiserialModule.of_uniserial hLuni
  · by_cases hradicalSquare : radicalSquareSubmodule L = ⊥
    · exact biserial_of_radicalSquare_eq_bot
        (k := k) e hall Hthin L hLtop hradicalSquare
    · exact LocalBiserialBelow.biserial_of_radicalSquare_ne_bot
        (k := k) e hall Hthin L Hbelow hLtop hLuni hradicalSquare

/-- Direct Pogorzały--Skowroński biserial induction: under a complete
coordinate family, if every indecomposable finitely generated module is
coordinate-thin, then every finitely generated module with simple top is
biserial. -/
theorem isBiserialModule_of_simpleTop_of_allIndecomposablesCoordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L))) :
    IsBiserialModule Aᵐᵒᵖ L := by
  let P : ℕ∞ → Prop := fun n ↦
    ∀ W : FinitelyGeneratedCategory A,
      Module.length Aᵐᵒᵖ W = n →
        IsSimpleModule Aᵐᵒᵖ
          (quotientFGObj W (Module.jacobson Aᵐᵒᵖ W)) →
        IsBiserialModule Aᵐᵒᵖ W
  have hP : ∀ n : ℕ∞, P n := by
    intro n
    induction n using WellFoundedLT.induction with
    | ind n ih =>
        intro W hWlength hWtop
        apply LocalBiserialBelow.biserial
          (k := k) e hall Hthin W _ hWtop
        intro X hXlength hXtop
        exact ih (Module.length Aᵐᵒᵖ X)
          (by simpa [hWlength] using hXlength)
          X rfl hXtop
  exact hP (Module.length Aᵐᵒᵖ L) L rfl hLtop

include k in
/-- A primitive principal right projective has simple top. -/
theorem PrimitiveIdempotentData.rightIdeal_top_isSimple
    {p : A} (D : PrimitiveIdempotentData p) :
    IsSimpleModule Aᵐᵒᵖ
      (rightIdealFGObj p ⧸
        Module.jacobson Aᵐᵒᵖ (rightIdealFGObj p)) := by
  let P := rightIdealFGObj p
  have hlength : IsFiniteLength Aᵐᵒᵖ P :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) P
  letI : Nontrivial P := (rightIdeal_isIndecomposableModule D).nontrivial
  letI : Module.Projective Aᵐᵒᵖ P :=
    rightIdeal_moduleProjective D.idempotent
  letI : IsLocalRing (Module.End Aᵐᵒᵖ P) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable
      hlength (rightIdeal_isIndecomposableModule D)
  apply isSimpleModule_iff_isCoatom.mpr
  exact jacobson_isCoatom_of_projective_local_end

/-- Every primitive principal right projective is biserial when all
indecomposable right modules are coordinate-thin. -/
theorem PrimitiveIdempotentData.rightIdeal_isBiserial_of_allIndecomposablesCoordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    {p : A} (D : PrimitiveIdempotentData p) :
    IsBiserialModule Aᵐᵒᵖ (rightIdealFGObj p) := by
  let P := rightIdealFGObj p
  have htop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P) :=
    D.rightIdeal_top_isSimple (k := k)
  exact isBiserialModule_of_simpleTop_of_allIndecomposablesCoordinateThin
    (k := k) e hall Hthin P htop

end MagnitudeConjecture.RightModule
