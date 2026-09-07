import MagnitudeConjecture.Algebra.RightModuleBoundaryGenerator
import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.RightModuleNakayamaARIdentification
import QuotientSubmoduleEquidistribution.CategoryTheory.CategoricalRadicalIdeal
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaLadderRadical

/-!
# Presentations from directed factor meshes

This file constructs the finite `add(U)` presentations required by the
minimal-realization argument.  The induction is over the ambient directed
order.  Tau-projective labels are coordinates of `U`; at every other label,
the compatible right mesh is a weak-cokernel pair whose middle summands and
left boundary strictly precede the endpoint.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open QuotientSubmoduleEquidistribution.Iyama
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Every tau-projective selected object is a coordinate retract of the
boundary generator. -/
theorem factorProjectiveObject_finiteAddClosure
    {K : Set (Fin S.n)}
    (p : S.FactorProjectiveLabel K) :
    finiteAddClosure (S.factorProjectiveGenerator K)
      (S.factorObject K p.1) := by
  let F : S.FactorProjectiveLabel K → S.FactorCategory K :=
    fun q ↦ S.factorObject K q.1
  let r : Retract (S.factorObject K p.1)
      (S.factorProjectiveGenerator K) :=
    { i := biproduct.ι F p
      r := biproduct.π F p
      retract := biproduct.ι_π_self F p }
  exact ⟨{
    n := 1
    retract := r.trans
      (Retract.ofIso
        (biproductUniqueIso
          (fun _ : Fin 1 ↦ S.factorProjectiveGenerator K)).symm) }⟩

/-- A nonprojective factor right mesh is a weak-cokernel pair, by transport
from its compatible left mesh. -/
theorem factorRightMesh_isWeakCokernel_of_nonprojective
    {K : Set (Fin S.n)} (x : S.SurvivingLabel K)
    (hx : ¬ (S.factorFiniteTauCategoryData K).IsProjective x) :
    ShortComplex.IsWeakCokernel
      ((S.factorFiniteTauCategoryData K).rightMesh
        ((S.factorFiniteTauCategoryData K).obj x)) := by
  let T := S.factorFiniteTauCategoryData K
  let X : T.Nonprojective := ⟨x, hx⟩
  exact
    ((T.leftTau (T.obj (T.tauPlus X))).minimalWeakCokernel.1).of_iso
      (T.rightLeftMeshIso X).symm

/-- Restricted positive translation strictly precedes its nonprojective
factor endpoint in the ambient directed order. -/
theorem factorTauPlus_strictly_precedes
    {K : Set (Fin S.n)}
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : S.SurvivingLabel K)
    (hx : ¬ (S.factorFiniteTauCategoryData K).IsProjective x) :
    (S.directedLinearOrder H).lt
      ((S.factorFiniteTauCategoryData K).tauPlus ⟨x, hx⟩).1 x.1 := by
  let X : {x : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorRightMesh K
          (S.factorObject K x)).X₁} := ⟨x, hx⟩
  obtain ⟨z, hz, htranslate⟩ :=
    S.factorRightBoundaryToLeft_val K X
  have hlt := S.rightTranslation_strictly_precedes H z
  change (S.directedLinearOrder H).lt
    (S.factorRightBoundaryToLeft K X).1.1 x.1
  rw [htranslate, ← hz]
  exact hlt

/-- Every indecomposable summand in a chosen decomposition of the middle of
a nonprojective factor right mesh strictly precedes its endpoint. -/
theorem factorRightMiddle_label_strictly_precedes
    {K : Set (Fin S.n)}
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : S.SurvivingLabel K)
    (hx : ¬ (S.factorFiniteTauCategoryData K).IsProjective x)
    {n : ℕ} (label : Fin n → S.SurvivingLabel K)
    (e : (S.factorFiniteTauCategoryData K).thetaPlus x ≅
      ⨁ fun i ↦
        (S.factorFiniteTauCategoryData K).obj (label i))
    (t : Fin n) :
    (S.directedLinearOrder H).lt (label t).1 x.1 := by
  let T := S.factorFiniteTauCategoryData K
  let R := T.rightMesh (T.obj x)
  let F : Fin n → S.FactorCategory K :=
    fun i ↦ T.obj (label i)
  let inc : F t ⟶ R.X₂ := biproduct.ι F t ≫ e.inv
  let proj : R.X₂ ⟶ F t := e.hom ≫ biproduct.π F t
  have hincproj : inc ≫ proj = 𝟙 (F t) := by
    simp [inc, proj, Category.assoc]
  have hcomponent : inc ≫ R.g ≠ 0 := by
    intro hzero
    let d : R.X₂ ⟶ R.X₂ := 𝟙 R.X₂ - proj ≫ inc
    have hfix : d ≫ R.g = R.g := by
      dsimp only [d]
      rw [Preadditive.sub_comp, Category.id_comp,
        Category.assoc, hzero, comp_zero, sub_zero]
    letI : IsIso d := (T.rightTau (T.obj x)).isRightMinimal_g d hfix
    have hinczero : inc = 0 := by
      apply (cancel_mono d).1
      dsimp only [d]
      simp only [Preadditive.comp_sub, Category.comp_id,
        zero_comp]
      rw [← Category.assoc, hincproj, Category.id_comp,
        sub_self]
      simp
    apply S.factorObject_not_isZero K (label t)
    rw [IsZero.iff_id_eq_zero]
    have hid : 𝟙 (F t) = 0 := by
      rw [← hincproj, hinczero, zero_comp]
    change 𝟙 (S.factorObject K (label t)) = 0 at hid
    exact hid
  let c : T.obj (label t) ⟶ T.obj x :=
    inc ≫ R.g ≫ (T.rightTermIso (T.obj x)).hom
  have hc : c ≠ 0 := by
    intro hzero
    apply hcomponent
    apply (cancel_mono (T.rightTermIso (T.obj x)).hom).1
    simpa [c, Category.assoc] using hzero
  have hcRad : IsRadicalMorphism c := by
    dsimp only [c]
    simpa only [Category.assoc] using
      isRadicalMorphism_postcomp (T.rightTermIso (T.obj x)).hom
        (isRadicalMorphism_precomp inc
          (T.rightTau (T.obj x)).g_radical)
  let Q := S.factorFunctor K
  obtain ⟨a, ha⟩ := Q.map_surjective c
  have ha0 : a.hom ≠ 0 := by
    intro hzero
    apply hc
    rw [← ha]
    have haZero : a = 0 := by
      apply ObjectProperty.hom_ext
      exact hzero
    rw [haZero, Q.map_zero]
    rfl
  by_cases hlabel : (label t).1 = x.1
  · have hlabel' : label t = x := Subtype.ext hlabel
    subst x
    haveI : IsIso a.hom :=
      H.isIso_of_ne_zero_endomorphism S (label t).1 a.hom ha0
    haveI : IsIso a :=
      (ObjectProperty.isIso_hom_iff a).mp inferInstance
    let hsplit : IsSplitEpi (Q.map a) := inferInstance
    rw [← ha] at hcRad
    exfalso
    exact ((T.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (Q.map a)).1 hcRad) hsplit
  · exact S.directedLinearOrder_hom_lt H a.hom ha0 hlabel

/-- Every map from the tau-projective boundary generator into the right
endpoint at a nonprojective label is radical. -/
theorem factorProjectiveGenerator_map_rightEndpoint_isRadical
    {K : Set (Fin S.n)}
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : S.SurvivingLabel K)
    (hx : ¬ (S.factorFiniteTauCategoryData K).IsProjective x)
    (a : S.factorProjectiveGenerator K ⟶
      ((S.factorFiniteTauCategoryData K).rightMesh
        ((S.factorFiniteTauCategoryData K).obj x)).X₃) :
    IsRadicalMorphism a := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let R := T.rightMesh (T.obj x)
  let U := S.factorProjectiveGenerator K
  let F : S.FactorProjectiveLabel K → S.FactorCategory K :=
    fun p ↦ T.obj p.1
  have hcomponent (p : S.FactorProjectiveLabel K) :
      IsRadicalMorphism (biproduct.ι F p ≫ a) := by
    let b : T.obj p.1 ⟶ T.obj x :=
      biproduct.ι F p ≫ a ≫ (T.rightTermIso (T.obj x)).hom
    have hbRad : IsRadicalMorphism b := by
      apply (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj b).2
      intro hsplit
      letI : IsSplitEpi b := hsplit
      let s : T.obj x ⟶ T.obj p.1 := section_ b
      have hb0 : b ≠ 0 := by
        intro hb
        apply S.factorObject_not_isZero K x
        rw [IsZero.iff_id_eq_zero]
        have hid : 𝟙 (T.obj x) = 0 := calc
          𝟙 (T.obj x) = s ≫ b := (IsSplitEpi.id b).symm
          _ = 0 := by rw [hb, comp_zero]
        change 𝟙 (S.factorObject K x) = 0 at hid
        exact hid
      have hs0 : s ≠ 0 := by
        intro hs
        apply S.factorObject_not_isZero K x
        rw [IsZero.iff_id_eq_zero]
        have hid : 𝟙 (T.obj x) = 0 := calc
          𝟙 (T.obj x) = s ≫ b := (IsSplitEpi.id b).symm
          _ = 0 := by rw [hs, zero_comp]
        change 𝟙 (S.factorObject K x) = 0 at hid
        exact hid
      have hpx : p.1 = x :=
        H.factorObject_label_eq_of_two_way S K p.1 x
          b hb0 s hs0
      apply hx
      simpa [hpx] using p.2
    have hback :=
      isRadicalMorphism_postcomp
        (T.rightTermIso (T.obj x)).inv hbRad
    dsimp only [b] at hback
    simpa only [Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
      using hback
  have hsumRad : IsRadicalMorphism
      (∑ p : S.FactorProjectiveLabel K,
        biproduct.π F p ≫ (biproduct.ι F p ≫ a)) := by
    exact ((CategoricalRadical.homIdeal.hom U R.X₃).sum_mem
      (fun p _ ↦
        isRadicalMorphism_precomp (biproduct.π F p)
          (hcomponent p)))
  have hsum :
      (∑ p : S.FactorProjectiveLabel K,
        biproduct.π F p ≫ (biproduct.ι F p ≫ a)) = a := by
    calc
      _ = (∑ p : S.FactorProjectiveLabel K,
          biproduct.π F p ≫ biproduct.ι F p) ≫ a := by
        simp only [Preadditive.sum_comp, Category.assoc]
      _ = a := by rw [biproduct.total, Category.id_comp]
  rw [hsum] at hsumRad
  exact hsumRad

/-- Every surviving indecomposable factor object has a finite presentation
by the tau-projective boundary generator. -/
theorem factorObject_finiteAddGeneratorPresentation
    {K : Set (Fin S.n)}
    (D : S.PrimitiveMultiplicityInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : S.SurvivingLabel K) :
    Nonempty
      (FiniteAddGeneratorPresentation
        (S.factorProjectiveGenerator K) (S.factorObject K x)) := by
  let O := S.directedLinearOrder H
  have hwell : WellFounded O.lt := by
    letI : LinearOrder (Fin S.n) := O
    exact Finite.wellFounded_of_trans_of_irrefl O.lt
  let U := S.factorProjectiveGenerator K
  let T := S.factorFiniteTauCategoryData K
  let P : Fin S.n → Prop := fun i ↦
    ∀ hi : i ∉ K,
      Nonempty
        (FiniteAddGeneratorPresentation U
          (S.factorObject K ⟨i, hi⟩))
  have hind : ∀ i : Fin S.n, P i := by
    intro i
    induction i using hwell.induction with
    | h i ih =>
        intro hi
        let xi : S.SurvivingLabel K := ⟨i, hi⟩
        by_cases hprojective : T.IsProjective xi
        · exact ⟨FiniteAddGeneratorPresentation.ofFiniteAddClosure
            (S.factorProjectiveObject_finiteAddClosure
              (⟨xi, hprojective⟩ : S.FactorProjectiveLabel K))⟩
        · let R := T.rightMesh (T.obj xi)
          obtain ⟨n, label, ⟨eM⟩⟩ := T.obj_decomposition R.X₂
          have hmiddle (t : Fin n) : O.lt (label t).1 i := by
            exact S.factorRightMiddle_label_strictly_precedes
              H xi hprojective label eM t
          let Pmiddle (t : Fin n) :
              FiniteAddGeneratorPresentation U (T.obj (label t)) :=
            Classical.choice (ih (label t).1 (hmiddle t) (label t).2)
          let PMsum := Classical.choice
            (finiteAddGeneratorPresentation_finBiproduct
              (fun t : Fin n ↦ T.obj (label t)) Pmiddle)
          let PM : FiniteAddGeneratorPresentation U R.X₂ :=
            PMsum.ofIso eM.symm
          let Xnp : T.Nonprojective := ⟨xi, hprojective⟩
          let y : S.SurvivingLabel K := T.tauPlus Xnp
          have hyi : O.lt y.1 i := by
            exact S.factorTauPlus_strictly_precedes H xi hprojective
          let Py : FiniteAddGeneratorPresentation U (T.obj y) :=
            Classical.choice (ih y.1 hyi y.2)
          let PL : FiniteAddGeneratorPresentation U R.X₁ :=
            Py.ofIso (T.tauPlusIso Xnp).symm
          have hweak : ∀ {Y : S.FactorCategory K}
              (q : R.X₂ ⟶ Y), R.f ≫ q = 0 →
                ∃ s : R.X₃ ⟶ Y, R.g ≫ s = q :=
            (ShortComplex.isWeakCokernel_iff R).1
              (S.factorRightMesh_isWeakCokernel_of_nonprojective
                xi hprojective)
          have hlift : ∀ h : U ⟶ R.X₃,
              ∃ l : U ⟶ R.X₂, l ≫ R.g = h := by
            intro h
            exact (T.rightTau (T.obj xi)).factors_into_right h
              (S.factorProjectiveGenerator_map_rightEndpoint_isRadical
                H xi hprojective h)
          let PR : FiniteAddGeneratorPresentation U R.X₃ :=
            PL.splice PM R.f R.g R.zero hlift hweak
              (S.factorProjectiveRestrictedYoneda_faithful D)
          exact ⟨PR.ofIso (T.rightTermIso (T.obj xi))⟩
  exact hind x.1 x.2

/-- Every object of the primitive factor has a finite presentation by the
tau-projective boundary generator. -/
theorem factorProjectiveGenerator_presentations
    {K : Set (Fin S.n)}
    (D : S.PrimitiveMultiplicityInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (X : S.FactorCategory K) :
    Nonempty
      (FiniteAddGeneratorPresentation
        (S.factorProjectiveGenerator K) X) := by
  obtain ⟨n, label, ⟨e⟩⟩ := S.factorCategory_obj_decomposition K X
  let P (i : Fin n) : FiniteAddGeneratorPresentation
      (S.factorProjectiveGenerator K) (S.factorObject K (label i)) :=
    Classical.choice
      (S.factorObject_finiteAddGeneratorPresentation D H (label i))
  let Psum := Classical.choice
    (finiteAddGeneratorPresentation_finBiproduct
      (fun i : Fin n ↦ S.factorObject K (label i)) P)
  exact ⟨Psum.ofIso e.symm⟩

/-- Restricted Yoneda on all tau-projective boundary objects is full in the
primitive directed factor. -/
theorem factorProjectiveRestrictedYoneda_full
    {K : Set (Fin S.n)}
    (D : S.PrimitiveMultiplicityInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    (S.factorProjectiveRestrictedYoneda K).Full :=
  S.factorProjectiveRestrictedYoneda_full_of_presentations D
    (S.factorProjectiveGenerator_presentations D H)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
