import MagnitudeConjecture.Algebra.StringPeakWedgeRepresentable
import MagnitudeConjecture.Algebra.StringPureEndpoint
import MagnitudeConjecture.Algebra.StringFiniteModuleClassification

/-!
# Pure peak strings as one-arm representables

A pure-positive string which starts and ends on peaks is the
complete surviving path arm from its source.  Evaluation at the source
therefore identifies its literal finite right-string module with the finite
representable there.  Reversal gives the pure-negative case.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- A pure-positive word with both endpoints on peaks is a peak wedge whose
left arm is trivial. -/
def PositiveExtension.oneArmPeakWedge
    (hR : IsAdmissible R) {C : Word R}
    (arm : PositiveExtension (vertex R hR C.source) C)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak) :
    C.PeakWedge where
  peak := C.source
  leftArm := Quiver.Path.nil
  rightArm := arm.ordinaryPath
  path_eq := by
    have hfactor := arm.toRightExtension.path_cast_comp_suffixPath
    rw [arm.toRightExtension_suffixPath_eq_positivePath] at hfactor
    simpa [vertex] using hfactor
  startsOnPeak := hstart
  endsOnPeak := hend

/-- The one nontrivial arm of a pure-positive peak wedge has the full word
length. -/
theorem IsPurePositive.exists_oneArmPeakWedge
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak) :
    ∃ W : C.PeakWedge,
      W.leftArm.length = 0 ∧ W.rightArm.length = C.length := by
  obtain ⟨arm⟩ := hpure
  let W : C.PeakWedge := arm.oneArmPeakWedge hR hstart hend
  refine ⟨W, rfl, ?_⟩
  change arm.ordinaryPath.length = C.length
  rw [arm.ordinaryPath_length]
  have hlength := arm.result_length
  simpa only [vertex_length, zero_add] using hlength.symm

namespace PositiveExtension

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]

/-- Every surviving path from the source of a pure peak arm is a prefix of
that arm, including when the arm is the trivial path. -/
theorem ordinaryPath_factor_of_vertex_of_peaks
    (P : SpecialBiserialPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (arm : PositiveExtension
      (vertex P.toPresentation.relations
        P.toPresentation.admissible C.source) C)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak)
    {y : Q} (p : Quiver.Path C.source y)
    (hp : pathMap P.toPresentation.relations p ≠ 0) :
    ∃ r : Quiver.Path y C.target,
      arm.ordinaryPath = p.comp r := by
  let q : Quiver.Path C.source C.target := arm.ordinaryPath
  have hCpath : C.path = positivePath q := by
    have hfactor := arm.toRightExtension.path_cast_comp_suffixPath
    rw [arm.toRightExtension_suffixPath_eq_positivePath] at hfactor
    simpa [vertex, q] using hfactor
  have hpString : IsString P.toPresentation.relations (positivePath p) :=
    isString_positivePath_of_pathMap_ne_zero
      P.toPresentation.admissible p hp
  by_cases hqzero : q.length = 0
  · have hCzero : C.path.length = 0 := by
      rw [hCpath, positivePath_length]
      exact hqzero
    have hsourceTarget : C.source = C.target :=
      q.eq_of_length_zero hqzero
    have hpzero : p.length = 0 := by
      by_contra hpnot
      obtain ⟨z, c, pTail, _, hpPath⟩ :=
        p.eq_toPath_comp_of_length_eq_succ
          (show p.length = p.length - 1 + 1 by omega)
      let c' : C.target ⟶ z :=
        Eq.mp (congrArg (fun x : Q ↦ x ⟶ z) hsourceTarget) c
      apply hstart c'
      exact isString_of_length_lt_two
        P.toPresentation.relations P.toPresentation.admissible
        (C.path.comp (positiveArrow c').toPath) (by
          simp only [Quiver.Path.length_comp,
            Quiver.Path.length_toPath, hCzero]
          omega)
    have hsource : C.source = y := p.eq_of_length_zero hpzero
    subst y
    refine ⟨q, ?_⟩
    rw [p.eq_nil_of_length_zero hpzero]
    simp
    rfl
  by_cases hpzero : p.length = 0
  · have hsource : C.source = y := p.eq_of_length_zero hpzero
    subst y
    refine ⟨q, ?_⟩
    rw [p.eq_nil_of_length_zero hpzero]
    simp [q]
  obtain ⟨w, b, qTail, _, hqPath⟩ :=
    q.eq_toPath_comp_of_length_eq_succ
      (show q.length = q.length - 1 + 1 by
        omega)
  obtain ⟨z, c, pTail, _, hpPath⟩ :=
    p.eq_toPath_comp_of_length_eq_succ
      (show p.length = p.length - 1 + 1 by omega)
  by_cases hbc : (⟨w, b⟩ : Quiver.Star C.source) = ⟨z, c⟩
  · cases hbc
    have hpTail :
        pathMap P.toPresentation.relations pTail ≫
            arrowMap P.toPresentation.relations b ≠ 0 := by
      change pathMap P.toPresentation.relations pTail ≫
        pathMap P.toPresentation.relations b.toPath ≠ 0
      rw [pathMap_comp]
      simpa only [hpPath] using hp
    have hqTail :
        pathMap P.toPresentation.relations qTail ≫
            arrowMap P.toPresentation.relations b ≠ 0 := by
      change pathMap P.toPresentation.relations qTail ≫
        pathMap P.toPresentation.relations b.toPath ≠ 0
      rw [pathMap_comp]
      have hq' := arm.pathMap_ordinaryPath_ne_zero
      change pathMap P.toPresentation.relations q ≠ 0 at hq'
      simpa only [hqPath] using hq'
    let pp : P.RightContinuationPath b := ⟨⟨y, pTail⟩, hpTail⟩
    let qq : P.RightContinuationPath b := ⟨⟨C.target, qTail⟩, hqTail⟩
    by_cases hle : p.length ≤ q.length
    · have htailLe : pTail.length ≤ qTail.length := by
        have hpLen := congrArg Quiver.Path.length hpPath
        have hqLen := congrArg Quiver.Path.length hqPath
        simp only [Quiver.Path.length_comp,
          Quiver.Path.length_toPath] at hpLen hqLen
        omega
      obtain ⟨r, hr⟩ :=
        P.rightContinuationPath_factor_of_length_le b pp qq htailLe
      refine ⟨r, ?_⟩
      change qTail = pTail.comp r at hr
      have hresult : q = p.comp r := by
        rw [hqPath, hpPath, hr, Quiver.Path.comp_assoc]
      exact hresult
    · have htailLe : qTail.length ≤ pTail.length := by
        have hpLen := congrArg Quiver.Path.length hpPath
        have hqLen := congrArg Quiver.Path.length hqPath
        simp only [Quiver.Path.length_comp,
          Quiver.Path.length_toPath] at hpLen hqLen
        omega
      obtain ⟨r, hr⟩ :=
        P.rightContinuationPath_factor_of_length_le b qq pp htailLe
      change pTail = qTail.comp r at hr
      have hrpos : 0 < r.length := by
        have hpLen := congrArg Quiver.Path.length hpPath
        have hqLen := congrArg Quiver.Path.length hqPath
        simp only [Quiver.Path.length_comp,
          Quiver.Path.length_toPath] at hpLen hqLen
        have hrLen := congrArg Quiver.Path.length hr
        simp only [Quiver.Path.length_comp] at hrLen
        omega
      obtain ⟨v, d, rTail, _, hrPath⟩ :=
        r.eq_toPath_comp_of_length_eq_succ
          (show r.length = r.length - 1 + 1 by omega)
      exfalso
      apply hstart d
      apply IsString.of_contiguousSubpath P.toPresentation.relations hpString
      refine ⟨Quiver.Path.nil, positivePath rTail, ?_⟩
      calc
        positivePath p =
            positivePath (q.comp (d.toPath.comp rTail)) := by
          rw [hpPath, hr, hrPath, hqPath,
            Quiver.Path.comp_assoc]
        _ = (positivePath q).comp
            ((positiveArrow d).toPath.comp (positivePath rTail)) := by
          rw [positivePath_comp, positivePath_comp,
            positivePath_toPath]
        _ = C.path.comp
            ((positiveArrow d).toPath.comp (positivePath rTail)) := by
          rw [hCpath]
        _ = Quiver.Path.nil.comp
            ((C.path.comp (positiveArrow d).toPath).comp
              (positivePath rTail)) := by
          simp only [Quiver.Path.nil_comp, ← Quiver.Path.comp_assoc,
            Quiver.Path.comp_toPath_eq_cons]
  · exfalso
    change C.reverse.StartsOnPeak at hend
    apply hend c
    change IsString P.toPresentation.relations
      (C.path.reverse.comp (positiveArrow c).toPath)
    rw [hCpath]
    have hqSigned : (positivePath q).reverse =
        (positivePath qTail).reverse.comp (negativeArrow b).toPath := by
      rw [hqPath, positivePath_comp, positivePath_toPath,
        Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath]
      rfl
    rw [hqSigned]
    apply isString_comp_of_negative_positive_boundaries_of_reduced
      P.toPresentation.relations
      (positivePath qTail).reverse b Quiver.Path.nil c Quiver.Path.nil
    · simp only [Quiver.Path.nil_comp, Quiver.Path.comp_nil]
      apply isReduced_comp_of_overlap
        (positivePath qTail).reverse (negativeArrow b).toPath
        (positiveArrow c).toPath (by simp)
      · rw [← hqSigned]
        exact (isString_reverse_iff P.toPresentation.relations
          (positivePath q)).2
            (isString_positivePath_of_pathMap_ne_zero
              P.toPresentation.admissible q
              arm.pathMap_ordinaryPath_ne_zero) |>.1
      · exact isReduced_negativeArrow_comp_positiveArrow_of_star_ne
          b c hbc
    · simpa only [Quiver.Path.comp_nil] using
        (show IsString P.toPresentation.relations
          ((positivePath qTail).reverse.comp (negativeArrow b).toPath) from by
            rw [← hqSigned]
            exact (isString_reverse_iff P.toPresentation.relations
              (positivePath q)).2
                (isString_positivePath_of_pathMap_ne_zero
                  P.toPresentation.admissible q
                  arm.pathMap_ordinaryPath_ne_zero))
    · change IsString P.toPresentation.relations
        (positiveArrow c).toPath
      exact isString_of_length_lt_two
        P.toPresentation.relations P.toPresentation.admissible
        (positiveArrow c).toPath (by simp)

/-- Every surviving path from the one-arm peak reaches a word position. -/
theorem exists_pathReach_oneArm_of_pathMap_ne_zero
    (P : SpecialBiserialPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (arm : PositiveExtension
      (vertex P.toPresentation.relations
        P.toPresentation.admissible C.source) C)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak)
    {y : Q} (p : Quiver.Path C.source y)
    (hp : pathMap P.toPresentation.relations p ≠ 0) :
    ∃ j : C.PositionAt y,
      C.PathReach p
        (arm.oneArmPeakWedge P.toPresentation.admissible
          hstart hend).peakPosition j := by
  let W := arm.oneArmPeakWedge P.toPresentation.admissible hstart hend
  obtain ⟨r, hr⟩ := arm.ordinaryPath_factor_of_vertex_of_peaks
    P hstart hend p hp
  exact ⟨W.rightPosition p r hr, W.pathReach_rightPosition p r hr⟩

/-- The position reached by a surviving path from a one-arm peak. -/
noncomputable def oneArmSurvivingPathTargetPosition
    (P : SpecialBiserialPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (arm : PositiveExtension
      (vertex P.toPresentation.relations
        P.toPresentation.admissible C.source) C)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak)
    (y : Q)
    (p : SurvivingPath P.toPresentation.relations C.source y) :
    C.PositionAt y :=
  Classical.choose
    (arm.exists_pathReach_oneArm_of_pathMap_ne_zero
      P hstart hend p.1 p.2)

/-- The selected one-arm target position is reached by its path. -/
theorem pathReach_oneArmSurvivingPathTargetPosition
    (P : SpecialBiserialPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (arm : PositiveExtension
      (vertex P.toPresentation.relations
        P.toPresentation.admissible C.source) C)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak)
    (y : Q)
    (p : SurvivingPath P.toPresentation.relations C.source y) :
    C.PathReach p.1
      (arm.oneArmPeakWedge P.toPresentation.admissible
        hstart hend).peakPosition
      (arm.oneArmSurvivingPathTargetPosition
        P hstart hend y p) :=
  Classical.choose_spec
    (arm.exists_pathReach_oneArm_of_pathMap_ne_zero
      P hstart hend p.1 p.2)

/-- Surviving paths from a one-arm peak are equivalent to word positions. -/
noncomputable def oneArmSurvivingPathEquivPositionAt
    (P : SpecialBiserialPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (arm : PositiveExtension
      (vertex P.toPresentation.relations
        P.toPresentation.admissible C.source) C)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak)
    (y : Q) :
    SurvivingPath P.toPresentation.relations C.source y ≃
      C.PositionAt y := by
  let W := arm.oneArmPeakWedge P.toPresentation.admissible hstart hend
  exact
    { toFun := arm.oneArmSurvivingPathTargetPosition
        P hstart hend y
      invFun := W.positionSurvivingPath P y
      left_inv := by
        intro p
        apply Subtype.ext
        exact W.path_eq_of_pathReach_peak _ _ _
            (W.pathReach_positionSurvivingPath P y
              (arm.oneArmSurvivingPathTargetPosition
              P hstart hend y p))
          (arm.pathReach_oneArmSurvivingPathTargetPosition
            P hstart hend y p)
      right_inv := by
        intro j
        have htarget :=
          arm.pathReach_oneArmSurvivingPathTargetPosition
            P hstart hend y (W.positionSurvivingPath P y j)
        have hj := W.pathReach_positionSurvivingPath P y j
        exact congrArg Subtype.val
          (@Subsingleton.elim
            {t : C.PositionAt y //
              C.PathReach (W.positionSurvivingPath P y j).1
                W.peakPosition t}
            (C.pathReach_subsingleton
              (W.positionSurvivingPath P y j).1 W.peakPosition)
            ⟨arm.oneArmSurvivingPathTargetPosition P hstart hend y
              (W.positionSurvivingPath P y j), htarget⟩
            ⟨j, hj⟩) }

end PositiveExtension

namespace PositiveExtension

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable (P : StringPresentation k A Q)
variable {C : Word P.toPresentation.relations}
variable (arm : PositiveExtension
  (vertex P.toPresentation.relations
    P.toPresentation.admissible C.source) C)
variable (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak)

private abbrev oneArmWedge :=
  arm.oneArmPeakWedge P.toPresentation.admissible hstart hend

/-- Source evaluation sends a surviving-path basis vector to the reached
word-position basis vector. -/
theorem oneArmPeakRepresentableHom_app_basis
    (y : Q)
    (p : SurvivingPath P.toPresentation.relations C.source y) :
    ((PeakWedge.peakRepresentableHom P
      (oneArmWedge P arm hstart hend)).hom.hom.app
        (Opposite.op (obj P.toPresentation.relations y))).hom
      (PeakWedge.peakRepresentableBasis P
        (oneArmWedge P arm hstart hend) y p) =
      Finsupp.single
        (arm.oneArmSurvivingPathTargetPosition
          P.toSpecialBiserialPresentation hstart hend y p) 1 := by
  rw [PeakWedge.peakRepresentableBasis_apply]
  change
    (linearCoyonedaHom (C.rightLinearModule P.monomial)
      (Opposite.op (obj P.toPresentation.relations C.source))
      (Finsupp.single
        (oneArmWedge P arm hstart hend).peakPosition 1)).hom.app
        (Opposite.op (obj P.toPresentation.relations y))
        (pathMap P.toPresentation.relations p.1).op = _
  rw [linearCoyonedaHom_app_apply]
  change (C.rightModule P.monomial).map
      (pathMap P.toPresentation.relations p.1).op
        (Finsupp.single
          (oneArmWedge P arm hstart hend).peakPosition 1) = _
  rw [C.rightModule_map_pathMap]
  change C.quiverRepresentation.map p.1
      (Finsupp.single
        (oneArmWedge P arm hstart hend).peakPosition 1) = _
  rw [C.quiverRepresentation_map_single, one_smul,
    C.pathOnBasis_eq_single_of_reach p.1
      (oneArmWedge P arm hstart hend).peakPosition
      (arm.oneArmSurvivingPathTargetPosition
        P.toSpecialBiserialPresentation hstart hend y p)
      (arm.pathReach_oneArmSurvivingPathTargetPosition
        P.toSpecialBiserialPresentation hstart hend y p)]

/-- The componentwise basis equivalence for a one-arm peak. -/
noncomputable def oneArmPeakRepresentableComponentLinearEquiv
    (y : Q) :
    ((PeakWedge.peakRepresentable P
      (oneArmWedge P arm hstart hend)).obj.obj.obj
        (Opposite.op (obj P.toPresentation.relations y))) ≃ₗ[k]
      C.Space y :=
    (PeakWedge.peakRepresentableBasis P
      (oneArmWedge P arm hstart hend) y).equiv
    Finsupp.basisSingleOne
    (arm.oneArmSurvivingPathEquivPositionAt
      P.toSpecialBiserialPresentation hstart hend y)

/-- Source evaluation agrees with the componentwise basis equivalence. -/
theorem oneArmPeakRepresentableHom_app_eq
    (y : Q) :
    ((PeakWedge.peakRepresentableHom P
      (oneArmWedge P arm hstart hend)).hom.hom.app
        (Opposite.op (obj P.toPresentation.relations y))).hom =
      (oneArmPeakRepresentableComponentLinearEquiv
        P arm hstart hend y).toLinearMap := by
  apply (PeakWedge.peakRepresentableBasis P
    (oneArmWedge P arm hstart hend) y).ext
  intro p
  rw [oneArmPeakRepresentableHom_app_basis
    P arm hstart hend y p]
  change Finsupp.single
      (arm.oneArmSurvivingPathTargetPosition
        P.toSpecialBiserialPresentation hstart hend y p) 1 =
    (oneArmPeakRepresentableComponentLinearEquiv
      P arm hstart hend y)
        (PeakWedge.peakRepresentableBasis P
          (oneArmWedge P arm hstart hend) y p)
  rw [oneArmPeakRepresentableComponentLinearEquiv,
    Module.Basis.equiv_apply]
  rfl

/-- Source evaluation is an isomorphism for a one-arm peak, including the
trivial-arm vertex case. -/
theorem oneArmPeakRepresentableHom_isIso :
    IsIso (PeakWedge.peakRepresentableHom P
      (oneArmWedge P arm hstart hend)) := by
  let W := oneArmWedge P arm hstart hend
  let f := PeakWedge.peakRepresentableHom P W
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := (Category P.toPresentation.relations)ᵒᵖ) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := (Category P.toPresentation.relations)ᵒᵖ) k).ι
  letI appIso (X : (Category P.toPresentation.relations)ᵒᵖ) :
      IsIso (f.hom.hom.app X) := by
    apply (ConcreteCategory.isIso_iff_bijective (f.hom.hom.app X)).mpr
    change Function.Bijective
      ((f.hom.hom.app (Opposite.op
        (obj P.toPresentation.relations X.unop.as))).hom)
    rw [show (f.hom.hom.app (Opposite.op
        (obj P.toPresentation.relations X.unop.as))).hom =
      (oneArmPeakRepresentableComponentLinearEquiv
        P arm hstart hend X.unop.as).toLinearMap from
      oneArmPeakRepresentableHom_app_eq
        P arm hstart hend X.unop.as]
    exact (oneArmPeakRepresentableComponentLinearEquiv
      P arm hstart hend X.unop.as).bijective
  haveI : IsIso f.hom.hom := NatIso.isIso_of_isIso_app f.hom.hom
  haveI : IsIso (I.map f.hom) := by
    change IsIso f.hom.hom
    infer_instance
  haveI : IsIso f.hom := isIso_of_reflects_iso f.hom I
  haveI : IsIso (J.map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f J

/-- A one-arm peak string is the finite representable at its source. -/
noncomputable def oneArmPeakRepresentableIso :
    PeakWedge.peakRepresentable P
        (oneArmWedge P arm hstart hend) ≅
      C.finiteRightModule P.monomial := by
  letI : IsIso (PeakWedge.peakRepresentableHom P
      (oneArmWedge P arm hstart hend)) :=
    oneArmPeakRepresentableHom_isIso
      P arm hstart hend
  exact asIso (PeakWedge.peakRepresentableHom P
    (oneArmWedge P arm hstart hend))

include arm hstart hend in
/-- The literal module of a one-arm peak is projective. -/
theorem finiteRightModule_projective_of_oneArmPeaks :
    Projective (C.finiteRightModule P.monomial) := by
  let W := oneArmWedge P arm hstart hend
  letI : Projective (PeakWedge.peakRepresentable P W) :=
    finiteDimensionalLinearCoyoneda_projective
      (Opposite.op (obj P.toPresentation.relations W.peak))
      (finiteOppositeRepresentablesOfAdmissible
        P.toPresentation.admissible
        (Opposite.op (obj P.toPresentation.relations W.peak)))
  exact Projective.of_iso
    (oneArmPeakRepresentableIso P arm hstart hend) inferInstance

end PositiveExtension

/-- A pure-positive word on peaks at both endpoints is projective, including
the length-zero vertex case. -/
theorem finiteRightModule_projective_of_isPurePositive_of_peaks
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : StringPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (hpure : C.IsPurePositive P.toPresentation.admissible)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak) :
    Projective (C.finiteRightModule P.monomial) := by
  obtain ⟨arm⟩ := hpure
  exact PositiveExtension.finiteRightModule_projective_of_oneArmPeaks
    P arm hstart hend

/-- The reversed pure-negative version of one-arm peak projectivity. -/
theorem finiteRightModule_projective_of_isPureNegative_of_peaks
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : StringPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (hpure : C.IsPureNegative P.toPresentation.admissible)
    (hstart : C.StartsOnPeak) (hend : C.EndsOnPeak) :
    Projective (C.finiteRightModule P.monomial) := by
  have hreverse : Projective
      (C.reverse.finiteRightModule P.monomial) :=
    finiteRightModule_projective_of_isPurePositive_of_peaks
      P hpure hend (by
        rw [reverse_endsOnPeak]
        exact hstart)
  exact Projective.of_iso C.finiteReverseRightModuleIso.symm hreverse

/-- A nonprojective pure-positive word which is maximal at its right endpoint
must admit a maximal left hook. -/
theorem exists_leftHook_of_isPurePositive_of_startsOnPeak_of_not_projective
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : StringPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (hpure : C.IsPurePositive P.toPresentation.admissible)
    (hstart : C.StartsOnPeak)
    (hnonprojective : ¬ Projective (C.finiteRightModule P.monomial)) :
    Nonempty (LeftHookExtension C) := by
  apply (exists_leftHook_iff_not_endsOnPeak
    P.toPresentation.admissible C).2
  intro hend
  apply hnonprojective
  exact finiteRightModule_projective_of_isPurePositive_of_peaks
    P hpure hstart hend

/-- A nonprojective pure-negative word which is maximal at its left endpoint
must admit a maximal right hook. -/
theorem exists_hook_of_isPureNegative_of_endsOnPeak_of_not_projective
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : StringPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (hpure : C.IsPureNegative P.toPresentation.admissible)
    (hend : C.EndsOnPeak)
    (hnonprojective : ¬ Projective (C.finiteRightModule P.monomial)) :
    ∃ D : Word P.toPresentation.relations,
      Nonempty (HookExtension C D) := by
  apply (exists_hook_iff_not_startsOnPeak
    P.toPresentation.admissible C).2
  intro hstart
  apply hnonprojective
  exact finiteRightModule_projective_of_isPureNegative_of_peaks
    P hpure hstart hend

end MagnitudeConjecture.BoundQuiver.StringWord.Word
