import MagnitudeConjecture.CategoryTheory.AlmostSplitEssentialImage
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownAuslanderReiten
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownBoundary
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso

/-!
# Radical morphisms in a finite deck-orbit category

For locally finite objects with local endomorphism rings and a deck action
free on isomorphism classes, a finite-support shift-orbit morphism is radical
exactly when each of its homogeneous components is radical upstairs.  This is
the pointwise input for push-down of the projective radical boundary.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- A local endomorphism ring makes its object nonzero. -/
theorem not_isZero_of_end_isLocalRing (X : C) [IsLocalRing (End X)] :
    ¬ IsZero X := by
  intro hX
  have h : (1 : End X) = 0 := by
    change (𝟙 X : X ⟶ X) = 0
    exact (IsZero.iff_id_eq_zero X).mp hX
  exact one_ne_zero h

/-- A split monomorphism into an object with local endomorphism ring is an
isomorphism as soon as its source is nonzero.  Unlike the biproduct version,
this uses only the local-ring idempotent dichotomy. -/
theorem isIso_of_isSplitMono_to_localEnd
    {X Y : C} [IsLocalRing (End Y)]
    (f : X ⟶ Y) [IsSplitMono f] (hX : ¬ IsZero X) : IsIso f := by
  let r : Y ⟶ X := retraction f
  let p : End Y := End.of (r ≫ f)
  have hp : IsIdempotentElem p := by
    change p * p = p
    apply End.ext
    change (r ≫ f) ≫ r ≫ f = r ≫ f
    dsimp only [r]
    rw [← Category.assoc (retraction f ≫ f) (retraction f) f,
      Category.assoc (retraction f) f (retraction f),
      IsSplitMono.id, Category.comp_id]
  rcases
      QuotientSubmoduleEquidistribution.Foundation.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
        hp with hpzero | hpone
  · exfalso
    apply hX
    apply (IsZero.iff_id_eq_zero X).mpr
    have hrf : r ≫ f = 0 := hpzero
    have hf : f = 0 := by
      calc
        f = (f ≫ r) ≫ f := by rw [IsSplitMono.id, Category.id_comp]
        _ = f ≫ (r ≫ f) := Category.assoc _ _ _
        _ = 0 := by rw [hrf, comp_zero]
    calc
      𝟙 X = f ≫ r := (IsSplitMono.id f).symm
      _ = 0 := by rw [hf, zero_comp]
  · apply IsIso.mk
    refine ⟨r, IsSplitMono.id f, ?_⟩
    exact hpone

/-- A homogeneous orbit morphism is the degree-zero inclusion of its
underlying map followed by the canonical isomorphism from the shifted target
back to the target. -/
theorem shiftOrbitOf_eq_zero_comp_objectShiftIso_inv
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    shiftOrbitOf X Y a f =
      shiftOrbitCompHom
        (shiftOrbitOf X ((shiftFunctor C a).obj Y) 0
          (shiftHomZero (A := A) f))
        (ShiftOrbitCategory.objectShiftIso Y a).inv := by
  rw [ShiftOrbitCategory.objectShiftIso]
  change shiftOrbitOf X Y a f =
    shiftOrbitCompHom
      (shiftOrbitOf X ((shiftFunctor C a).obj Y) 0
        (shiftHomZero (A := A) f))
      (shiftOrbitOf ((shiftFunctor C a).obj Y) Y a (𝟙 _))
  rw [shiftOrbitComp_zero_left_of]
  simp

/-- Split-monicity of a homogeneous orbit morphism is equivalent to
split-monicity of its upstairs component. -/
theorem shiftOrbitOf_isSplitMono_iff
    (k : Type uK) [Field k] [CategoryTheory.Linear k C]
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    IsSplitMono
        (show (show ShiftOrbitCategory C A from X) ⟶
            (show ShiftOrbitCategory C A from Y) from
          shiftOrbitOf X Y a f) ↔
      IsSplitMono f := by
  let q : (show ShiftOrbitCategory C A from X) ⟶
      (show ShiftOrbitCategory C A from Y) :=
    shiftOrbitOf X Y a f
  let q₀ : (show ShiftOrbitCategory C A from X) ⟶
      (show ShiftOrbitCategory C A from (shiftFunctor C a).obj Y) :=
    shiftOrbitOf X ((shiftFunctor C a).obj Y) 0
      (shiftHomZero (A := A) f)
  let e := ShiftOrbitCategory.objectShiftIso Y a
  have hq : q = q₀ ≫ e.inv :=
    shiftOrbitOf_eq_zero_comp_objectShiftIso_inv a f
  constructor
  · intro h
    letI : IsSplitMono q := h
    have hq₀ : IsSplitMono q₀ := by
      apply IsSplitMono.mk'
      exact
        { retraction := e.inv ≫ retraction q
          id := by
            calc
              q₀ ≫ (e.inv ≫ retraction q) =
                  (q₀ ≫ e.inv) ≫ retraction q :=
                (Category.assoc _ _ _).symm
              _ = q ≫ retraction q := by rw [← hq]
              _ = 𝟙 _ := IsSplitMono.id q }
    exact isSplitMono_of_shiftOrbit_zero_isSplitMono k f hq₀
  · intro h
    letI : IsSplitMono f := h
    let F := ShiftOrbitCategory.identityComponentFunctor (C := C) (A := A)
    have hq₀ : IsSplitMono q₀ := by
      change IsSplitMono (F.map f)
      infer_instance
    letI : IsSplitMono q₀ := hq₀
    apply IsSplitMono.mk'
    exact
      { retraction := e.hom ≫ retraction q₀
        id := by
          change q ≫ (e.hom ≫ retraction q₀) = 𝟙 _
          calc
            q ≫ (e.hom ≫ retraction q₀) =
                (q₀ ≫ e.inv) ≫ e.hom ≫ retraction q₀ := by rw [hq]
            _ = 𝟙 _ := by simp }

/-- With local endomorphism rings on the upstairs source and the orbit
source, a homogeneous orbit morphism is radical exactly when its component
is radical upstairs. -/
theorem shiftOrbitOf_isRadicalMorphism_iff
    (k : Type uK) [Field k] [CategoryTheory.Linear k C]
    {X Y : C} [IsLocalRing (End X)]
    [IsLocalRing
      (End (show ShiftOrbitCategory C A from X))]
    (a : A) (f : ShiftHom X Y a) :
    IsRadicalMorphism
        (show (show ShiftOrbitCategory C A from X) ⟶
            (show ShiftOrbitCategory C A from Y) from
          shiftOrbitOf X Y a f) ↔
      IsRadicalMorphism f := by
  rw [isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (not_isZero_of_end_isLocalRing
        (show ShiftOrbitCategory C A from X)),
    isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (not_isZero_of_end_isLocalRing X),
    shiftOrbitOf_isSplitMono_iff k]

omit [Preadditive C] [∀ a : A, (shiftFunctor C a).Additive] in
/-- Triviality of the shift stabilizer makes the degree of an isomorphism
between two translates unique. -/
theorem eq_of_isIso_shiftHom_of_isIso_shiftHom
    {X Y : C} {a b : A}
    (htrivial : ∀ c : A,
      Nonempty (Y ≅ (shiftFunctor C c).obj Y) → c = 0)
    (f : ShiftHom X Y a) (g : ShiftHom X Y b)
    [IsIso f] [IsIso g] : a = b := by
  let e : (shiftFunctor C a).obj Y ≅ (shiftFunctor C b).obj Y :=
    (asIso f).symm ≪≫ asIso g
  let eShift : Y ≅ (shiftFunctor C (b + -a)).obj Y :=
    (shiftShiftNeg Y a).symm ≪≫
      (shiftFunctor C (-a)).mapIso e ≪≫
        (shiftFunctorAdd C b (-a)).symm.app Y
  have hba : b + -a = 0 := htrivial (b + -a) ⟨eShift⟩
  exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hba)).symm

/-- Under localness and a trivial target shift stabilizer, a shift-orbit
morphism is radical exactly when all homogeneous components are radical. -/
theorem shiftOrbitHom_isRadicalMorphism_iff_components
    (k : Type uK) [Field k] [CategoryTheory.Linear k C]
    (hlocal : ∀ Z : C, IsLocalRing (End Z))
    (horbitLocal : ∀ Z : C,
      IsLocalRing (End (show ShiftOrbitCategory C A from Z)))
    (htrivial : ∀ (Y : C) (a : A),
      Nonempty (Y ≅ (shiftFunctor C a).obj Y) → a = 0)
    (X Y : C) (q : ShiftOrbitHom A X Y) :
    IsRadicalMorphism
        (show (show ShiftOrbitCategory C A from X) ⟶
            (show ShiftOrbitCategory C A from Y) from q) ↔
      ∀ a : A, IsRadicalMorphism (q a) := by
  classical
  letI : IsLocalRing (End X) := hlocal X
  letI : IsLocalRing
      (End (show ShiftOrbitCategory C A from X)) := horbitLocal X
  have forward (s : ShiftOrbitHom A X Y)
      (hs : ∀ a : A, IsRadicalMorphism (s a)) :
      IsRadicalMorphism
        (show (show ShiftOrbitCategory C A from X) ⟶
            (show ShiftOrbitCategory C A from Y) from s) := by
    classical
    rw [show s = ∑ a ∈ s.support, shiftOrbitOf X Y a (s a) by
      exact DFinsupp.sum_single.symm]
    apply isRadicalMorphism_finset_sum
    intro a _
    exact (shiftOrbitOf_isRadicalMorphism_iff k a (s a)).mpr (hs a)
  constructor
  · intro hq a
    by_contra ha
    have hsplitA : IsSplitMono (q a) := by
      by_contra hsplit
      exact ha ((isRadicalMorphism_iff_not_isSplitMono_of_local_end
        (not_isZero_of_end_isLocalRing X) (q a)).mpr hsplit)
    letI : IsSplitMono (q a) := hsplitA
    have hrestComponents : ∀ b : A,
        IsRadicalMorphism
          ((q - shiftOrbitOf X Y a (q a)) b) := by
      intro b
      by_cases hba : b = a
      · subst b
        have hof : (shiftOrbitOf X Y a (q a)) a = q a := by
          change DirectSum.of (fun c : A ↦ ShiftHom X Y c) a (q a) a = q a
          simp
        have hcomponent :
            (q - shiftOrbitOf X Y a (q a)) a =
              q a - (shiftOrbitOf X Y a (q a)) a := by
          exact map_sub
            (DirectSum.component k A (fun c : A ↦ ShiftHom X Y c) a)
            q (shiftOrbitOf X Y a (q a))
        rw [hcomponent, hof, sub_self]
        exact
          (isRadicalMorphism_zero :
            IsRadicalMorphism (0 : ShiftHom X Y a))
      · have hqb : IsRadicalMorphism (q b) := by
          by_contra hb
          have hsplitB : IsSplitMono (q b) := by
            by_contra hsplit
            exact hb ((isRadicalMorphism_iff_not_isSplitMono_of_local_end
              (not_isZero_of_end_isLocalRing X) (q b)).mpr hsplit)
          letI : IsSplitMono (q b) := hsplitB
          letI : IsLocalRing (End ((shiftFunctor C a).obj Y)) :=
            hlocal ((shiftFunctor C a).obj Y)
          letI : IsLocalRing (End ((shiftFunctor C b).obj Y)) :=
            hlocal ((shiftFunctor C b).obj Y)
          haveI : IsIso (q a) :=
            isIso_of_isSplitMono_to_localEnd (q a)
              (not_isZero_of_end_isLocalRing X)
          haveI : IsIso (q b) :=
            isIso_of_isSplitMono_to_localEnd (q b)
              (not_isZero_of_end_isLocalRing X)
          exact hba (eq_of_isIso_shiftHom_of_isIso_shiftHom
            (htrivial Y) (q a) (q b)).symm
        have hof : (shiftOrbitOf X Y a (q a)) b = 0 := by
          change DirectSum.of (fun c : A ↦ ShiftHom X Y c) a (q a) b = 0
          simp [DirectSum.of_apply, Ne.symm hba]
        have hcomponent :
            (q - shiftOrbitOf X Y a (q a)) b =
              q b - (shiftOrbitOf X Y a (q a)) b := by
          exact map_sub
            (DirectSum.component k A (fun c : A ↦ ShiftHom X Y c) b)
            q (shiftOrbitOf X Y a (q a))
        rw [hcomponent, hof, sub_zero]
        exact hqb
    have hrest : IsRadicalMorphism
        (show (show ShiftOrbitCategory C A from X) ⟶
            (show ShiftOrbitCategory C A from Y) from
          q - shiftOrbitOf X Y a (q a)) :=
      forward _ hrestComponents
    have hsingle : IsRadicalMorphism
        (show (show ShiftOrbitCategory C A from X) ⟶
            (show ShiftOrbitCategory C A from Y) from
          shiftOrbitOf X Y a (q a)) := by
      have hsum := isRadicalMorphism_add hq (isRadicalMorphism_neg hrest)
      have heq :
          q + -(q - shiftOrbitOf X Y a (q a)) =
            shiftOrbitOf X Y a (q a) := by
        abel
      simpa only [heq] using hsum
    exact ha ((shiftOrbitOf_isRadicalMorphism_iff k a (q a)).mp hsingle)
  · exact forward q

section RadicalComparison

universe uR vR

variable {kR : Type vR} [Field kR]
variable {CR : Type uR} [Category.{vR} CR] [Preadditive CR]
variable [CategoryTheory.Linear kR CR]
variable {AR : Type vR} [AddGroup AR] [HasShift CR AR]
variable [∀ a : AR, (shiftFunctor CR a).Additive]
variable [∀ a : AR, (shiftFunctor CR a).Linear kR]

/-- The diagonal inclusion from the push-down of `rad(X,-)` into the
push-down of `Hom(X,-)`, followed by the canonical orbit-representable
comparison. -/
noncomputable def orbitPushdownRadicalToRepresentable (X : CR) :
    orbitPushdown (A := AR) (radicalLinearCoyoneda (k := kR) X) ⟶
      (linearCoyoneda kR (ShiftOrbitCategory CR AR)).obj
        (Opposite.op (show ShiftOrbitCategory CR AR from X)) :=
  orbitPushdownNatTrans (A := AR)
      (radicalLinearCoyonedaInclusionNatTrans (k := kR) X) ≫
    (orbitPushdownLinearCoyonedaIso (k := kR) (A := AR) X).hom

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise, the preceding comparison simply forgets each component's
radical-membership proof. -/
theorem orbitPushdownRadicalToRepresentable_app_apply
    (X Y : CR)
    (z : orbitPushdownValue (A := AR)
      (radicalLinearCoyoneda (k := kR) X) Y) :
    (orbitPushdownRadicalToRepresentable (kR := kR) (AR := AR) X).app Y z =
      DirectSum.lmap
        (fun a ↦
          ((radicalLinearCoyonedaInclusionNatTrans (k := kR) X).app
            ((shiftFunctor CR a).obj Y)).hom) z := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp
  | of a f =>
      change orbitPushdownNatTransAppLinear (A := AR)
          (radicalLinearCoyonedaInclusionNatTrans (k := kR) X) Y
          (orbitPushdownLof (radicalLinearCoyoneda (k := kR) X) Y a f) = _
      rw [orbitPushdownNatTransAppLinear_lof, DirectSum.lmap_of]
      rw [orbitPushdownLof, DirectSum.lof_eq_of]
  | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, map_add, hz₁, hz₂]

/-- Before choosing orbit representatives, push-down of the radical
representable maps canonically to the radical of the orbit representable. -/
noncomputable def orbitPushdownRadicalLinearCoyonedaComparison
    (X : CR)
    (hcomponents : ∀ (Y : CR) (q : ShiftOrbitHom AR X Y),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory CR AR from X) ⟶
              (show ShiftOrbitCategory CR AR from Y) from q) ↔
        ∀ a : AR, IsRadicalMorphism (q a)) :
    orbitPushdown (A := AR) (radicalLinearCoyoneda (k := kR) X) ⟶
      radicalLinearCoyoneda (k := kR)
        (C := ShiftOrbitCategory CR AR)
        (show ShiftOrbitCategory CR AR from X) where
  app Y := ModuleCat.ofHom
    { toFun := fun z ↦
        ⟨(orbitPushdownRadicalToRepresentable
            (kR := kR) (AR := AR) X).app Y z,
          (hcomponents (show CR from Y) _).mpr (fun a ↦ by
            rw [orbitPushdownRadicalToRepresentable_app_apply]
            change IsRadicalMorphism
              ((DirectSum.lmap
                (fun b ↦
                  ((radicalLinearCoyonedaInclusionNatTrans (k := kR) X).app
                    ((shiftFunctor CR b).obj (show CR from Y))).hom)
                z) a)
            rw [DirectSum.lmap_apply]
            change IsRadicalMorphism (z a).1
            exact (z a).2)⟩
      map_add' := by
        intro z z'
        apply Subtype.ext
        exact map_add _ z z'
      map_smul' := by
        intro a z
        apply Subtype.ext
        exact map_smul _ a z }
  naturality := by
    intro Y Z f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((orbitPushdownRadicalToRepresentable
        (kR := kR) (AR := AR) X).naturality f) z

/-- The raw orbit radical comparison is an isomorphism: its inverse regroups
the finitely many homogeneous radical components. -/
noncomputable def orbitPushdownRadicalLinearCoyonedaIso
    (X : CR)
    (hcomponents : ∀ (Y : CR) (q : ShiftOrbitHom AR X Y),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory CR AR from X) ⟶
              (show ShiftOrbitCategory CR AR from Y) from q) ↔
        ∀ a : AR, IsRadicalMorphism (q a)) :
    orbitPushdown (A := AR) (radicalLinearCoyoneda (k := kR) X) ≅
      radicalLinearCoyoneda (k := kR)
        (C := ShiftOrbitCategory CR AR)
        (show ShiftOrbitCategory CR AR from X) := by
  let c := orbitPushdownRadicalLinearCoyonedaComparison
    (kR := kR) (AR := AR) X hcomponents
  haveI hc : IsIso c := by
    letI appIso (Y : ShiftOrbitCategory CR AR) : IsIso (c.app Y) := by
      apply (ConcreteCategory.isIso_iff_bijective (c.app Y)).mpr
      constructor
      · intro z z' hzz'
        apply (DirectSum.lmap_injective
          (fun a ↦
            ((radicalLinearCoyonedaInclusionNatTrans (k := kR) X).app
              ((shiftFunctor CR a).obj (show CR from Y))).hom)).mpr
          (fun a ↦
            (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule kR X
              ((shiftFunctor CR a).obj (show CR from Y))).subtype_injective)
        rw [← orbitPushdownRadicalToRepresentable_app_apply,
          ← orbitPushdownRadicalToRepresentable_app_apply]
        exact congrArg Subtype.val hzz'
      · intro q
        classical
        let qval : ShiftOrbitHom AR X (show CR from Y) := q.1
        let z : orbitPushdownValue (A := AR)
            (radicalLinearCoyoneda (k := kR) X) (show CR from Y) :=
          ∑ a ∈ qval.support,
            orbitPushdownLof (radicalLinearCoyoneda (k := kR) X)
              (show CR from Y) a
              ⟨qval a, (hcomponents (show CR from Y) qval).mp q.2 a⟩
        refine ⟨z, ?_⟩
        apply Subtype.ext
        change (orbitPushdownRadicalToRepresentable
          (kR := kR) (AR := AR) X).app (show CR from Y) z = qval
        rw [orbitPushdownRadicalToRepresentable_app_apply]
        change DirectSum.lmap
            (fun a ↦
              ((radicalLinearCoyonedaInclusionNatTrans (k := kR) X).app
                ((shiftFunctor CR a).obj (show CR from Y))).hom) z = qval
        dsimp only [z]
        rw [map_sum]
        simp only [orbitPushdownLof, DirectSum.lmap_lof,
          radicalLinearCoyonedaInclusionNatTrans]
        change ∑ a ∈ qval.support,
            DirectSum.of (fun b : AR ↦ ShiftHom X (show CR from Y) b)
              a (qval a) = qval
        exact DFinsupp.sum_single
    exact NatIso.isIso_of_isIso_app c
  exact asIso c

/-- The raw radical comparison is the restriction of the canonical
projective-representable push-down comparison. -/
theorem orbitPushdownRadicalLinearCoyonedaIso_hom_comp_inclusion
    (X : CR)
    (hcomponents : ∀ (Y : CR) (q : ShiftOrbitHom AR X Y),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory CR AR from X) ⟶
              (show ShiftOrbitCategory CR AR from Y) from q) ↔
        ∀ a : AR, IsRadicalMorphism (q a)) :
    (orbitPushdownRadicalLinearCoyonedaIso
        (kR := kR) (AR := AR) X hcomponents).hom ≫
        radicalLinearCoyonedaInclusionNatTrans (k := kR)
          (C := ShiftOrbitCategory CR AR)
          (show ShiftOrbitCategory CR AR from X) =
      orbitPushdownNatTrans (A := AR)
          (radicalLinearCoyonedaInclusionNatTrans (k := kR) X) ≫
        (orbitPushdownLinearCoyonedaIso
          (k := kR) (A := AR) X).hom := by
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

end RadicalComparison

namespace CoherentDeckShift

universe u' v'

variable {k' : Type v'} [Field k']
variable {C' : Type u'} [Category.{v'} C'] [Preadditive C']
variable {G : Type v'} [Group G] [MulAction G C'] [IsCancelSMul G C']
variable [CategoryTheory.Linear k' C']
variable (D : CoherentDeckShift C' G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k']

private def inducedEndRingEquiv
    (q : MulAction.orbitRel.Quotient G C') :
    letI := D.hasShift
    letI := D.additiveShift
    End (show DeckOrbitSkeleton C' G from q) ≃+*
      End (show ShiftOrbitCategory C' (Additive G) from
        deckOrbitRepresentative (C := C') (G := G) q) := by
  letI := D.hasShift
  letI := D.additiveShift
  exact
    { toFun := fun f ↦ f.hom
      invFun := fun f ↦ InducedCategory.homMk f
      left_inv := by intro f; apply InducedCategory.hom_ext; rfl
      right_inv := by intro f; rfl
      map_add' := by intro f g; rfl
      map_mul' := by intro f g; rfl }

private def endRingEquivOfIso
    {D₀ : Type u'} [Category.{v'} D₀] [Preadditive D₀]
    {X Y : D₀} (e : X ≅ Y) : End X ≃+* End Y :=
  { e.conj with
    map_add' := by
      intro f g
      apply End.ext
      change e.inv ≫ (End.asHom f + End.asHom g) ≫ e.hom =
        e.inv ≫ End.asHom f ≫ e.hom +
          e.inv ≫ End.asHom g ≫ e.hom
      simp only [Preadditive.comp_add, Preadditive.add_comp] }

omit [Preadditive C'] [IsCancelSMul G C']
  [∀ a : Additive G, (D.core.F a).Additive] in
/-- Freeness of the deck action on isomorphism classes gives a trivial
stabilizer for every object under the associated additive shift. -/
theorem object_trivialShiftStabilizer
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    ∀ a : Additive G,
      Nonempty (X ≅ (shiftFunctor C' a).obj X) → a = 0 := by
  letI := D.hasShift
  intro a
  rintro ⟨e⟩
  have hinv : a.toMul⁻¹ = 1 :=
    hfree a.toMul⁻¹ X ⟨e ≪≫ D.objIso a.toMul X⟩
  exact toMul_eq_one.mp (inv_eq_one.mp hinv)

/-- The shift-orbit endomorphism ring of every upstairs object is local.
It is transported from the corresponding deck-orbit-skeleton vertex. -/
theorem shiftOrbit_end_isLocalRing
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    IsLocalRing
      (End (show ShiftOrbitCategory C' (Additive G) from X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let q : MulAction.orbitRel.Quotient G C' := Quotient.mk'' X
  let R := deckOrbitRepresentative (C := C') (G := G) q
  letI hq : IsLocalRing (End (show DeckOrbitSkeleton C' G from q)) :=
    D.orbitSkeleton_end_isLocalRing (k := k') hP hlocal hfree q
  letI hR : IsLocalRing
      (End (show ShiftOrbitCategory C' (Additive G) from R)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (inducedEndRingEquiv (D := D) q)
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (endRingEquivOfIso (D.objectIsoDeckOrbitRepresentative X).symm)

/-- Deck-specialized componentwise criterion for categorical radical
morphisms in the shift-orbit category. -/
theorem shiftOrbitHom_isRadicalMorphism_iff_components
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X Y : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    ∀ q : ShiftOrbitHom (Additive G) X Y,
      IsRadicalMorphism
          (show (show ShiftOrbitCategory C' (Additive G) from X) ⟶
              (show ShiftOrbitCategory C' (Additive G) from Y) from q) ↔
        ∀ a : Additive G, IsRadicalMorphism (q a) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  intro q
  exact MagnitudeConjecture.CoveringHom.shiftOrbitHom_isRadicalMorphism_iff_components
    k' hlocal
      (D.shiftOrbit_end_isLocalRing (k' := k') hP hlocal hfree)
      (D.object_trivialShiftStabilizer hfree) X Y q

/-- Before choosing orbit representatives, Gabriel push-down sends the
radical of an upstairs projective representable to the radical of the
corresponding shift-orbit representable. -/
noncomputable def orbitPushdownRadicalLinearCoyonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    orbitPushdown (A := Additive G)
        (radicalLinearCoyoneda (k := k') X) ≅
      radicalLinearCoyoneda (k := k')
        (C := ShiftOrbitCategory C' (Additive G))
        (show ShiftOrbitCategory C' (Additive G) from X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  exact
    MagnitudeConjecture.CoveringHom.orbitPushdownRadicalLinearCoyonedaIso
      (kR := k') (AR := Additive G) X
      (fun Y ↦ D.shiftOrbitHom_isRadicalMorphism_iff_components
        (k' := k') hP hlocal hfree X Y)

/-- The deck-specialized raw radical comparison is compatible with the
projective-representable comparison. -/
theorem orbitPushdownRadicalLinearCoyonedaIso_hom_comp_inclusion
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.orbitPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom ≫
        radicalLinearCoyonedaInclusionNatTrans (k := k')
          (C := ShiftOrbitCategory C' (Additive G))
          (show ShiftOrbitCategory C' (Additive G) from X) =
      orbitPushdownNatTrans (A := Additive G)
          (radicalLinearCoyonedaInclusionNatTrans (k := k') X) ≫
        (orbitPushdownLinearCoyonedaIso
          (k := k') (A := Additive G) X).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  exact
    MagnitudeConjecture.CoveringHom.orbitPushdownRadicalLinearCoyonedaIso_hom_comp_inclusion
      (kR := k') (AR := Additive G) X
      (fun Y ↦ D.shiftOrbitHom_isRadicalMorphism_iff_components
        (k' := k') hP hlocal hfree X Y)

/-- Radicality agrees in the chosen orbit skeleton and in the ambient
shift-orbit category. -/
theorem deckOrbitRepresentativeFunctor_map_isRadicalMorphism_iff
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    {X Y : MulAction.orbitRel.Quotient G C'}
    (f :
      letI := D.hasShift
      letI := D.additiveShift
      (show DeckOrbitSkeleton C' G from X) ⟶
        (show DeckOrbitSkeleton C' G from Y)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    IsRadicalMorphism
        ((deckOrbitRepresentativeFunctor (C := C') (G := G)).map f) ↔
      IsRadicalMorphism f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := deckOrbitRepresentativeFunctor (C := C') (G := G)
  letI hX : IsLocalRing
      (End (show DeckOrbitSkeleton C' G from X)) :=
    D.orbitSkeleton_end_isLocalRing (k := k') hP hlocal hfree X
  letI hJX : IsLocalRing
      (End (J.obj (show DeckOrbitSkeleton C' G from X))) :=
    D.shiftOrbit_end_isLocalRing (k' := k') hP hlocal hfree
      (deckOrbitRepresentative (C := C') (G := G) X)
  rw [MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (not_isZero_of_end_isLocalRing
        (J.obj (show DeckOrbitSkeleton C' G from X))),
    MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (not_isZero_of_end_isLocalRing
        (show DeckOrbitSkeleton C' G from X)),
    Functor.isSplitMono_iff]

/-- At chosen representatives, the ambient and induced-category radical Hom
spaces are canonically linearly equivalent. -/
noncomputable def deckOrbitRepresentativeRadicalHomLinearEquiv
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X Y : MulAction.orbitRel.Quotient G C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k'
        (show ShiftOrbitCategory C' (Additive G) from
          deckOrbitRepresentative (C := C') (G := G) X)
        (show ShiftOrbitCategory C' (Additive G) from
          deckOrbitRepresentative (C := C') (G := G) Y) ≃ₗ[k']
      MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k'
        (show DeckOrbitSkeleton C' G from X)
        (show DeckOrbitSkeleton C' G from Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := deckOrbitRepresentativeFunctor (C := C') (G := G)
  exact
    { toFun := fun f ↦
        let g : (show DeckOrbitSkeleton C' G from X) ⟶
            (show DeckOrbitSkeleton C' G from Y) :=
          InducedCategory.homMk f.1
        ⟨g,
          (D.deckOrbitRepresentativeFunctor_map_isRadicalMorphism_iff
            (k' := k') hP hlocal hfree g).mp (by
              change IsRadicalMorphism f.1
              exact f.2)⟩
      invFun := fun f ↦
        ⟨J.map f.1,
          (D.deckOrbitRepresentativeFunctor_map_isRadicalMorphism_iff
            (k' := k') hP hlocal hfree f.1).mpr f.2⟩
      left_inv := by
        intro f
        apply Subtype.ext
        rfl
      right_inv := by
        intro f
        apply Subtype.ext
        apply InducedCategory.hom_ext
        rfl
      map_add' := by
        intro f g
        apply Subtype.ext
        apply InducedCategory.hom_ext
        rfl
      map_smul' := by
        intro r f
        apply Subtype.ext
        apply InducedCategory.hom_ext
        rfl }

/-- Restricting the radical representable at a chosen representative gives
the literal radical representable on the deck-orbit skeleton. -/
noncomputable def deckOrbitRepresentativeRadicalLinearCoyonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : MulAction.orbitRel.Quotient G C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    deckOrbitRepresentativeFunctor (C := C') (G := G) ⋙
        radicalLinearCoyoneda (k := k')
          (C := ShiftOrbitCategory C' (Additive G))
          (show ShiftOrbitCategory C' (Additive G) from
            deckOrbitRepresentative (C := C') (G := G) X) ≅
      radicalLinearCoyoneda (k := k')
        (C := DeckOrbitSkeleton C' G)
        (show DeckOrbitSkeleton C' G from X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  refine NatIso.ofComponents (fun Y ↦
    (D.deckOrbitRepresentativeRadicalHomLinearEquiv
      (k' := k') hP hlocal hfree X Y).toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  apply InducedCategory.hom_ext
  rfl

/-- The chosen-representative radical comparison is the restriction of the
corresponding representable comparison. -/
theorem deckOrbitRepresentativeRadicalLinearCoyonedaIso_hom_comp_inclusion
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : MulAction.orbitRel.Quotient G C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.deckOrbitRepresentativeRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom ≫
        radicalLinearCoyonedaInclusionNatTrans (k := k')
          (C := DeckOrbitSkeleton C' G)
          (show DeckOrbitSkeleton C' G from X) =
      Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C') (G := G))
          (radicalLinearCoyonedaInclusionNatTrans (k := k')
            (C := ShiftOrbitCategory C' (Additive G))
            (show ShiftOrbitCategory C' (Additive G) from
              deckOrbitRepresentative (C := C') (G := G) X)) ≫
        (deckOrbitRepresentativeLinearCoyonedaIso (k := k') X).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  rfl

/-- Skeletal Gabriel push-down sends the radical of the projective
representable at `X` to the radical of the projective representable at the
strict orbit of `X`. -/
noncomputable def orbitSkeletonPushdownRadicalLinearCoyonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    orbitSkeletonPushdown (G := G)
        (radicalLinearCoyoneda (k := k') X) ≅
      radicalLinearCoyoneda (k := k')
        (C := DeckOrbitSkeleton C' G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := deckOrbitRepresentativeFunctor (C := C') (G := G)
  let Q : DeckOrbitSkeleton C' G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  exact Functor.isoWhiskerLeft J
      (D.orbitPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X) ≪≫
    Functor.isoWhiskerLeft J
      (radicalLinearCoyonedaMapIso (k := k')
        (D.objectIsoDeckOrbitRepresentative X)) ≪≫
    D.deckOrbitRepresentativeRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree Q

/-- The skeletal radical comparison and projective-representable comparison
identify the pushed radical inclusion with the literal downstairs radical
inclusion. -/
theorem orbitSkeletonPushdownRadicalLinearCoyonedaIso_hom_comp_inclusion
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.orbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom ≫
        radicalLinearCoyonedaInclusionNatTrans (k := k')
          (C := DeckOrbitSkeleton C' G)
          (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') =
      Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C') (G := G))
          (orbitPushdownNatTrans (A := Additive G)
            (radicalLinearCoyonedaInclusionNatTrans (k := k') X)) ≫
        (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k') X).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := deckOrbitRepresentativeFunctor (C := C') (G := G)
  let Q : DeckOrbitSkeleton C' G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  let a := Functor.whiskerLeft J
    (D.orbitPushdownRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree X).hom
  let b := Functor.whiskerLeft J
    (radicalLinearCoyonedaMapIso (k := k')
      (D.objectIsoDeckOrbitRepresentative X)).hom
  let c := (D.deckOrbitRepresentativeRadicalLinearCoyonedaIso
    (k' := k') hP hlocal hfree Q).hom
  let iX := Functor.whiskerLeft J
    (radicalLinearCoyonedaInclusionNatTrans (k := k')
      (C := ShiftOrbitCategory C' (Additive G))
      (show ShiftOrbitCategory C' (Additive G) from X))
  let iR := Functor.whiskerLeft J
    (radicalLinearCoyonedaInclusionNatTrans (k := k')
      (C := ShiftOrbitCategory C' (Additive G))
      (show ShiftOrbitCategory C' (Additive G) from
        deckOrbitRepresentative (C := C') (G := G) Q))
  let iQ := radicalLinearCoyonedaInclusionNatTrans (k := k')
    (C := DeckOrbitSkeleton C' G) Q
  let p := Functor.whiskerLeft J
    (orbitPushdownNatTrans (A := Additive G)
      (radicalLinearCoyonedaInclusionNatTrans (k := k') X))
  let A₀ := Functor.whiskerLeft J
    (orbitPushdownLinearCoyonedaIso
      (k := k') (A := Additive G) X).hom
  let B₀ := Functor.whiskerLeft J
    ((linearCoyoneda k'
      (ShiftOrbitCategory C' (Additive G))).mapIso
        (D.objectIsoDeckOrbitRepresentative X).symm.op).hom
  let C₀ := (deckOrbitRepresentativeLinearCoyonedaIso (k := k') Q).hom
  change (a ≫ b ≫ c) ≫ iQ = p ≫ (A₀ ≫ B₀ ≫ C₀)
  have h₁ : a ≫ iX = p ≫ A₀ := by
    dsimp only [a, iX, p, A₀, J]
    simpa only [Functor.whiskerLeft_comp] using congrArg
      (Functor.whiskerLeft J)
      (D.orbitPushdownRadicalLinearCoyonedaIso_hom_comp_inclusion
        (k' := k') hP hlocal hfree X)
  have h₂ : b ≫ iR = iX ≫ B₀ := by
    dsimp only [b, iR, iX, B₀, J]
    simpa only [Functor.whiskerLeft_comp] using congrArg
      (Functor.whiskerLeft J)
      (radicalLinearCoyonedaMapIso_hom_comp_inclusion
        (k := k') (D.objectIsoDeckOrbitRepresentative X))
  have h₃ : c ≫ iQ = iR ≫ C₀ := by
    exact D.deckOrbitRepresentativeRadicalLinearCoyonedaIso_hom_comp_inclusion
      (k' := k') hP hlocal hfree Q
  calc
    (a ≫ b ≫ c) ≫ iQ = a ≫ b ≫ (c ≫ iQ) := by simp only [Category.assoc]
    _ = a ≫ b ≫ (iR ≫ C₀) := by rw [h₃]
    _ = a ≫ (b ≫ iR) ≫ C₀ := by simp only [Category.assoc]
    _ = a ≫ (iX ≫ B₀) ≫ C₀ := by rw [h₂]
    _ = (a ≫ iX) ≫ B₀ ≫ C₀ := by simp only [Category.assoc]
    _ = (p ≫ A₀) ≫ B₀ ≫ C₀ := by rw [h₁]
    _ = p ≫ (A₀ ≫ B₀ ≫ C₀) := by simp only [Category.assoc]

/-- Bundled linear-module form of skeletal push-down preserving the radical
of a projective representable. -/
noncomputable def linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (linearModuleOrbitSkeletonPushdown
        (k := k') (C := C') (G := G)).obj
        (radicalLinearCoyonedaLinearModule (k := k') X) ≅
      radicalLinearCoyonedaLinearModule (k := k')
        (C := DeckOrbitSkeleton C' G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  exact (IsLinearModule (C := DeckOrbitSkeleton C' G) k').ι.preimageIso
    (D.orbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree X)

@[simp]
theorem linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso_hom_hom
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom.hom =
      (D.orbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := (IsLinearModule (C := DeckOrbitSkeleton C' G) k').ι
  let LX := (linearModuleOrbitSkeletonPushdown
    (k := k') (C := C') (G := G)).obj
      (radicalLinearCoyonedaLinearModule (k := k') X)
  let RX := radicalLinearCoyonedaLinearModule (k := k')
    (C := DeckOrbitSkeleton C' G)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  change (J.preimage (X := LX) (Y := RX)
      (D.orbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom).hom =
    (D.orbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree X).hom
  exact J.map_preimage (X := LX) (Y := RX)
    (D.orbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree X).hom

/-- The finite downstairs radical projective associated to the strict orbit
of `X`. -/
noncomputable def orbitSkeletonFiniteDimensionalLinearCoyonedaRadical
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    FiniteDimensionalModuleCategory
      (C := DeckOrbitSkeleton C' G) k' := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k') hP
  exact finiteDimensionalLinearCoyonedaRadical (k := k')
    (C := DeckOrbitSkeleton C' G)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
    (hP' (Quotient.mk'' X : MulAction.orbitRel.Quotient G C'))

/-- Finite-dimensional skeletal push-down preserves the radical of a finite
projective representable. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).obj
        (finiteDimensionalLinearCoyonedaRadical (k := k') X (hP X)) ≅
      D.orbitSkeletonFiniteDimensionalLinearCoyonedaRadical
        (k' := k') hP X := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  exact (IsFiniteDimensionalModule
    (C := DeckOrbitSkeleton C' G) k').ι.preimageIso
      (D.linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X)

@[simp]
theorem finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso_hom_hom
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom.hom =
      (D.linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := (IsFiniteDimensionalModule
    (C := DeckOrbitSkeleton C' G) k').ι
  let LX := (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).obj
    (finiteDimensionalLinearCoyonedaRadical (k := k') X (hP X))
  let RX := D.orbitSkeletonFiniteDimensionalLinearCoyonedaRadical
    (k' := k') hP X
  change (J.preimage (X := LX) (Y := RX)
      (D.linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom).hom =
    (D.linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree X).hom
  exact J.map_preimage (X := LX) (Y := RX)
    (D.linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree X).hom

/-- Finite-dimensional push-down carries the literal radical inclusion of an
upstairs projective representable to the literal radical inclusion of the
corresponding downstairs projective representable. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k') hP
    (D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom ≫
        finiteDimensionalLinearCoyonedaRadicalInclusion (k := k')
          (C := DeckOrbitSkeleton C' G)
          (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
          (hP' (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')) =
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).map
          (finiteDimensionalLinearCoyonedaRadicalInclusion
            (k := k') X (hP X)) ≫
        (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
          (k := k') X (hP X)).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k') hP
  apply ObjectProperty.hom_ext
  change
    (D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom.hom ≫
        (finiteDimensionalLinearCoyonedaRadicalInclusion (k := k')
          (C := DeckOrbitSkeleton C' G)
          (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
          (hP' (Quotient.mk'' X : MulAction.orbitRel.Quotient G C'))).hom =
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).map
          (finiteDimensionalLinearCoyonedaRadicalInclusion
            (k := k') X (hP X))).hom ≫
        (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
          (k := k') X (hP X)).hom.hom
  rw [finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso_hom_hom,
    finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso_hom_hom]
  apply ObjectProperty.hom_ext
  change
    (D.linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom.hom ≫
        (radicalLinearCoyonedaInclusion (k := k')
          (C := DeckOrbitSkeleton C' G)
          (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')).hom =
      ((linearModuleOrbitSkeletonPushdown
          (k := k') (C := C') (G := G)).map
          (radicalLinearCoyonedaInclusion (k := k') X)).hom ≫
        (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
          (k := k') X).hom.hom
  rw [linearModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso_hom_hom,
    linearModuleOrbitSkeletonPushdownLinearCoyonedaIso_hom_hom]
  change
    (D.orbitSkeletonPushdownRadicalLinearCoyonedaIso
        (k' := k') hP hlocal hfree X).hom ≫
        radicalLinearCoyonedaInclusionNatTrans (k := k')
          (C := DeckOrbitSkeleton C' G)
          (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') =
      Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C') (G := G))
          (orbitPushdownNatTrans (A := Additive G)
            (radicalLinearCoyonedaInclusionNatTrans (k := k') X)) ≫
        (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k') X).hom
  exact D.orbitSkeletonPushdownRadicalLinearCoyonedaIso_hom_comp_inclusion
    (k' := k') hP hlocal hfree X

/-- Finite-dimensional skeletal push-down sends the radical inclusion of a
projective representable to a right almost-split morphism. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion_isRightAlmostSplit
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    IsRightAlmostSplit
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).map
        (finiteDimensionalLinearCoyonedaRadicalInclusion
          (k := k') X (hP X))) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')
  let m := finiteDimensionalLinearCoyonedaRadicalInclusion
    (k := k') X (hP X)
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k') hP
  let Q : DeckOrbitSkeleton C' G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  let mQ := finiteDimensionalLinearCoyonedaRadicalInclusion
    (k := k') Q (hP' Q)
  let eR :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree X
  let eP :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k') X (hP X)
  have hmQ : IsRightAlmostSplit mQ :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP' (D.orbitSkeleton_end_isLocalRing (k := k') hP hlocal hfree) Q
  have hleft : IsRightAlmostSplit (eR.hom ≫ mQ) :=
    MagnitudeConjecture.CategoryTheory.rightAlmostSplit_precomp_iso eR hmQ
  have hsquare : eR.hom ≫ mQ = P.map m ≫ eP.hom :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion
      (k' := k') hP hlocal hfree X
  have hcomp : IsRightAlmostSplit (P.map m ≫ eP.hom) := by
    rw [← hsquare]
    exact hleft
  have hback := hcomp.postcomp_iso eP.symm
  simpa [Category.assoc] using hback

set_option linter.unusedVariables false in
/-- Projective boundary adjacency: every indecomposable with an irreducible
map to the push-down of an upstairs projective representable is itself the
push-down of an upstairs indecomposable. -/
theorem exists_pushedIndecomposable_of_irreducible_to_projectivePushdown
    [IsMulTorsionFree G]
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    letI := isLinearModule_stableUnderShift (k := k') D.core
    letI := linearModuleCategoryHasShift (k := k') D.core
    letI := linearModuleCategoryAdditiveShift (R := k') D.core
    letI := linearModuleCategoryLinearShift (R := k') D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k')
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k')
    letI := trivialHasShift
      (LinearModuleCategory.{u', v', v', v'}
        (C := ShiftOrbitCategory C' (Additive G)) k') (Additive G)
    ∀ {Y : FiniteDimensionalModuleCategory.{u', v', v', v'}
        (C := DeckOrbitSkeleton C' G) k'}
      (hY : Indecomposable Y)
      (f : Y ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).obj
          (finiteDimensionalLinearCoyoneda (k := k') X (hP X)))
      (hf : IsIrreducibleMorphism f),
        ∃ Z : FiniteDimensionalModuleCategory.{u', v', v', v'}
            (C := C') k',
          Indecomposable Z ∧
            Nonempty
              ((D.finiteDimensionalModuleOrbitSkeletonPushdown
                (k := k')).obj Z ≅ Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  letI := isLinearModule_stableUnderShift (k := k') D.core
  letI := linearModuleCategoryHasShift (k := k') D.core
  letI := linearModuleCategoryAdditiveShift (R := k') D.core
  letI := linearModuleCategoryLinearShift (R := k') D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k')
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k')
  letI := trivialHasShift
    (LinearModuleCategory.{u', v', v', v'}
      (C := ShiftOrbitCategory C' (Additive G)) k') (Additive G)
  intro Y hY f hf
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')
  let M := finiteDimensionalLinearCoyoneda (k := k') X (hP X)
  let R := finiteDimensionalLinearCoyonedaRadical (k := k') X (hP X)
  let m : R ⟶ M :=
    finiteDimensionalLinearCoyonedaRadicalInclusion (k := k') X (hP X)
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k') hP
  let Q : DeckOrbitSkeleton C' G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  let mQ := finiteDimensionalLinearCoyonedaRadicalInclusion (k := k')
    (C := DeckOrbitSkeleton C' G) Q (hP' Q)
  let eR :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k') hP hlocal hfree X
  let eM :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k') X (hP X)
  have hmQ : IsRightAlmostSplit mQ :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP'
      (D.orbitSkeleton_end_isLocalRing (k := k') hP hlocal hfree) Q
  have hleft : IsRightAlmostSplit (eR.hom ≫ mQ) :=
    MagnitudeConjecture.CategoryTheory.rightAlmostSplit_precomp_iso eR hmQ
  have hsquare : eR.hom ≫ mQ = P.map m ≫ eM.hom := by
    exact D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion
      (k' := k') hP hlocal hfree X
  have hcomp : IsRightAlmostSplit (P.map m ≫ eM.hom) := by
    rw [← hsquare]
    exact hleft
  have hPm : IsRightAlmostSplit (P.map m) := by
    have hback := hcomp.postcomp_iso eM.symm
    simpa [Category.assoc] using hback
  apply
    MagnitudeConjecture.CategoryTheory.exists_essentialImage_of_irreducible_to_of_map_rightAlmostSplit
      P finiteDimensionalModule_finiteIndecomposableDecomposition
      (fun Z hZ ↦ ?_) m hPm hY
      (finiteDimensionalModule_end_isLocalRing k' Y hY) f hf
  exact
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k') Z hZ
        (D.finiteDimensionalModule_trivialStabilizer (k := k') Z hZ.1)

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
