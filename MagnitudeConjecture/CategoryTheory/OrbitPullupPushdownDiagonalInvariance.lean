import MagnitudeConjecture.CategoryTheory.OrbitPullupPushdownSummand
import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso

/-!
# Deck invariance of pull-up projector diagonals

A transformation defined downstairs in the shift-orbit category has
translation-conjugate diagonal blocks after pull-up to the explicit direct sum
of translates.  Hence invertibility of a diagonal block is invariant under
left deck translation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

variable (M : C ⥤ ModuleCat.{w} k)
variable [M.Additive] [M.Linear k]

private theorem diagonal_conjugacy
    {D : Type*} [Category D]
    {B S T U : D}
    (i : B ⟶ S) (f : S ⟶ T) (j : U ⟶ T)
    (eS : S ⟶ S) (eT : T ⟶ T)
    (p : T ⟶ U) (q : S ⟶ B) (v : B ⟶ U)
    (hlof : i ≫ f = v ≫ j)
    (hnat : f ≫ eT = eS ≫ f)
    (hcomponent : f ≫ p = q ≫ v) :
    v ≫ j ≫ eT ≫ p = i ≫ eS ≫ q ≫ v := by
  calc
    v ≫ j ≫ eT ≫ p = (v ≫ j) ≫ (eT ≫ p) := by
      simp only [Category.assoc]
    _ = (i ≫ f) ≫ (eT ≫ p) := by rw [hlof]
    _ = i ≫ ((f ≫ eT) ≫ p) := by simp only [Category.assoc]
    _ = i ≫ ((eS ≫ f) ≫ p) := by rw [hnat]
    _ = i ≫ (eS ≫ (f ≫ p)) := by simp only [Category.assoc]
    _ = i ≫ (eS ≫ (q ≫ v)) := by rw [hcomponent]
    _ = i ≫ eS ≫ q ≫ v := rfl

/-- Restrict a transformation of modules on the shift-orbit category to
degree-zero arrows upstairs. -/
noncomputable def orbitPullupNatTrans
    {N P : ShiftOrbitCategory C A ⥤ ModuleCat.{w} k}
    (α : N ⟶ P) :
    ShiftOrbitCategory.identityComponentFunctor ⋙ N ⟶
      ShiftOrbitCategory.identityComponentFunctor ⋙ P :=
  Functor.whiskerLeft ShiftOrbitCategory.identityComponentFunctor α

/-- Transport the degree-zero restriction of a push-down endomorphism to the
explicit direct-sum model of pull-up. -/
noncomputable def orbitPullupPushdownEnd
    (α : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) M) :
    orbitPullupPushdown (A := A) M ⟶
      orbitPullupPushdown (A := A) M :=
  (orbitPullupPushdownIso (A := A) M).hom ≫
    orbitPullupNatTrans (A := A) α ≫
    (orbitPullupPushdownIso (A := A) M).inv

/-- Pull back an inclusion into a push-down module and transport its target
to the explicit direct-sum model. -/
noncomputable def orbitPullupPushdownInclusion
    {N : ShiftOrbitCategory C A ⥤ ModuleCat.{w} k}
    (j : N ⟶ orbitPushdown (A := A) M) :
    (ShiftOrbitCategory.identityComponentFunctor ⋙ N) ⟶
      orbitPullupPushdown (A := A) M :=
  orbitPullupNatTrans (A := A) j ≫
    (orbitPullupPushdownIso (A := A) M).inv

/-- Pull back a retraction from a push-down module and transport its source
from the explicit direct-sum model. -/
noncomputable def orbitPullupPushdownRetraction
    {N : ShiftOrbitCategory C A ⥤ ModuleCat.{w} k}
    (r : orbitPushdown (A := A) M ⟶ N) :
    orbitPullupPushdown (A := A) M ⟶
      (ShiftOrbitCategory.identityComponentFunctor ⋙ N) :=
  (orbitPullupPushdownIso (A := A) M).hom ≫
    orbitPullupNatTrans (A := A) r

@[reassoc]
theorem orbitPullupPushdownInclusion_retraction
    {N : ShiftOrbitCategory C A ⥤ ModuleCat.{w} k}
    (j : N ⟶ orbitPushdown (A := A) M)
    (r : orbitPushdown (A := A) M ⟶ N)
    (hjr : j ≫ r = 𝟙 N) :
    orbitPullupPushdownInclusion (A := A) M j ≫
        orbitPullupPushdownRetraction (A := A) M r =
      𝟙 _ := by
  simp [orbitPullupPushdownInclusion, orbitPullupPushdownRetraction,
    orbitPullupNatTrans, Category.assoc, ← Functor.whiskerLeft_comp, hjr]

/-- The projector of a pulled-back retract is the transported pull-up of its
downstairs projector. -/
theorem orbitPullupPushdownRetraction_inclusion
    {N : ShiftOrbitCategory C A ⥤ ModuleCat.{w} k}
    (j : N ⟶ orbitPushdown (A := A) M)
    (r : orbitPushdown (A := A) M ⟶ N) :
    orbitPullupPushdownRetraction (A := A) M r ≫
        orbitPullupPushdownInclusion (A := A) M j =
      orbitPullupPushdownEnd (A := A) M (r ≫ j) := by
  simp [orbitPullupPushdownInclusion, orbitPullupPushdownRetraction,
    orbitPullupPushdownEnd, orbitPullupNatTrans, Category.assoc,
    -Functor.whiskerLeft_comp]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp]

theorem orbitPullupPushdownEnd_add
    (α β : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) M) :
    orbitPullupPushdownEnd (A := A) M (α + β) =
      orbitPullupPushdownEnd (A := A) M α +
        orbitPullupPushdownEnd (A := A) M β := by
  ext X
  rfl

@[simp]
theorem orbitPullupPushdownEnd_id :
    orbitPullupPushdownEnd (A := A) M (𝟙 _) = 𝟙 _ := by
  simp [orbitPullupPushdownEnd, orbitPullupNatTrans]

omit [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Linear k] in
/-- Restriction along the degree-zero orbit functor reflects isomorphisms,
because it is the identity on objects. -/
theorem isIso_of_orbitPullupNatTrans_isIso
    {N P : ShiftOrbitCategory C A ⥤ ModuleCat.{w} k}
    (α : N ⟶ P) [IsIso (orbitPullupNatTrans (A := A) α)] :
    IsIso α := by
  letI appIso (X : ShiftOrbitCategory C A) : IsIso (α.app X) := by
    change IsIso
      ((orbitPullupNatTrans (A := A) α).app (show C from X))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- An isomorphism after pulled-back inclusion was transported to the explicit
sum already came from an isomorphism downstairs. -/
theorem isIso_of_orbitPullupPushdownInclusion_isIso
    {N : ShiftOrbitCategory C A ⥤ ModuleCat.{w} k}
    (j : N ⟶ orbitPushdown (A := A) M)
    [IsIso (orbitPullupPushdownInclusion (A := A) M j)] :
    IsIso j := by
  haveI hcomp : IsIso
      (orbitPullupNatTrans (A := A) j ≫
        (orbitPullupPushdownIso (A := A) M).inv) := by
    change IsIso (orbitPullupPushdownInclusion (A := A) M j)
    infer_instance
  haveI : IsIso (orbitPullupNatTrans (A := A) j) :=
    IsIso.of_isIso_comp_right _
      (orbitPullupPushdownIso (A := A) M).inv
  exact isIso_of_orbitPullupNatTrans_isIso (A := A) j

/-- The `b`-th diagonal block of a pulled-back push-down endomorphism. -/
noncomputable def orbitPullupPushdownDiagonal
    (α : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) M)
    (b : A) :
    orbitPullupPushdownTranslate (A := A) M b ⟶
      orbitPullupPushdownTranslate (A := A) M b :=
  orbitPullupPushdownTranslateLof (A := A) M b ≫
    orbitPullupPushdownEnd (A := A) M α ≫
    orbitPullupPushdownTranslateComponent (A := A) M b

/-- The homogeneous orbit isomorphism from `X⟦a⟧` to `X` carries the
`b`-summand to the `(a+b)`-summand. -/
noncomputable def orbitPushdownShiftSummandHom
    (a b : A) (X : C) :
    (orbitPullupPushdownTranslate (A := A) M b).obj
        ((shiftFunctor C a).obj X) ⟶
      (orbitPullupPushdownTranslate (A := A) M (a + b)).obj X :=
  ModuleCat.ofHom <| orbitPushdownComponent M a b
    (show ShiftHom ((shiftFunctor C a).obj X) X a from 𝟙 _)

instance orbitPushdownShiftSummandHom_isIso
    (a b : A) (X : C) :
    IsIso (orbitPushdownShiftSummandHom M a b X) := by
  let f : (shiftFunctor C b).obj ((shiftFunctor C a).obj X) ⟶
      (shiftFunctor C (a + b)).obj X :=
    orbitPushdownArrow' rfl
      (show ShiftHom ((shiftFunctor C a).obj X) X a from 𝟙 _)
  haveI : IsIso f := by
    rw [show f = (shiftFunctorAdd' C a b (a + b) rfl).inv.app X by
      simp [f, orbitPushdownArrow']]
    apply IsIso.mk
    exact
      ⟨(shiftFunctorAdd' C a b (a + b) rfl).hom.app X,
        Iso.inv_hom_id_app (shiftFunctorAdd' C a b (a + b) rfl) X,
        Iso.hom_inv_id_app (shiftFunctorAdd' C a b (a + b) rfl) X⟩
  change IsIso (M.map f)
  infer_instance

@[reassoc]
theorem orbitPullupPushdownTranslateLof_shiftOrbitFromShift
    (a b : A) (X : C) :
    (orbitPullupPushdownTranslateLof (A := A) M b).app
          ((shiftFunctor C a).obj X) ≫
        (orbitPushdown (A := A) M).map (shiftOrbitFromShift X a) =
      orbitPushdownShiftSummandHom M a b X ≫
        (orbitPullupPushdownTranslateLof (A := A) M (a + b)).app X := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    orbitPushdownMapLinear M (shiftOrbitFromShift X a)
        (orbitPushdownLof M ((shiftFunctor C a).obj X) b x) =
      orbitPushdownLof M X (a + b)
        (orbitPushdownComponent M a b
          (show ShiftHom ((shiftFunctor C a).obj X) X a from 𝟙 _) x)
  rw [shiftOrbitFromShift, orbitPushdownMapLinear_of,
    orbitPushdownHomogeneousMap_lof]

@[reassoc]
theorem shiftOrbitFromShift_orbitPullupPushdownTranslateComponent
    (a b : A) (X : C) :
    (orbitPushdown (A := A) M).map (shiftOrbitFromShift X a) ≫
        (orbitPullupPushdownTranslateComponent (A := A) M (a + b)).app X =
      (orbitPullupPushdownTranslateComponent (A := A) M b).app
          ((shiftFunctor C a).obj X) ≫
        orbitPushdownShiftSummandHom M a b X := by
  classical
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro c
  apply LinearMap.ext
  intro x
  change
    DirectSum.component k A _ (a + b)
        (orbitPushdownMapLinear M (shiftOrbitFromShift X a)
          (orbitPushdownLof M ((shiftFunctor C a).obj X) c x)) =
      orbitPushdownComponent M a b
          (show ShiftHom ((shiftFunctor C a).obj X) X a from 𝟙 _)
        (DirectSum.component k A _ b
          (orbitPushdownLof M ((shiftFunctor C a).obj X) c x))
  rw [shiftOrbitFromShift, orbitPushdownMapLinear_of,
    orbitPushdownHomogeneousMap_lof]
  by_cases hcb : c = b
  · subst c
    simp [orbitPushdownLof]
  · have hacb : a + c ≠ a + b := fun h ↦ hcb (add_left_cancel h)
    simp [orbitPushdownLof, DirectSum.component.of, hcb, hacb]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality downstairs conjugates the `b`-diagonal block at `X⟦a⟧`
to the `(a+b)`-diagonal block at `X`. -/
theorem orbitPullupPushdownDiagonal_shift
    (α : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) M)
    (a b : A) (X : C) :
    orbitPushdownShiftSummandHom M a b X ≫
        (orbitPullupPushdownDiagonal (A := A) M α (a + b)).app X =
      (orbitPullupPushdownDiagonal (A := A) M α b).app
          ((shiftFunctor C a).obj X) ≫
        orbitPushdownShiftSummandHom M a b X := by
  dsimp only [orbitPullupPushdownDiagonal, orbitPullupPushdownEnd,
    orbitPullupNatTrans, orbitPullupPushdownIso, NatTrans.comp_app,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp]
  exact diagonal_conjugacy
    ((orbitPullupPushdownTranslateLof (A := A) M b).app
      ((shiftFunctor C a).obj X))
    ((orbitPushdown (A := A) M).map (shiftOrbitFromShift X a))
    ((orbitPullupPushdownTranslateLof (A := A) M (a + b)).app X)
    (α.app (show ShiftOrbitCategory C A from (shiftFunctor C a).obj X))
    (α.app (show ShiftOrbitCategory C A from X))
    ((orbitPullupPushdownTranslateComponent (A := A) M (a + b)).app X)
    ((orbitPullupPushdownTranslateComponent (A := A) M b).app
      ((shiftFunctor C a).obj X))
    (orbitPushdownShiftSummandHom M a b X)
    (orbitPullupPushdownTranslateLof_shiftOrbitFromShift
      (A := A) M a b X)
    (α.naturality (shiftOrbitFromShift X a))
    (shiftOrbitFromShift_orbitPullupPushdownTranslateComponent
      (A := A) M a b X)

set_option backward.isDefEq.respectTransparency false in
/-- Invertibility of a pulled-back diagonal block propagates under left deck
translation. -/
theorem orbitPullupPushdownDiagonal_isIso_add_left
    (α : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) M)
    (a b : A)
    (hb : IsIso (orbitPullupPushdownDiagonal (A := A) M α b)) :
    IsIso (orbitPullupPushdownDiagonal (A := A) M α (a + b)) := by
  letI : IsIso (orbitPullupPushdownDiagonal (A := A) M α b) := hb
  letI appIso (X : C) : IsIso
      ((orbitPullupPushdownDiagonal (A := A) M α (a + b)).app X) := by
    let v := orbitPushdownShiftSummandHom M a b X
    letI : IsIso v := orbitPushdownShiftSummandHom_isIso M a b X
    have hconj := orbitPullupPushdownDiagonal_shift (A := A) M α a b X
    haveI hcomp : IsIso
        (v ≫ (orbitPullupPushdownDiagonal (A := A) M α (a + b)).app X) := by
      rw [hconj]
      infer_instance
    exact IsIso.of_isIso_comp_left v _
  exact NatIso.isIso_of_isIso_app _

/-- The unit-diagonal predicate of every downstairs endomorphism is invariant
under left deck translation after pull-up. -/
theorem orbitPullupPushdownDiagonal_isIso_iff_add_left
    (α : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) M)
    (a b : A) :
    IsIso (orbitPullupPushdownDiagonal (A := A) M α b) ↔
      IsIso (orbitPullupPushdownDiagonal (A := A) M α (a + b)) := by
  constructor
  · exact orbitPullupPushdownDiagonal_isIso_add_left
      (A := A) M α a b
  · intro hab
    have h := orbitPullupPushdownDiagonal_isIso_add_left
      (A := A) M α (-a) (a + b) hab
    rw [show -a + (a + b) = b by simp] at h
    exact h

/-- Complementary retracts of a push-down module pull back to complementary
retracts of the translate sum.  Hence, under the Krull--Schmidt hypotheses on
the translates, one of the original downstairs inclusions is an isomorphism.
This is the invariant-summand core of Gabriel's indecomposability argument. -/
theorem orbitPushdown_one_retract_inclusion_isIso
    {L Q : ShiftOrbitCategory C A ⥤ ModuleCat.{w} k}
    (j : L ⟶ orbitPushdown (A := A) M)
    (r : orbitPushdown (A := A) M ⟶ L)
    (hjr : j ≫ r = 𝟙 L)
    (j' : Q ⟶ orbitPushdown (A := A) M)
    (r' : orbitPushdown (A := A) M ⟶ Q)
    (hj'r' : j' ≫ r' = 𝟙 Q)
    (htotal : r ≫ j + r' ≫ j' = 𝟙 (orbitPushdown (A := A) M))
    (hindecomp : ∀ b : A,
      Indecomposable (orbitPullupPushdownTranslate (A := A) M b))
    (hlocal : ∀ b : A,
      IsLocalRing (End
        (orbitPullupPushdownTranslate (A := A) M b)))
    (hpair : ∀ b c : A, b ≠ c →
      ¬ Nonempty
        (orbitPullupPushdownTranslate (A := A) M b ≅
          orbitPullupPushdownTranslate (A := A) M c)) :
    IsIso j ∨ IsIso j' := by
  let J := orbitPullupPushdownInclusion (A := A) M j
  let R := orbitPullupPushdownRetraction (A := A) M r
  let J' := orbitPullupPushdownInclusion (A := A) M j'
  let R' := orbitPullupPushdownRetraction (A := A) M r'
  have hJR : J ≫ R = 𝟙 _ := by
    exact orbitPullupPushdownInclusion_retraction
      (A := A) M j r hjr
  have hJ'R' : J' ≫ R' = 𝟙 _ := by
    exact orbitPullupPushdownInclusion_retraction
      (A := A) M j' r' hj'r'
  have hprojector : R ≫ J =
      orbitPullupPushdownEnd (A := A) M (r ≫ j) := by
    exact orbitPullupPushdownRetraction_inclusion
      (A := A) M j r
  have hprojector' : R' ≫ J' =
      orbitPullupPushdownEnd (A := A) M (r' ≫ j') := by
    exact orbitPullupPushdownRetraction_inclusion
      (A := A) M j' r'
  have htotalUp : R ≫ J + R' ≫ J' = 𝟙 _ := by
    rw [hprojector, hprojector', ← orbitPullupPushdownEnd_add,
      htotal, orbitPullupPushdownEnd_id]
  have hclassification :=
    orbitPullupPushdown_one_retract_inclusion_isIso_of_invariant_diagonal
      (A := A) M J R hJR J' R' hJ'R' htotalUp
        hindecomp hlocal hpair (fun a b ↦ by
          have hdiag (c : A) :
              orbitPullupPushdownTranslateLof (A := A) M c ≫
                  R ≫ J ≫
                  orbitPullupPushdownTranslateComponent (A := A) M c =
                orbitPullupPushdownDiagonal (A := A) M (r ≫ j) c := by
            calc
              _ = orbitPullupPushdownTranslateLof (A := A) M c ≫
                  (R ≫ J) ≫
                  orbitPullupPushdownTranslateComponent (A := A) M c := by
                    simp only [Category.assoc]
              _ = orbitPullupPushdownTranslateLof (A := A) M c ≫
                  orbitPullupPushdownEnd (A := A) M (r ≫ j) ≫
                  orbitPullupPushdownTranslateComponent (A := A) M c := by
                    rw [hprojector]
              _ = orbitPullupPushdownDiagonal
                  (A := A) M (r ≫ j) c := rfl
          rw [hdiag b, hdiag (a + b)]
          exact orbitPullupPushdownDiagonal_isIso_iff_add_left
            (A := A) M (r ≫ j) a b)
  rcases hclassification with hJ | hJ'
  · left
    letI : IsIso J := hJ
    exact isIso_of_orbitPullupPushdownInclusion_isIso
      (A := A) M j
  · right
    letI : IsIso J' := hJ'
    exact isIso_of_orbitPullupPushdownInclusion_isIso
      (A := A) M j'

end MagnitudeConjecture.CoveringHom
