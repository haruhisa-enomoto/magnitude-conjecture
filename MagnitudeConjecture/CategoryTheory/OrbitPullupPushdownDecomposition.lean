import MagnitudeConjecture.CategoryTheory.OrbitPushdownFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Pull-up of Gabriel push-down as a sum of translates

The pull-up of an orbit push-down is the coproduct of all translated copies
of the original module.  This is the displayed decomposition used at the
start of Gabriel's Lemma 3.5.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- The translate indexed by `b` in the pull-up of an orbit push-down. -/
abbrev orbitPullupPushdownTranslate
    (M : C ⥤ ModuleCat.{max w uM} k) (b : A) :
    C ⥤ ModuleCat.{max w uM} k :=
  shiftFunctor C b ⋙ M

variable (M : C ⥤ ModuleCat.{max w uM} k)
variable [M.Additive] [M.Linear k]

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- A degree-zero orbit arrow acts diagonally on every translated summand. -/
theorem orbitPushdownArrow_zero_of_hasShift
    {X Y : C} (h : X ⟶ Y) (b : A) :
    orbitPushdownArrow' (zero_add b) (shiftHomZero (A := A) h) =
      (shiftFunctor C b).map h := by
  simp only [orbitPushdownArrow', shiftHomZero,
    CategoryTheory.ShiftedHom.mk₀,
    shiftFunctorAdd'_zero_add_inv_app, Functor.map_comp,
    Category.assoc]
  have hz (h0 : (0 : A) = 0) :
      shiftFunctorZero' C 0 h0 = shiftFunctorZero C A := by
    rw [Subsingleton.elim h0 rfl]
    ext
    simp [shiftFunctorZero']
  rw [hz]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  apply congrArg (fun q ↦ (shiftFunctor C b).map q)
  exact Category.comp_id h

set_option backward.isDefEq.respectTransparency false in
theorem orbitPullupPushdownTranslate_lof_naturality
    {X Y : C} (h : X ⟶ Y) (b : A) :
    (orbitPushdownMapLinear M
        (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))).comp
        (orbitPushdownLof M X b) =
      (orbitPushdownLof M Y b).comp
        (M.map ((shiftFunctor C b).map h)).hom := by
  classical
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [orbitPushdownMapLinear_of, orbitPushdownHomogeneousMap_lof]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add b)
  exact
    (orbitPushdownComponent_apply_heq_component'_apply M
      (zero_add b) (shiftHomZero (A := A) h) x).trans
      (heq_of_eq (by
        change M.map
            (orbitPushdownArrow' (zero_add b)
              (shiftHomZero (A := A) h)) x = _
        rw [orbitPushdownArrow_zero_of_hasShift]))

/-- Restrict orbit push-down to degree-zero arrows, presented with its
objectwise direct sums definitionally visible. -/
noncomputable def orbitPullupPushdown : C ⥤ ModuleCat.{max w uM} k where
  obj X := ModuleCat.of k (orbitPushdownValue (A := A) M X)
  map {X Y} h := ModuleCat.ofHom <|
    orbitPushdownMapLinear M
      (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))
  map_id X := by
    apply ModuleCat.hom_ext
    change orbitPushdownMapLinear M
        (shiftOrbitOf X X 0 (shiftHomZero (A := A) (𝟙 X))) =
      LinearMap.id
    rw [shiftHomZero_id, orbitPushdownMapLinear_of,
      orbitPushdownHomogeneousMap_id]
  map_comp f g := by
    apply ModuleCat.hom_ext
    change orbitPushdownMapLinear M
        (shiftOrbitOf _ _ 0 (shiftHomZero (A := A) (f ≫ g))) =
      (orbitPushdownMapLinear M
          (shiftOrbitOf _ _ 0 (shiftHomZero (A := A) g))).comp
        (orbitPushdownMapLinear M
          (shiftOrbitOf _ _ 0 (shiftHomZero (A := A) f)))
    rw [← orbitPushdownMapLinear_comp,
      shiftOrbitComp_zero_zero]

/-- The explicit degree-zero restriction is the underlying functor of
pull-up applied to push-down. -/
noncomputable def orbitPullupPushdownIso :
    orbitPullupPushdown (A := A) M ≅
      ShiftOrbitCategory.identityComponentFunctor ⋙
        orbitPushdown (A := A) M := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · change ModuleCat.of k (orbitPushdownValue (A := A) M X) ≅
      ModuleCat.of k (orbitPushdownValue (A := A) M X)
    exact Iso.refl _
  · intro X Y h
    rfl

instance orbitPullupPushdown_additive :
    (orbitPullupPushdown (A := A) M).Additive :=
  Functor.additive_of_iso (orbitPullupPushdownIso M).symm

instance orbitPullupPushdown_linear :
    (orbitPullupPushdown (A := A) M).Linear k :=
  Functor.linear_of_iso k (orbitPullupPushdownIso M).symm

/-- Inclusion of one translate into the pull-up of the push-down. -/
noncomputable def orbitPullupPushdownTranslateLof (b : A) :
    orbitPullupPushdownTranslate (A := A) M b ⟶
      orbitPullupPushdown (A := A) M :=
  { app := fun X ↦ ModuleCat.ofHom (orbitPushdownLof M X b)
    naturality := fun {X Y} h ↦ by
      apply ModuleCat.hom_ext
      exact (orbitPullupPushdownTranslate_lof_naturality M h b).symm }

/-- Projection from the pull-up direct sum to one translated summand. -/
noncomputable def orbitPullupPushdownTranslateComponent (b : A) :
    orbitPullupPushdown (A := A) M ⟶
      orbitPullupPushdownTranslate (A := A) M b :=
  { app := fun X ↦ ModuleCat.ofHom <|
      DirectSum.component k A
        (fun c ↦ M.obj ((shiftFunctor C c).obj X)) b
    naturality := fun {X Y} h ↦ by
      classical
      apply ModuleCat.hom_ext
      apply DirectSum.linearMap_ext
      intro c
      apply LinearMap.ext
      intro x
      have hmap := LinearMap.congr_fun
        (orbitPullupPushdownTranslate_lof_naturality M h c) x
      change
        orbitPushdownMapLinear M
            (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))
            (orbitPushdownLof M X c x) =
          orbitPushdownLof M Y c
            (M.map ((shiftFunctor C c).map h) x) at hmap
      change
        DirectSum.component k A _ b
            (orbitPushdownMapLinear M
              (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))
              (orbitPushdownLof M X c x)) =
          M.map ((shiftFunctor C b).map h)
            (DirectSum.component k A _ b
              (orbitPushdownLof M X c x))
      rw [hmap]
      by_cases hcb : c = b
      · subst c
        simp [orbitPushdownLof]
      · simp [orbitPushdownLof, DirectSum.component.of, hcb] }

@[reassoc (attr := simp)]
theorem orbitPullupPushdownTranslateLof_component_self (b : A) :
    orbitPullupPushdownTranslateLof (A := A) M b ≫
        orbitPullupPushdownTranslateComponent (A := A) M b =
      𝟙 _ := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change DirectSum.component k A _ b
      (orbitPushdownLof M X b x) = x
  rw [orbitPushdownLof, DirectSum.component.lof_self]

@[reassoc]
theorem orbitPullupPushdownTranslateLof_component_ne
    {b c : A} (hbc : b ≠ c) :
    orbitPullupPushdownTranslateLof (A := A) M b ≫
        orbitPullupPushdownTranslateComponent (A := A) M c =
      0 := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change DirectSum.component k A _ c
      (orbitPushdownLof M X b x) = 0
  rw [orbitPushdownLof, DirectSum.component.of]
  simp [hbc]

/-- The canonical cocone of all translates into the pull-up of the
push-down. -/
noncomputable def orbitPullupPushdownTranslateCofan :
    Cofan (fun b : A ↦ orbitPullupPushdownTranslate (A := A) M b) :=
  Cofan.mk _ (orbitPullupPushdownTranslateLof (A := A) M)

/-- A leg of a translate cocone at one object, with its source written in
the literal family used by `orbitPushdownValue`. -/
abbrev orbitPullupPushdownTranslateCofanAppHom
    (t : Cofan (fun b : A ↦
      orbitPullupPushdownTranslate (A := A) M b))
    (X : C) (b : A) :
    M.obj ((shiftFunctor C b).obj X) →ₗ[k] t.pt.obj X :=
  (t.inj b).app X |>.hom

/-- A family of maps out of all translates extends uniquely over the
pull-up of the push-down. -/
noncomputable def orbitPullupPushdownTranslateDesc
    (t : Cofan (fun b : A ↦
      orbitPullupPushdownTranslate (A := A) M b)) :
    (orbitPullupPushdownTranslateCofan (A := A) M).pt ⟶ t.pt := by
  classical
  exact
    { app := fun X ↦ ModuleCat.ofHom <|
        DirectSum.toModule k A _ fun b ↦
          orbitPullupPushdownTranslateCofanAppHom M t X b
      naturality := fun {X Y} h ↦ by
        apply ModuleCat.hom_ext
        apply DirectSum.linearMap_ext
        intro b
        apply LinearMap.ext
        intro x
        have hzero := LinearMap.congr_fun
          (orbitPullupPushdownTranslate_lof_naturality M h b) x
        change
          orbitPushdownMapLinear M
              (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))
              (orbitPushdownLof M X b x) =
            orbitPushdownLof M Y b
              (M.map ((shiftFunctor C b).map h) x) at hzero
        change
          (DirectSum.toModule k A _
              (orbitPullupPushdownTranslateCofanAppHom M t Y))
              (orbitPushdownMapLinear M
                (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))
                (orbitPushdownLof M X b x)) =
            (t.pt.map h).hom
              ((DirectSum.toModule k A _
                (orbitPullupPushdownTranslateCofanAppHom M t X))
                (orbitPushdownLof M X b x))
        rw [hzero]
        have hdescY :
            (DirectSum.toModule k A _
                (orbitPullupPushdownTranslateCofanAppHom M t Y))
                (orbitPushdownLof M Y b
                  (M.map ((shiftFunctor C b).map h) x)) =
              orbitPullupPushdownTranslateCofanAppHom M t Y b
                (M.map ((shiftFunctor C b).map h) x) := by
          rw [orbitPushdownLof, DirectSum.toModule_lof]
        have hdescX :
            (DirectSum.toModule k A _
                (orbitPullupPushdownTranslateCofanAppHom M t X))
                (orbitPushdownLof M X b x) =
              orbitPullupPushdownTranslateCofanAppHom M t X b x := by
          rw [orbitPushdownLof, DirectSum.toModule_lof]
        rw [hdescY, hdescX]
        exact congrArg (fun f ↦ f.hom x) ((t.inj b).naturality h) }

@[reassoc]
theorem orbitPullupPushdownTranslateLof_desc
    (t : Cofan (fun b : A ↦
      orbitPullupPushdownTranslate (A := A) M b))
    (b : A) :
    orbitPullupPushdownTranslateLof (A := A) M b ≫
        orbitPullupPushdownTranslateDesc (A := A) M t =
      t.inj b := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    (DirectSum.toModule k A _
      (orbitPullupPushdownTranslateCofanAppHom M t X))
        (orbitPushdownLof M X b x) =
      (t.inj b).app X x
  rw [orbitPushdownLof, DirectSum.toModule_lof]

/-- The canonical translate cocone is a categorical coproduct. -/
noncomputable def orbitPullupPushdownTranslateCofanIsColimit :
    IsColimit (orbitPullupPushdownTranslateCofan (A := A) M) := by
  classical
  refine Cofan.IsColimit.mk _
    (orbitPullupPushdownTranslateDesc (A := A) M) ?_ ?_
  · intro t b
    exact orbitPullupPushdownTranslateLof_desc (A := A) M t b
  · intro t f hf
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro b
    apply LinearMap.ext
    intro x
    have hbX := congrArg (fun q ↦ q.app X) (hf b)
    have hval := congrArg (fun q ↦ q.hom x) hbX
    change
      f.app X (orbitPushdownLof M X b x) =
        (t.inj b).app X x at hval
    change
      f.app X (orbitPushdownLof M X b x) =
        (DirectSum.toModule k A _
          (orbitPullupPushdownTranslateCofanAppHom M t X))
            (orbitPushdownLof M X b x)
    rw [orbitPushdownLof, DirectSum.toModule_lof]
    exact hval

variable
  (M₀ : LinearModuleCategory.{u, v, uK, max w uM} (C := C) k)

/-- The translated summand, bundled again as a linear module. -/
abbrev linearOrbitPullupPushdownTranslate (b : A) :
    LinearModuleCategory.{u, v, uK, max w uM} (C := C) k :=
  ⟨orbitPullupPushdownTranslate (A := A) M₀.obj b,
    inferInstance, inferInstance⟩

/-- The translate cocone in the full category of linear modules. -/
noncomputable def linearOrbitPullupPushdownTranslateCofan :
    Cofan (fun b : A ↦
      linearOrbitPullupPushdownTranslate (A := A) M₀ b) :=
  Cofan.mk
    ⟨orbitPullupPushdown (A := A) M₀.obj,
      inferInstance, inferInstance⟩
    (fun b ↦ ObjectProperty.homMk
      (orbitPullupPushdownTranslateLof (A := A) M₀.obj b))

/-- Forget the linear-module bundling from a translate cocone. -/
noncomputable def linearOrbitPullupPushdownTranslateCofanUnderlying
    (t : Cofan (fun b : A ↦
      linearOrbitPullupPushdownTranslate (A := A) M₀ b)) :
    Cofan (fun b : A ↦
      orbitPullupPushdownTranslate (A := A) M₀.obj b) :=
  Cofan.mk t.pt.obj (fun b ↦ (t.inj b).hom)

/-- The pull-up of push-down is also the coproduct of the translates inside
the full category of linear modules. -/
noncomputable def linearOrbitPullupPushdownTranslateCofanIsColimit :
    IsColimit (linearOrbitPullupPushdownTranslateCofan (A := A) M₀) := by
  let hc := orbitPullupPushdownTranslateCofanIsColimit
    (A := A) M₀.obj
  refine Cofan.IsColimit.mk _ (fun t ↦ ObjectProperty.homMk <|
    hc.desc (linearOrbitPullupPushdownTranslateCofanUnderlying
      (A := A) M₀ t)) ?_ ?_
  · intro t b
    apply ObjectProperty.hom_ext
    exact hc.fac
      (linearOrbitPullupPushdownTranslateCofanUnderlying
        (A := A) M₀ t) ⟨b⟩
  · intro t f hf
    apply ObjectProperty.hom_ext
    apply hc.uniq
      (linearOrbitPullupPushdownTranslateCofanUnderlying
        (A := A) M₀ t) f.hom
    intro b
    exact congrArg (fun q ↦ q.hom) (hf b.as)

end MagnitudeConjecture.CoveringHom
