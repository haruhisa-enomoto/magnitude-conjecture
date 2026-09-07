import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownExact
import MagnitudeConjecture.CategoryTheory.OrbitPushdownCorepresentable
import Mathlib.CategoryTheory.Preadditive.Mat

/-!
# Orbit push-down and finite projective Nakayama data

The matrix category `Mat_ Cᵒᵖ` is the finite additive envelope of the
representing objects.  Its linear-coyoneda lift consists of finite sums of
projective representables, while the corresponding dual-Yoneda lift consists
of their Nakayama images.  This file extends the objectwise orbit push-down
comparisons to those additive envelopes.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uD vD uE vE

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- The linear coyoneda functor with codomain restricted to additive linear
modules. -/
noncomputable def linearCoyonedaLinearModuleFunctor :
    Cᵒᵖ ⥤ LinearModuleCategory.{u, v, uK, v} (C := C) k :=
  ObjectProperty.lift (IsLinearModule (C := C) k)
    (linearCoyoneda k C) (fun X ↦ by
      exact ⟨inferInstance,
        linearCoyoneda_obj_linear (k := k) X.unop⟩)

instance linearCoyonedaLinearModuleFunctor_additive :
    (linearCoyonedaLinearModuleFunctor (k := k) (C := C)).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    change (f.unop + g.unop) ≫ q =
      f.unop ≫ q + g.unop ≫ q
    rw [Preadditive.add_comp]

instance linearCoyonedaLinearModuleFunctor_full :
    (linearCoyonedaLinearModuleFunctor (k := k) (C := C)).Full := by
  dsimp only [linearCoyonedaLinearModuleFunctor]
  infer_instance

/-- The coefficient-dual corepresentables as a functor on the opposite
category of representing objects. -/
noncomputable def dualLinearYonedaFunctor : Cᵒᵖ ⥤ C ⥤ ModuleCat k where
  obj X := dualLinearYoneda (k := k) X.unop
  map f := dualLinearYonedaMap (k := k) f.unop
  map_id X := by
    simp
  map_comp f g := by
    simp

instance dualLinearYonedaFunctor_additive :
    (dualLinearYonedaFunctor (k := k) (C := C)).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual k (Z ⟶ X.unop) at phi
    apply LinearMap.ext
    intro q
    change phi (q ≫ (f.unop + g.unop)) =
      phi (q ≫ f.unop) + phi (q ≫ g.unop)
    rw [Preadditive.comp_add, map_add]

/-- The dual corepresentable functor with codomain restricted to additive
linear modules. -/
noncomputable def dualLinearYonedaLinearModuleFunctor :
    Cᵒᵖ ⥤ LinearModuleCategory (C := C) k :=
  ObjectProperty.lift (IsLinearModule (C := C) k)
    (dualLinearYonedaFunctor (k := k) (C := C)) (fun X ↦ by
      exact ⟨dualLinearYoneda_additive (k := k) X.unop,
        dualLinearYoneda_linear (k := k) X.unop⟩)

instance dualLinearYonedaLinearModuleFunctor_additive :
    (dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    exact (dualLinearYonedaFunctor (k := k) (C := C)).map_add

/-- Finite projective representables, functorially bundled in the literal
finite-dimensional module category. -/
noncomputable def finiteDimensionalLinearCoyonedaFunctor
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    Cᵒᵖ ⥤ FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
  ObjectProperty.lift (IsFiniteDimensionalModule (C := C) k)
    (linearCoyonedaLinearModuleFunctor (k := k) (C := C))
    (fun X ↦ hP X.unop)

instance finiteDimensionalLinearCoyonedaFunctor_additive
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    exact (linearCoyonedaLinearModuleFunctor (k := k) (C := C)).map_add

instance finiteDimensionalLinearCoyonedaFunctor_faithful
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).Faithful := by
  dsimp [finiteDimensionalLinearCoyonedaFunctor,
    linearCoyonedaLinearModuleFunctor]
  infer_instance

instance finiteDimensionalLinearCoyonedaFunctor_full
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).Full := by
  dsimp only [finiteDimensionalLinearCoyonedaFunctor]
  infer_instance

/-- Finite dual corepresentables, functorially bundled in the literal
finite-dimensional module category. -/
noncomputable def finiteDimensionalDualLinearYonedaFunctor
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    Cᵒᵖ ⥤ FiniteDimensionalModuleCategory (C := C) k :=
  ObjectProperty.lift (IsFiniteDimensionalModule (C := C) k)
    (dualLinearYonedaLinearModuleFunctor (k := k) (C := C))
    (fun X ↦ hI X.unop)

instance finiteDimensionalDualLinearYonedaFunctor_additive
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    (finiteDimensionalDualLinearYonedaFunctor (k := k) hI).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    exact (dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).map_add

section FiniteMatrixLift

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [HasFiniteBiproducts D]

/-- Universe-polymorphic finite additive-envelope lift.  This is the same
matrix construction as `Mat_.lift`, without its same-universe restriction on
the target category. -/
@[simps]
noncomputable def finiteMatrixLift (F : C ⥤ D) [F.Additive] :
    Mat_ C ⥤ D where
  obj X := ⨁ fun i ↦ F.obj (X.X i)
  map f := biproduct.matrix fun i j ↦ F.map (f i j)
  map_id X := by
    ext i j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  map_comp f g := by
    classical
    apply (biproduct.matrixEquiv).injective
    funext i k
    simp [Mat_.comp_apply, biproduct.components,
      biproduct.lift_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance finiteMatrixLift_additive (F : C ⥤ D) [F.Additive] :
    (finiteMatrixLift F).Additive where

set_option backward.isDefEq.respectTransparency false in
instance finiteMatrixLift_faithful (F : C ⥤ D) [F.Additive] [F.Faithful] :
    (finiteMatrixLift F).Faithful where
  map_injective {X Y} f g h := by
    ext i j
    apply F.map_injective
    have hcomponent := congrArg
      (fun q ↦ biproduct.ι (fun i ↦ F.obj (X.X i)) i ≫ q ≫
        biproduct.π (fun j ↦ F.obj (Y.X j)) j) h
    simpa [finiteMatrixLift] using hcomponent

set_option backward.isDefEq.respectTransparency false in
instance finiteMatrixLift_full (F : C ⥤ D) [F.Additive] [F.Full] :
    (finiteMatrixLift F).Full where
  map_surjective {X Y} f := by
    let m : X ⟶ Y := fun i j ↦ F.preimage
      (biproduct.ι (fun i ↦ F.obj (X.X i)) i ≫ f ≫
        biproduct.π (fun j ↦ F.obj (Y.X j)) j)
    refine ⟨m, ?_⟩
    apply (biproduct.matrixEquiv).injective
    funext i j
    change biproduct.components
      (biproduct.matrix fun i j ↦ F.map (m i j)) i j =
        biproduct.components f i j
    rw [biproduct.matrix_components]
    dsimp only [m]
    rw [F.map_preimage]
    rfl

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable [HasFiniteBiproducts E]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteMatrixPushforward_naturality
    (F : Functor C D) [F.Additive] (P : Functor D E) [P.Additive]
    (H : Functor C E) [H.Additive] (e : F ⋙ P ≅ H)
    {M N : Mat_ C} (m : ∀ i j, M.X i ⟶ N.X j) :
    P.map (biproduct.matrix fun i j ↦ F.map (m i j)) ≫
        (P.mapBiproduct (fun i ↦ F.obj (N.X i)) ≪≫
          biproduct.mapIso (fun i ↦ e.app (N.X i))).hom =
      (P.mapBiproduct (fun i ↦ F.obj (M.X i)) ≪≫
          biproduct.mapIso (fun i ↦ e.app (M.X i))).hom ≫
        biproduct.matrix (fun i j ↦ H.map (m i j)) := by
  rw [← cancel_epi
    ((P.mapBiproduct (fun i ↦ F.obj (M.X i)) ≪≫
      biproduct.mapIso (fun i ↦ e.app (M.X i))).inv)]
  simp only [Iso.inv_hom_id_assoc]
  apply (biproduct.matrixEquiv).injective
  funext i j
  change biproduct.components _ i j = biproduct.components _ i j
  simp [biproduct.components, Iso.trans_hom]
  rw [← P.map_comp_assoc, ← P.map_comp_assoc]
  have hm :
      (biproduct.ι (fun i ↦ F.obj (M.X i)) i ≫
          biproduct.matrix (fun i j ↦ F.map (m i j))) ≫
        biproduct.π (fun i ↦ F.obj (N.X i)) j =
          F.map (m i j) := by
    simp
  with_reducible_and_instances rw [hm]
  change
    e.inv.app (M.X i) ≫ (F ⋙ P).map (m i j) ≫
      e.hom.app (N.X j) = H.map (m i j)
  rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural isomorphism after an additive functor extends componentwise to
finite matrices, with the additive functor's canonical biproduct comparison
on the source. -/
noncomputable def finiteMatrixPushforwardIso
    (F : C ⥤ D) [F.Additive] (P : D ⥤ E) [P.Additive]
    (H : C ⥤ E) [H.Additive] (e : F ⋙ P ≅ H) :
    finiteMatrixLift F ⋙ P ≅ finiteMatrixLift H := by
  refine NatIso.ofComponents (fun M ↦
    P.mapBiproduct (fun i ↦ F.obj (M.X i)) ≪≫
      biproduct.mapIso (fun i ↦ e.app (M.X i))) ?_
  intro M N m
  change (∀ i j, M.X i ⟶ N.X j) at m
  exact finiteMatrixPushforward_naturality F P H e m

end FiniteMatrixLift

/-- Finite sums of finite-dimensional projective representables, with maps
encoded as matrices between the representing objects. -/
noncomputable def finiteProjectiveRepresentableSumFunctor
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    Functor (Mat_ (Cᵒᵖ))
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :=
  finiteMatrixLift (finiteDimensionalLinearCoyonedaFunctor (k := k) hP)

instance finiteProjectiveRepresentableSumFunctor_faithful
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    (finiteProjectiveRepresentableSumFunctor (k := k) hP).Faithful := by
  dsimp [finiteProjectiveRepresentableSumFunctor]
  infer_instance

/-- Finite sums of finite dual corepresentables, the Nakayama images of the
corresponding finite sums of projective representables. -/
noncomputable def finiteNakayamaRepresentableSumFunctor
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    Functor (Mat_ (Cᵒᵖ))
      (FiniteDimensionalModuleCategory (C := C) k) :=
  finiteMatrixLift (finiteDimensionalDualLinearYonedaFunctor (k := k) hI)

namespace CoherentDeckShift

variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- The finite projective representables on chosen strict orbits, indexed by
their upstairs representing objects. -/
noncomputable def orbitSkeletonFiniteDimensionalLinearCoyonedaFunctor
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Cᵒᵖ ⥤ FiniteDimensionalModuleCategory
      (C := DeckOrbitSkeleton C G) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := D.orbitSkeletonFunctor.op ⋙
    linearCoyonedaLinearModuleFunctor
      (k := k) (C := DeckOrbitSkeleton C G)
  exact ObjectProperty.lift
    (IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k) F
    (fun X ↦
      (D.orbitSkeletonFiniteDimensionalLinearCoyoneda
        (k := k) X.unop (hP X.unop)).property)

set_option backward.isDefEq.respectTransparency false in
instance orbitSkeletonFiniteDimensionalLinearCoyonedaFunctor_additive
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.orbitSkeletonFiniteDimensionalLinearCoyonedaFunctor
      (k := k) hP).Additive where
  map_add := by
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    intro X Y f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    change (linearCoyoneda k (DeckOrbitSkeleton C G)).map
          (D.orbitSkeletonMap ((f + g).unop)).op =
      (linearCoyoneda k (DeckOrbitSkeleton C G)).map
          (D.orbitSkeletonMap f.unop).op +
        (linearCoyoneda k (DeckOrbitSkeleton C G)).map
          (D.orbitSkeletonMap g.unop).op
    rw [CategoryTheory.unop_add, D.orbitSkeletonMap_add,
      CategoryTheory.op_add]
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    change (D.orbitSkeletonMap f.unop +
        D.orbitSkeletonMap g.unop) ≫ q =
      D.orbitSkeletonMap f.unop ≫ q +
        D.orbitSkeletonMap g.unop ≫ q
    rw [Preadditive.add_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The finite dual corepresentables on chosen strict orbits, indexed by their
upstairs representing objects. -/
noncomputable def orbitSkeletonFiniteDimensionalDualLinearYonedaFunctor
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Cᵒᵖ ⥤ FiniteDimensionalModuleCategory
      (C := DeckOrbitSkeleton C G) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := D.orbitSkeletonFunctor.op ⋙
    dualLinearYonedaLinearModuleFunctor
      (k := k) (C := DeckOrbitSkeleton C G)
  exact ObjectProperty.lift
    (IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k) F
    (fun X ↦
      (D.orbitSkeletonFiniteDimensionalDualLinearYoneda
        (k := k) X.unop (hI X.unop)).property)

set_option backward.isDefEq.respectTransparency false in
instance orbitSkeletonFiniteDimensionalDualLinearYonedaFunctor_additive
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.orbitSkeletonFiniteDimensionalDualLinearYonedaFunctor
      (k := k) hI).Additive where
  map_add := by
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    intro X Y f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    change dualLinearYonedaMap (k := k)
          (D.orbitSkeletonMap ((f + g).unop)) =
      dualLinearYonedaMap (k := k) (D.orbitSkeletonMap f.unop) +
        dualLinearYonedaMap (k := k) (D.orbitSkeletonMap g.unop)
    rw [CategoryTheory.unop_add, D.orbitSkeletonMap_add]
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual k
      (Z ⟶ (Quotient.mk'' X.unop :
        MulAction.orbitRel.Quotient G C)) at phi
    apply LinearMap.ext
    intro q
    change phi (q ≫
        (D.orbitSkeletonMap f.unop +
          D.orbitSkeletonMap g.unop)) =
      phi (q ≫ D.orbitSkeletonMap f.unop) +
        phi (q ≫ D.orbitSkeletonMap g.unop)
    rw [Preadditive.comp_add, map_add]

set_option backward.isDefEq.respectTransparency false in
/-- The finite projective-representable comparison, bundled as a natural
isomorphism in the upstairs representing object. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaNatIso
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    finiteDimensionalLinearCoyonedaFunctor (k := k) hP ⋙
        D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k) ≅
      D.orbitSkeletonFiniteDimensionalLinearCoyonedaFunctor
        (k := k) hP := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  refine NatIso.ofComponents (fun X ↦
    D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X.unop (hP X.unop)) ?_
  intro X Y f
  exact D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso_representing_naturality
    (k := k) f.unop (hP Y.unop) (hP X.unop)

set_option backward.isDefEq.respectTransparency false in
/-- The finite dual-corepresentable comparison, bundled as a natural
isomorphism in the upstairs representing object. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaNatIso
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    finiteDimensionalDualLinearYonedaFunctor (k := k) hI ⋙
        D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k) ≅
      D.orbitSkeletonFiniteDimensionalDualLinearYonedaFunctor
        (k := k) hI := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  refine NatIso.ofComponents (fun X ↦
    D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) X.unop (hI X.unop)) ?_
  intro X Y f
  exact D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso_representing_naturality
    (k := k) f.unop (hI Y.unop) (hI X.unop)

set_option backward.isDefEq.respectTransparency false in
/-- Finite sums of projective representables on the chosen strict orbit
skeleton, still indexed by their upstairs representing objects. -/
noncomputable def orbitSkeletonFiniteProjectiveRepresentableSumFunctor
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Functor (Mat_ (Cᵒᵖ)) (FiniteDimensionalModuleCategory
      (C := DeckOrbitSkeleton C G) k) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact finiteMatrixLift
    (D.orbitSkeletonFiniteDimensionalLinearCoyonedaFunctor
      (k := k) hP)

set_option backward.isDefEq.respectTransparency false in
/-- Finite sums of dual corepresentables on the chosen strict orbit skeleton,
still indexed by their upstairs representing objects. -/
noncomputable def orbitSkeletonFiniteNakayamaRepresentableSumFunctor
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Functor (Mat_ (Cᵒᵖ)) (FiniteDimensionalModuleCategory
      (C := DeckOrbitSkeleton C G) k) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact finiteMatrixLift
    (D.orbitSkeletonFiniteDimensionalDualLinearYonedaFunctor
      (k := k) hI)

set_option backward.isDefEq.respectTransparency false in
/-- Orbit push-down commutes with finite sums and matrices of projective
representables. -/
noncomputable def finiteProjectiveRepresentableSumOrbitSkeletonPushdownIso
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    finiteProjectiveRepresentableSumFunctor (k := k) hP ⋙
        D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k) ≅
      D.orbitSkeletonFiniteProjectiveRepresentableSumFunctor
        (k := k) hP := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact finiteMatrixPushforwardIso
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))
    (D.orbitSkeletonFiniteDimensionalLinearCoyonedaFunctor
      (k := k) hP)
    (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaNatIso
      (k := k) hP)

set_option backward.isDefEq.respectTransparency false in
/-- Orbit push-down commutes with the finite sums and matrices of dual
corepresentables that occur after applying Nakayama. -/
noncomputable def finiteNakayamaRepresentableSumOrbitSkeletonPushdownIso
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    finiteNakayamaRepresentableSumFunctor (k := k) hI ⋙
        D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k) ≅
      D.orbitSkeletonFiniteNakayamaRepresentableSumFunctor
        (k := k) hI := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact finiteMatrixPushforwardIso
    (finiteDimensionalDualLinearYonedaFunctor (k := k) hI)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))
    (D.orbitSkeletonFiniteDimensionalDualLinearYonedaFunctor
      (k := k) hI)
    (D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaNatIso
      (k := k) hI)

set_option backward.isDefEq.respectTransparency false in
/-- Exact orbit push-down transports the kernel of a matrix between finite
Nakayama sums to the kernel of the pushed matrix.  For a minimal projective
presentation, this is the categorical kernel that defines the
Auslander--Reiten translate. -/
noncomputable def finiteNakayamaKernelOrbitSkeletonPushdownIso
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    {P₁ P₀ : Mat_ (Cᵒᵖ)} (d : P₁ ⟶ P₀) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (kernel ((finiteNakayamaRepresentableSumFunctor
          (k := k) hI).map d)) ≅
      kernel ((D.orbitSkeletonFiniteNakayamaRepresentableSumFunctor
        (k := k) hI).map d) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let N := finiteNakayamaRepresentableSumFunctor (k := k) hI
  let N' := D.orbitSkeletonFiniteNakayamaRepresentableSumFunctor
    (k := k) hI
  let e := D.finiteNakayamaRepresentableSumOrbitSkeletonPushdownIso
    (k := k) hI
  exact PreservesKernel.iso P (N.map d) ≪≫
    kernel.mapIso (P.map (N.map d)) (N'.map d)
      (e.app P₁) (e.app P₀)
      (e.hom.naturality d)

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
