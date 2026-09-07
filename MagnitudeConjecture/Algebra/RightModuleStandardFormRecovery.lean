import MagnitudeConjecture.Algebra.RightModuleStandardFormRestriction
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleInjectiveEnvelope

/-!
# Recovery from the projective vertices of the standard mesh

Restriction from finite contravariant modules on the whole standard mesh to
the full subcategory on its projective vertices is an equivalence on
projective objects.  The proof compares the Auslander--Bongartz--Gabriel
equivalence with kernel realization and uses two injective presentations to
show that every target module is such a kernel.

Consequently the restricted Yoneda functor is full, and every indecomposable
finite module on the projective vertices is represented by a standard-mesh
vertex.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormRecoveryQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormRecoveryArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- Finite contravariant modules on the projective vertices of the standard
mesh. -/
abbrev StandardFormProjectiveVertexModuleCategory :=
  FiniteDimensionalModuleCategory.{0, u, u, u}
    (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k

/-- Restriction of projective-injective whole-mesh modules, with the target
injectivity witness forgotten. -/
def standardFormProjectiveInjectiveRestrictionUnderlyingFunctor :
    Functor
      (ProjectiveInjectiveObject
        S.StandardFormFiniteContravariantModuleCategory)
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
  ProjectiveInjectiveObject.ι _ ⋙
    S.standardFormModuleRestrictionFunctor (k := k)

instance :
    (S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
      (k := k)).Additive := by
  dsimp only [standardFormProjectiveInjectiveRestrictionUnderlyingFunctor]
  infer_instance

instance :
    (S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
      (k := k)).Full := by
  let K := S.standardFormProjectiveInjectiveRestrictionFunctor (k := k)
  let U := InjectiveObject.ι
    (S.StandardFormProjectiveVertexModuleCategory (k := k))
  let e : K ⋙ U ≅
      S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
        (k := k) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  exact Functor.Full.of_iso e

instance :
    (S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
      (k := k)).Faithful := by
  let K := S.standardFormProjectiveInjectiveRestrictionFunctor (k := k)
  let U := InjectiveObject.ι
    (S.StandardFormProjectiveVertexModuleCategory (k := k))
  let e : K ⋙ U ≅
      S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
        (k := k) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  exact Functor.Faithful.of_iso e

/-- Kernel realization after restricting projective-injective whole-mesh
modules to the projective vertices. -/
def standardFormRestrictedInjectiveKernelFunctor :
    Functor
      (Preadditive.LeftFreyd
        (ProjectiveInjectiveObject
          S.StandardFormFiniteContravariantModuleCategory))
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
  LeftFreyd.kernelFunctor
    S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor

instance : (S.standardFormRestrictedInjectiveKernelFunctor (k := k)).Full :=
  LeftFreyd.kernelFunctor_full_of_injective_objects
    S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
    (fun X ↦ by
      exact S.standardFormModuleRestriction_injective (k := k) X.obj)

instance :
    (S.standardFormRestrictedInjectiveKernelFunctor (k := k)).Faithful :=
  LeftFreyd.kernelFunctor_faithful_of_injective_objects
    S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
    (fun X ↦ by
      exact S.standardFormModuleRestriction_injective (k := k) X.obj)

/-- Every finite module on the projective vertices has a two-term kernel
presentation by restricted projective-injective whole-mesh modules. -/
theorem standardFormRestrictedInjectiveKernelPresentation_nonempty
    (M : S.StandardFormProjectiveVertexModuleCategory (k := k)) :
    Nonempty (LeftFreyd.KernelPresentationAlong
      (S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
        (k := k)) M) := by
  let K := S.standardFormProjectiveInjectiveRestrictionFunctor (k := k)
  let U := InjectiveObject.ι
    (S.StandardFormProjectiveVertexModuleCategory (k := k))
  let F :=
    S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor (k := k)
  let hEnough := finiteDimensionalModuleCategoryEnoughInjectives
    S.standardFormProjectiveMeshFiniteDualCorepresentables
  let I₀ : InjectivePresentation M := (hEnough.presentation M).some
  let I₁ : InjectivePresentation (cokernel I₀.f) :=
    (hEnough.presentation (cokernel I₀.f)).some
  let dI : I₀.J ⟶ I₁.J := cokernel.π I₀.f ≫ I₁.f
  have zeroI : I₀.f ≫ dI = 0 := by
    simp [dI]
  let SI : ShortComplex
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
    ShortComplex.mk I₀.f dI zeroI
  have exactI : SI.Exact := by
    change (ShortComplex.mk I₀.f dI zeroI).Exact
    apply (ShortComplex.exact_iff_mono_cokernel_desc _).2
    have hDesc : cokernel.desc I₀.f dI zeroI = I₁.f := by
      apply (cancel_epi (cokernel.π I₀.f)).1
      simp [dI]
    rw [hDesc]
    infer_instance
  let J₀ : InjectiveObject
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
    ⟨I₀.J, inferInstance⟩
  let J₁ : InjectiveObject
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
    ⟨I₁.J, inferInstance⟩
  obtain ⟨V₀, ⟨e₀⟩⟩ :=
    (inferInstance : K.EssSurj).mem_essImage J₀
  obtain ⟨V₁, ⟨e₁⟩⟩ :=
    (inferInstance : K.EssSurj).mem_essImage J₁
  let e₀' : F.obj V₀ ≅ I₀.J := U.mapIso e₀
  let e₁' : F.obj V₁ ≅ I₁.J := U.mapIso e₁
  let dC : F.obj V₀ ⟶ F.obj V₁ :=
    e₀'.hom ≫ dI ≫ e₁'.inv
  let d : V₀ ⟶ V₁ := F.preimage dC
  have hd : F.map d = dC := F.map_preimage dC
  let augmentation : M ⟶ F.obj V₀ := I₀.f ≫ e₀'.inv
  have zero : augmentation ≫ F.map d = 0 := by
    rw [hd]
    simp only [augmentation, dC, Category.assoc, e₀'.inv_hom_id_assoc]
    rw [← Category.assoc, zeroI, zero_comp]
  let T : ShortComplex
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
    ShortComplex.mk augmentation (F.map d) zero
  let eT : SI ≅ T :=
    ShortComplex.isoMk (Iso.refl M) e₀'.symm e₁'.symm
      (by rfl)
      (by
        dsimp only [T]
        rw [hd]
        simp [SI, dC])
  exact ⟨
    { left := V₀
      right := V₁
      augmentation := augmentation
      differential := d
      zero := zero
      augmentation_mono := by
        dsimp only [augmentation]
        infer_instance
      exact := ShortComplex.exact_of_iso eT exactI }⟩

instance :
    (S.standardFormRestrictedInjectiveKernelFunctor (k := k)).EssSurj :=
  LeftFreyd.kernelFunctor_essSurj_of_kernelPresentations
    S.standardFormProjectiveInjectiveRestrictionUnderlyingFunctor
    S.standardFormRestrictedInjectiveKernelPresentation_nonempty

instance :
    (S.standardFormRestrictedInjectiveKernelFunctor (k := k)).IsEquivalence
    where

/-- The equivalence obtained by realizing formal arrows as kernels after
restriction to the projective vertices. -/
def standardFormRestrictedInjectiveKernelEquivalence :
    Preadditive.LeftFreyd
        (ProjectiveInjectiveObject
          S.StandardFormFiniteContravariantModuleCategory) ≌
      S.StandardFormProjectiveVertexModuleCategory (k := k) :=
  (S.standardFormRestrictedInjectiveKernelFunctor (k := k)).asEquivalence

/-- Restriction from projective whole-mesh modules to finite modules on the
projective vertices. -/
def standardFormProjectiveModuleRestrictionFunctor :
    Functor
      (ProjectiveObject S.StandardFormFiniteContravariantModuleCategory)
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
  ProjectiveObject.ι _ ⋙
    S.standardFormModuleRestrictionFunctor (k := k)

/-- Forgetting the projectivity witness after the standard-form
Auslander--Bongartz--Gabriel equivalence recovers its kernel realization
functor. -/
def standardFormAuslanderUnderlyingNatIso :
    S.standardFormAuslanderBongartzGabrielEquivalence.functor ⋙
        ProjectiveObject.ι
          S.StandardFormFiniteContravariantModuleCategory ≅
      LeftFreyd.projectiveInjectiveKernelFunctor
        S.StandardFormFiniteContravariantModuleCategory := by
  change
    (LeftFreyd.projectiveInjectiveKernelFunctorToProjectives
      (fun M ↦
        S.standardFormFiniteModule_hasProjectiveDimensionLE_two M)) ⋙
        ProjectiveObject.ι
          S.StandardFormFiniteContravariantModuleCategory ≅
      LeftFreyd.projectiveInjectiveKernelFunctor
        S.StandardFormFiniteContravariantModuleCategory
  exact (isProjective
    S.StandardFormFiniteContravariantModuleCategory).liftCompιIso
      (LeftFreyd.projectiveInjectiveKernelFunctor
        S.StandardFormFiniteContravariantModuleCategory)
      (fun X ↦ by
        change Projective (kernel X.as.hom.hom)
        exact LeftFreyd.kernel_projective_of_projectiveDimensionLE_two
          X.as.hom.hom
          (fun M ↦
            S.standardFormFiniteModule_hasProjectiveDimensionLE_two M))

/-- The composite of the Auslander--Bongartz--Gabriel equivalence with
projective restriction agrees with restricted kernel realization. -/
def standardFormAuslanderRestrictionKernelNatIso :
    S.standardFormAuslanderBongartzGabrielEquivalence.functor ⋙
        S.standardFormProjectiveModuleRestrictionFunctor (k := k) ≅
      S.standardFormRestrictedInjectiveKernelFunctor (k := k) := by
  let E := S.standardFormAuslanderBongartzGabrielEquivalence
  let P := ProjectiveObject.ι
    S.StandardFormFiniteContravariantModuleCategory
  let K := S.standardFormModuleRestrictionFunctor (k := k)
  change E.functor ⋙ (P ⋙ K) ≅
    LeftFreyd.kernelFunctor
      (ProjectiveInjectiveObject.ι
        S.StandardFormFiniteContravariantModuleCategory ⋙ K)
  exact (Functor.associator E.functor P K).symm |>.trans
    ((Functor.isoWhiskerRight
        (S.standardFormAuslanderUnderlyingNatIso (k := k)) K).trans
      (LeftFreyd.kernelFunctorCompIso
        (ProjectiveInjectiveObject.ι
          S.StandardFormFiniteContravariantModuleCategory) K))

instance :
    (S.standardFormProjectiveModuleRestrictionFunctor
      (k := k)).IsEquivalence := by
  let E := S.standardFormAuslanderBongartzGabrielEquivalence
  let R := S.standardFormProjectiveModuleRestrictionFunctor (k := k)
  let H := S.standardFormRestrictedInjectiveKernelFunctor (k := k)
  let e : E.functor ⋙ R ≅ H :=
    S.standardFormAuslanderRestrictionKernelNatIso (k := k)
  letI : (E.functor ⋙ R).IsEquivalence :=
    Functor.isEquivalence_of_iso e.symm
  exact Functor.isEquivalence_of_comp_left E.functor R

/-- Projective restriction as an explicit equivalence. -/
def standardFormProjectiveModuleRestrictionEquivalence :
    ProjectiveObject S.StandardFormFiniteContravariantModuleCategory ≌
      S.StandardFormProjectiveVertexModuleCategory (k := k) :=
  (S.standardFormProjectiveModuleRestrictionFunctor
    (k := k)).asEquivalence

/-- The strict standard-mesh category and its induced vertex category have
the same objects and morphisms. -/
def standardFormMeshVertexFunctor :
    Functor S.StandardFormMeshCategory
      (S.standardFormRightMeshData.VertexCategory (k := k)) where
  obj X := X.as
  map f := InducedCategory.homMk f
  map_id X := by
    apply InducedCategory.hom_ext
    rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    rfl

instance : (S.standardFormMeshVertexFunctor (k := k)).Full where
  map_surjective f :=
    ⟨f.hom, by
      apply InducedCategory.hom_ext
      rfl⟩

instance : (S.standardFormMeshVertexFunctor (k := k)).Faithful where
  map_injective {X Y} f g h := by
    have h' := congrArg InducedCategory.Hom.hom h
    change f = g at h'
    exact h'

instance : (S.standardFormMeshVertexFunctor (k := k)).EssSurj where
  mem_essImage X :=
    ⟨MeshCategory.obj (k := k) S.standardFormRightMeshData X,
      ⟨Iso.refl X⟩⟩

instance : (S.standardFormMeshVertexFunctor (k := k)).IsEquivalence where

/-- The concrete inverse from the induced vertex category back to the strict
raw standard-mesh category. -/
def standardFormMeshRawFunctor :
    Functor (S.standardFormRightMeshData.VertexCategory (k := k))
      S.StandardFormMeshCategory where
  obj X := MeshCategory.obj (k := k) S.standardFormRightMeshData X
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (S.standardFormMeshRawFunctor (k := k)).Additive where
  map_add := by intros; rfl

instance : (S.standardFormMeshRawFunctor (k := k)).Full where
  map_surjective f := ⟨InducedCategory.homMk f, rfl⟩

instance : (S.standardFormMeshRawFunctor (k := k)).Faithful where
  map_injective {X Y} f g h := by
    apply InducedCategory.hom_ext
    exact h

instance : (S.standardFormMeshRawFunctor (k := k)).EssSurj where
  mem_essImage X := ⟨X.as, ⟨Iso.refl X⟩⟩

instance : (S.standardFormMeshRawFunctor (k := k)).IsEquivalence where

/-- Restricted Yoneda written on the literal vertex model of the standard
mesh. -/
def standardFormVertexRestrictedYonedaFunctor :
    Functor (S.standardFormRightMeshData.VertexCategory (k := k))
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
  S.standardFormMeshRawFunctor (k := k) ⋙
    S.standardFormRestrictedYonedaFunctor S.standardFormMeshHomFinite

instance standardFormRestrictedYonedaFunctor_additive :
    (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).Additive := by
  dsimp only [standardFormRestrictedYonedaFunctor]
  infer_instance

instance : (S.standardFormVertexRestrictedYonedaFunctor (k := k)).Additive := by
  dsimp only [standardFormVertexRestrictedYonedaFunctor]
  infer_instance

instance : (S.standardFormVertexRestrictedYonedaFunctor (k := k)).Faithful := by
  dsimp only [standardFormVertexRestrictedYonedaFunctor]
  letI : (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).Faithful :=
    S.standardFormRestrictedYonedaFunctor_faithful
  infer_instance

/-- A standard-mesh vertex, sent to its finite contravariant representable
and bundled as a projective whole-mesh module. -/
def standardFormRepresentableProjectiveFunctor :
    Functor S.StandardFormMeshCategory
      (ProjectiveObject S.StandardFormFiniteContravariantModuleCategory) :=
  (isProjective S.StandardFormFiniteContravariantModuleCategory).lift
    (S.standardFormMeshVertexFunctor (k := k) ⋙
      opOp (S.standardFormRightMeshData.VertexCategory (k := k)) ⋙
        finiteDimensionalLinearCoyonedaFunctor
          (k := k) S.standardFormFiniteContravariantRepresentables)
    (fun X ↦ finiteDimensionalLinearCoyoneda_projective
      (Opposite.op (S.standardFormMeshVertexFunctor.obj X))
      (S.standardFormFiniteContravariantRepresentables
        (Opposite.op (S.standardFormMeshVertexFunctor.obj X))))

instance : (S.standardFormRepresentableProjectiveFunctor (k := k)).Full := by
  dsimp only [standardFormRepresentableProjectiveFunctor]
  infer_instance

instance :
    (S.standardFormRepresentableProjectiveFunctor (k := k)).Faithful := by
  dsimp only [standardFormRepresentableProjectiveFunctor]
  infer_instance

/-- Restricting the projective representable attached to a mesh vertex is
the restricted Yoneda module of that vertex. -/
def standardFormRepresentableRestrictionNatIso :
    S.standardFormRepresentableProjectiveFunctor ⋙
        S.standardFormProjectiveModuleRestrictionFunctor (k := k) ≅
      S.standardFormRestrictedYonedaFunctor
        S.standardFormMeshHomFinite :=
  NatIso.ofComponents
    (fun X ↦
      (S.standardFormModuleRestrictionFunctor (k := k)).mapIso
          (S.standardFormRightMeshData.contravariantRepresentableFiniteIso
            (k := k) S.standardFormFiniteContravariantRepresentables X.as)
        |>.trans
          (S.standardFormRestrictedRepresentableIso (k := k) X.as))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext P
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro q
      rfl)

instance standardFormRestrictedYonedaFunctor_full :
    (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).Full := by
  let H := S.standardFormRepresentableProjectiveFunctor (k := k)
  let R := S.standardFormProjectiveModuleRestrictionFunctor (k := k)
  let Y := S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite
  let e : H ⋙ R ≅ Y :=
    S.standardFormRepresentableRestrictionNatIso (k := k)
  exact Functor.Full.of_iso e

instance : (S.standardFormVertexRestrictedYonedaFunctor (k := k)).Full := by
  dsimp only [standardFormVertexRestrictedYonedaFunctor]
  infer_instance

/-- If the restriction of a projective whole-mesh module is indecomposable,
then its underlying whole-mesh module is indecomposable. -/
theorem standardFormProjectiveRestriction_indecomposable_underlying
    (P : ProjectiveObject
      S.StandardFormFiniteContravariantModuleCategory)
    (hP : Indecomposable
      ((S.standardFormProjectiveModuleRestrictionFunctor (k := k)).obj P)) :
    Indecomposable P.obj := by
  let U := ProjectiveObject.ι
    S.StandardFormFiniteContravariantModuleCategory
  let K := S.standardFormModuleRestrictionFunctor (k := k)
  let R := S.standardFormProjectiveModuleRestrictionFunctor (k := k)
  refine ⟨?_, ?_⟩
  · intro hzero
    exact hP.1 (K.map_isZero hzero)
  · intro Y Z e
    letI : PreservesBinaryBiproduct Y Z K :=
      preservesBinaryBiproduct_of_preservesBinaryProduct K
    let eR' : K.obj P.obj ≅ K.obj Y ⊞ K.obj Z :=
      (K.mapIso e).trans (K.mapBiprod Y Z)
    let eR : R.obj P ≅ K.obj Y ⊞ K.obj Z := eR'
    rcases hP.2 (K.obj Y) (K.obj Z) eR with hY | hZ
    · let rY : Retract Y P.obj :=
        (BinaryBiproduct.bicone Y Z).retract_left |>.trans
          (Retract.ofIso e.symm)
      let YP : ProjectiveObject
          S.StandardFormFiniteContravariantModuleCategory :=
        ⟨Y, rY.projective⟩
      have hRYP : IsZero (R.obj YP) := hY
      exact Or.inl (U.map_isZero
        (IsZero.of_full_of_faithful_of_isZero R YP hRYP))
    · let rZ : Retract Z P.obj :=
        (BinaryBiproduct.bicone Y Z).retract_right |>.trans
          (Retract.ofIso e.symm)
      let ZP : ProjectiveObject
          S.StandardFormFiniteContravariantModuleCategory :=
        ⟨Z, rZ.projective⟩
      have hRZP : IsZero (R.obj ZP) := hZ
      exact Or.inr (U.map_isZero
        (IsZero.of_full_of_faithful_of_isZero R ZP hRZP))

/-- Every indecomposable finite module on the projective vertices is the
restricted Yoneda module of a standard-mesh vertex. -/
theorem standardFormRestrictedYonedaFunctor_indec_dense
    (M : S.StandardFormProjectiveVertexModuleCategory (k := k))
    (hM : Indecomposable M) :
    ∃ X : S.StandardFormMeshCategory, Nonempty
      ((S.standardFormRestrictedYonedaFunctor
        S.standardFormMeshHomFinite).obj X ≅ M) := by
  let R := S.standardFormProjectiveModuleRestrictionFunctor (k := k)
  obtain ⟨P, ⟨eP⟩⟩ := (inferInstance : R.EssSurj).mem_essImage M
  have hRP : Indecomposable (R.obj P) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eP).mpr hM
  have hPobj : Indecomposable P.obj :=
    S.standardFormProjectiveRestriction_indecomposable_underlying
      (k := k) P hRP
  obtain ⟨X, ⟨eX⟩⟩ :=
    indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
      S.standardFormFiniteContravariantRepresentables
      S.standardFormOppositeVertexCategoryEndLocal P.obj hPobj
  let V : S.standardFormRightMeshData.VertexCategory (k := k) := X.unop
  let Q : S.StandardFormMeshCategory :=
    MeshCategory.obj (k := k) S.standardFormRightMeshData V
  let H := S.standardFormRepresentableProjectiveFunctor (k := k)
  let eQ : H.obj Q ≅ P := ObjectProperty.isoMk _ eX
  exact ⟨Q, ⟨
    (S.standardFormRepresentableRestrictionNatIso
      (k := k)).app Q |>.symm |>.trans
        ((R.mapIso eQ).trans eP)⟩⟩

/-- The finite additive hull of the strict standard-mesh category. -/
abbrev StandardFormAdditiveMeshCategory :=
  S.StandardFormMeshAdditiveHull (k := k)

/-- The additive extension of restricted Yoneda from mesh vertices to finite
formal sums of mesh vertices. -/
def standardFormAdditiveRestrictedYonedaFunctor :
    Functor (S.StandardFormAdditiveMeshCategory (k := k))
      (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
  finiteMatrixLift (S.standardFormVertexRestrictedYonedaFunctor (k := k))

instance :
    (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).Additive := by
  dsimp only [standardFormAdditiveRestrictedYonedaFunctor]
  infer_instance

instance :
    (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).Full := by
  dsimp only [standardFormAdditiveRestrictedYonedaFunctor]
  infer_instance

instance :
    (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).Faithful := by
  dsimp only [standardFormAdditiveRestrictedYonedaFunctor]
  letI : (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).Faithful :=
    S.standardFormRestrictedYonedaFunctor_faithful
  infer_instance

/-- On a singleton matrix object, additive restricted Yoneda is the original
restricted Yoneda module. -/
def standardFormAdditiveRestrictedYonedaSingletonIso
    (x : Fin S.n) :
    (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
        (S.standardFormRightMeshData.additiveVertexObj (k := k) x) ≅
      (S.standardFormRestrictedYonedaFunctor
        S.standardFormMeshHomFinite).obj
          (MeshCategory.obj (k := k) S.standardFormRightMeshData x) :=
  by
    dsimp only [standardFormAdditiveRestrictedYonedaFunctor,
      standardFormVertexRestrictedYonedaFunctor,
      standardFormMeshRawFunctor, finiteMatrixLift,
      MeshCategory.RightMeshData.additiveVertexObj, Mat_.embedding]
    exact biproductUniqueIso (fun _ : PUnit ↦
      (S.standardFormRestrictedYonedaFunctor
        S.standardFormMeshHomFinite).obj
          (MeshCategory.obj (k := k) S.standardFormRightMeshData x))

instance standardFormAdditiveRestrictedYonedaFunctor_essSurj :
    (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).EssSurj where
  mem_essImage M := by
    obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition M
    choose X e using fun j ↦
      S.standardFormRestrictedYonedaFunctor_indec_dense
        (k := k) (d.summand j) (d.indecomposable j)
    let Q : S.StandardFormAdditiveMeshCategory :=
      ⟨Fin d.n, fun j ↦ (X j).as⟩
    refine ⟨Q, ⟨?_⟩⟩
    dsimp only [standardFormAdditiveRestrictedYonedaFunctor,
      standardFormVertexRestrictedYonedaFunctor,
      standardFormMeshRawFunctor, finiteMatrixLift, Q]
    exact (biproduct.mapIso fun j ↦ Classical.choice (e j)).trans
      d.isoBiproduct.symm

instance standardFormAdditiveRestrictedYonedaFunctor_isEquivalence :
    (S.standardFormAdditiveRestrictedYonedaFunctor
      (k := k)).IsEquivalence where

/-- The finite additive hull of the standard mesh is equivalent to finite
modules on its projective vertices. -/
def standardFormAdditiveRestrictedYonedaEquivalence :
    S.StandardFormAdditiveMeshCategory (k := k) ≌
      S.StandardFormProjectiveVertexModuleCategory (k := k) :=
  (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).asEquivalence

/-- Algebra-facing form of standard-mesh recovery: its finite additive hull
is equivalent to finitely generated right modules over the standard-form
category algebra. -/
def standardFormAdditiveMeshModuleEquivalence :
    S.StandardFormAdditiveMeshCategory (k := k) ≌
      RightModule.FinitelyGeneratedCategory
        (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  (S.standardFormAdditiveRestrictedYonedaEquivalence (k := k)).trans
    (finiteCategoryProjectiveGenerator.moduleEquivalence
      (S.standardFormFiniteRightRepresentables
        S.standardFormMeshHomFinite))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
