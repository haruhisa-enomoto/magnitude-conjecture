import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.FreydCategory.Homotopy
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The left Freyd category and its kernel realization

This file supplies the left-handed part of the Freyd-category API that is not
yet present in Mathlib.  It also constructs the kernel realization used in the
Auslander--Bongartz--Gabriel argument: arrows between projective-injective
objects, modulo left homotopy, map to their kernels.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u''

namespace CategoryTheory.Preadditive

variable (V : Type u) [Category.{v} V] [Preadditive V]

/-- The category of arrows in `V`, modulo left homotopy. -/
def LeftFreyd :=
  CategoryTheory.Quotient (Arrow.leftHomotopic V)

instance : Category.{v} (LeftFreyd V) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (Arrow.leftHomotopic V)))

instance : Preadditive (LeftFreyd V) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨Arrow.LeftHomotopy.add h h'⟩)

namespace LeftFreyd

/-- The quotient functor from the arrow category to the left Freyd category. -/
def quotient : Arrow V ⥤ LeftFreyd V :=
  CategoryTheory.Quotient.functor _

instance : (quotient V).Full := Quotient.full_functor _

instance : (quotient V).EssSurj := Quotient.essSurj_functor _

instance : (quotient V).Additive where

variable {V}

/-- Left-homotopic squares become equal in the left Freyd category. -/
theorem eq_of_leftHomotopy {a b : Arrow V} (f g : a ⟶ b)
    (h : Arrow.LeftHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- Equality in the left Freyd category is represented by a left homotopy. -/
def homotopyOfEq {a b : Arrow V} (f g : a ⟶ b)
    (h : (quotient V).map f = (quotient V).map g) :
    Arrow.LeftHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp h).some

variable {a b : Arrow V} (f g : a ⟶ b)

/-- Two squares have equal images precisely when they are left homotopic. -/
lemma quotient_map_eq_iff :
    (quotient V).map f = (quotient V).map g ↔
      Nonempty (Arrow.LeftHomotopy f g) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_leftHomotopy _ _ h⟩

end LeftFreyd

end CategoryTheory.Preadditive

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The full subcategory of projective objects. -/
abbrev ProjectiveObject : Type u :=
  ObjectProperty.FullSubcategory (isProjective C)

namespace ProjectiveObject

/-- The inclusion of projective objects. -/
abbrev ι : ProjectiveObject C ⥤ C := ObjectProperty.ι _

instance (X : ProjectiveObject C) : Projective X.obj := X.2

end ProjectiveObject

/-- The full subcategory of injective objects. -/
abbrev InjectiveObject : Type u :=
  ObjectProperty.FullSubcategory (isInjective C)

namespace InjectiveObject

/-- The inclusion of injective objects. -/
abbrev ι : InjectiveObject C ⥤ C := ObjectProperty.ι _

instance (X : InjectiveObject C) : Injective X.obj := X.2

end InjectiveObject

/-- The full subcategory of objects that are both projective and injective. -/
abbrev ProjectiveInjectiveObject : Type u :=
  ObjectProperty.FullSubcategory (fun X : C ↦ Projective X ∧ Injective X)

namespace ProjectiveInjectiveObject

/-- The inclusion of projective-injective objects. -/
abbrev ι : ProjectiveInjectiveObject C ⥤ C := ObjectProperty.ι _

instance (X : ProjectiveInjectiveObject C) : Projective X.obj := X.2.1

instance (X : ProjectiveInjectiveObject C) : Injective X.obj := X.2.2

/-- Finite biproducts of projective-injective objects, constructed in the
ambient preadditive category, remain projective-injective. -/
noncomputable instance [Preadditive C] [HasFiniteBiproducts C] :
    HasFiniteBiproducts (ProjectiveInjectiveObject C) where
  out n :=
    { has_biproduct := fun X ↦ by
        classical
        letI : ∀ j : Fin n, Projective (X j).obj := fun j ↦ (X j).2.1
        letI : ∀ j : Fin n, Injective (X j).obj := fun j ↦ (X j).2.2
        have hprojective :
            Projective (⨁ fun j : Fin n ↦ (X j).obj) := by
          constructor
          intro E Y f e he
          refine ⟨biproduct.desc fun j ↦
            Projective.factorThru
              (biproduct.ι (fun i : Fin n ↦ (X i).obj) j ≫ f) e, ?_⟩
          apply biproduct.hom_ext'
          intro j
          simp
        have hinjective :
            Injective (⨁ fun j : Fin n ↦ (X j).obj) := by infer_instance
        let B : ProjectiveInjectiveObject C :=
          ⟨biproduct (fun j : Fin n ↦ (X j).obj),
            ⟨hprojective, hinjective⟩⟩
        let b : Bicone X :=
          { pt := B
            π := fun j ↦ ObjectProperty.homMk
              (biproduct.π (fun i : Fin n ↦ (X i).obj) j)
            ι := fun j ↦ ObjectProperty.homMk
              (biproduct.ι (fun i : Fin n ↦ (X i).obj) j)
            ι_π := by
              intro j i
              apply ObjectProperty.hom_ext
              by_cases h : j = i
              · subst i
                simp
              · simp [h] }
        apply HasBiproduct.mk
        exact
          { bicone := b
            isBilimit := isBilimitOfTotal b (by
              apply (ι C).map_injective
              rw [(ι C).map_sum, (ι C).map_id]
              exact biproduct.total) } }

end ProjectiveInjectiveObject

namespace Preadditive.LeftFreyd

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {C : Type u'} [Category.{v'} C] [Preadditive C] [HasKernels C]

/-- Before quotienting by left homotopy, send an arrow in `V` to the kernel of
its image under an additive functor `F : V ⥤ C`. -/
def rawKernel (F : V ⥤ C) : Arrow V ⥤ C where
  obj a := kernel (F.map a.hom)
  map {a b} f := kernel.lift (F.map b.hom) (kernel.ι (F.map a.hom) ≫ F.map f.left) (by
    rw [Category.assoc, ← F.map_comp, f.w, F.map_comp]
    simp)
  map_id a := by
    apply (cancel_mono (kernel.ι (F.map a.hom))).1
    simp only [kernel.lift_ι, Arrow.id_left, Functor.map_id, Category.comp_id,
      Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (kernel.ι (F.map _))).1
    simp

/-- The kernel realization of a left Freyd category along an additive functor. -/
def kernelFunctor (F : V ⥤ C) [F.Additive] :
    Preadditive.LeftFreyd V ⥤ C :=
  Quotient.lift (Arrow.leftHomotopic V) (rawKernel F) (by
    rintro a b f g ⟨h⟩
    apply (cancel_mono (kernel.ι (F.map b.hom))).1
    simp only [rawKernel, kernel.lift_ι]
    rw [← sub_eq_zero]
    rw [← Preadditive.comp_sub]
    rw [← F.map_sub, h.comm, F.map_comp]
    simp)

/-- Applying a kernel-preserving additive functor after kernel realization is
naturally isomorphic to taking kernels after applying the composite functor. -/
def kernelFunctorCompIso
    {D : Type u''} [Category.{v''} D] [Preadditive D] [HasKernels D]
    (F : Functor V C) [F.Additive]
    (G : Functor C D) [G.Additive]
    [∀ {X Y : C} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) G] :
    kernelFunctor F ⋙ G ≅ kernelFunctor (F ⋙ G) :=
  NatIso.ofComponents
    (fun X ↦ PreservesKernel.iso G (F.map X.as.hom))
    (by
      intro X Y f
      rcases X with ⟨a⟩
      rcases Y with ⟨b⟩
      obtain ⟨s, rfl⟩ := (LeftFreyd.quotient _).map_surjective f
      change G.map ((rawKernel F).map s) ≫
          (PreservesKernel.iso G (F.map b.hom)).hom =
        (PreservesKernel.iso G (F.map a.hom)).hom ≫
          (rawKernel (F ⋙ G)).map s
      rw [PreservesKernel.iso_hom, PreservesKernel.iso_hom]
      exact (kernelComparison_comp_kernel_map (f := F.map a.hom) G
        (F.map b.hom) (F.map s.left) (F.map s.right)
        (by simpa only [F.map_comp] using
          (congrArg F.map s.w).symm)).symm)

/-- A two-term presentation of `X` as the kernel of the image under `F` of
an arrow in the source category. -/
structure KernelPresentationAlong
    {C : Type u'} [Category.{v'} C] [Abelian C]
    (F : Functor V C) (X : C) where
  left : V
  right : V
  augmentation : X ⟶ F.obj left
  differential : left ⟶ right
  zero : augmentation ≫ F.map differential = 0
  [augmentation_mono : Mono augmentation]
  exact : (ShortComplex.mk augmentation (F.map differential) zero).Exact

attribute [instance] KernelPresentationAlong.augmentation_mono

namespace KernelPresentationAlong

variable {C : Type u'} [Category.{v'} C] [Abelian C]
variable {F : Functor V C} {X : C}

/-- The source arrow of a kernel presentation. -/
def arrow (I : KernelPresentationAlong F X) : Arrow V :=
  Arrow.mk I.differential

/-- The chosen exact monomorphism identifies the formal kernel with the
presented object. -/
def kernelIso (I : KernelPresentationAlong F X) :
    kernel (F.map I.differential) ≅ X :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel (F.map I.differential))
    I.exact.fIsKernel

end KernelPresentationAlong

/-- Kernel presentations of every target object make the kernel realization
essentially surjective. -/
theorem kernelFunctor_essSurj_of_kernelPresentations
    {C : Type u'} [Category.{v'} C] [Abelian C]
    (F : Functor V C) [F.Additive]
    (h : ∀ X : C, Nonempty (KernelPresentationAlong F X)) :
    (kernelFunctor F).EssSurj where
  mem_essImage X := by
    let I := (h X).some
    exact ⟨(LeftFreyd.quotient _).obj I.arrow, ⟨I.kernelIso⟩⟩

section FullyFaithfulInjectives

variable {C : Type u'} [Category.{v'} C] [Abelian C]

private theorem rawKernel_map_surjective_of_injective_objects
    (F : Functor V C) [F.Additive] [F.Full] [F.Faithful]
    (hI : ∀ X : V, Injective (F.obj X))
    (a b : Arrow V)
    (f : kernel (F.map a.hom) ⟶ kernel (F.map b.hom)) :
    ∃ s : a ⟶ b, (rawKernel F).map s = f := by
  letI : Injective (F.obj b.left) := hI b.left
  letI : Injective (F.obj b.right) := hI b.right
  let f₀ : F.obj a.left ⟶ F.obj b.left :=
    Injective.factorThru (f ≫ kernel.ι (F.map b.hom))
      (kernel.ι (F.map a.hom))
  have hf₀ : kernel.ι (F.map a.hom) ≫ f₀ =
      f ≫ kernel.ι (F.map b.hom) := by
    simp [f₀]
  have hzero : kernel.ι (F.map a.hom) ≫
      (f₀ ≫ F.map b.hom) = 0 := by
    rw [← Category.assoc, hf₀, Category.assoc, kernel.condition, comp_zero]
  let q : Abelian.coimage (F.map a.hom) ⟶ F.obj b.right :=
    cokernel.desc (kernel.ι (F.map a.hom))
      (f₀ ≫ F.map b.hom) hzero
  let f₁ : F.obj a.right ⟶ F.obj b.right :=
    Injective.factorThru q (Abelian.factorThruCoimage (F.map a.hom))
  have hsquare : f₀ ≫ F.map b.hom = F.map a.hom ≫ f₁ := by
    rw [← Abelian.coimage.fac (F.map a.hom), Category.assoc]
    simp [f₁, q]
  obtain ⟨g₀, hg₀⟩ := F.map_surjective f₀
  obtain ⟨g₁, hg₁⟩ := F.map_surjective f₁
  have hsquareV : g₀ ≫ b.hom = a.hom ≫ g₁ := by
    apply F.map_injective
    simpa only [F.map_comp, hg₀, hg₁] using hsquare
  let s : a ⟶ b := Arrow.homMk g₀ g₁ hsquareV
  refine ⟨s, ?_⟩
  apply (cancel_mono (kernel.ι (F.map b.hom))).1
  simpa [s, rawKernel, hg₀] using hf₀

private def leftHomotopy_of_rawKernel_map_eq_of_injective_objects
    (F : Functor V C) [F.Additive] [F.Full] [F.Faithful]
    (hI : ∀ X : V, Injective (F.obj X))
    {a b : Arrow V} (s t : a ⟶ b)
    (hst : (rawKernel F).map s = (rawKernel F).map t) :
    Arrow.LeftHomotopy s t := by
  letI : Injective (F.obj b.left) := hI b.left
  have hkernel : kernel.ι (F.map a.hom) ≫
      (F.map s.left - F.map t.left) = 0 := by
    rw [Preadditive.comp_sub, sub_eq_zero]
    have h := congrArg (fun k ↦ k ≫ kernel.ι (F.map b.hom)) hst
    change
      kernel.lift (F.map b.hom)
          (kernel.ι (F.map a.hom) ≫ F.map s.left) _ ≫
            kernel.ι (F.map b.hom) =
        kernel.lift (F.map b.hom)
          (kernel.ι (F.map a.hom) ≫ F.map t.left) _ ≫
            kernel.ι (F.map b.hom) at h
    simpa only [kernel.lift_ι] using h
  let q : Abelian.coimage (F.map a.hom) ⟶ F.obj b.left :=
    cokernel.desc (kernel.ι (F.map a.hom))
      (F.map s.left - F.map t.left) hkernel
  let h : F.obj a.right ⟶ F.obj b.left :=
    Injective.factorThru q (Abelian.factorThruCoimage (F.map a.hom))
  have hfactor : F.map s.left - F.map t.left = F.map a.hom ≫ h := by
    rw [← Abelian.coimage.fac (F.map a.hom), Category.assoc]
    simp [h, q]
  let hV : a.right ⟶ b.left := F.preimage h
  have hhV : F.map hV = h := F.map_preimage h
  exact
    { hom := hV
      comm := by
        apply F.map_injective
        simpa only [F.map_sub, F.map_comp, hhV] using hfactor }

/-- Kernel realization along a fully faithful functor with injective values is
full. -/
theorem kernelFunctor_full_of_injective_objects
    (F : Functor V C) [F.Additive] [F.Full] [F.Faithful]
    (hI : ∀ X : V, Injective (F.obj X)) :
    (kernelFunctor F).Full where
  map_surjective {X Y} f := by
    rcases X with ⟨a⟩
    rcases Y with ⟨b⟩
    obtain ⟨s, hs⟩ :=
      rawKernel_map_surjective_of_injective_objects F hI a b f
    exact ⟨(LeftFreyd.quotient _).map s, hs⟩

/-- Kernel realization along a fully faithful functor with injective values is
faithful. -/
theorem kernelFunctor_faithful_of_injective_objects
    (F : Functor V C) [F.Additive] [F.Full] [F.Faithful]
    (hI : ∀ X : V, Injective (F.obj X)) :
    (kernelFunctor F).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨f, rfl⟩ := (LeftFreyd.quotient _).map_surjective f
    obtain ⟨g, rfl⟩ := (LeftFreyd.quotient _).map_surjective g
    apply LeftFreyd.eq_of_leftHomotopy
    exact leftHomotopy_of_rawKernel_map_eq_of_injective_objects F hI f g h

end FullyFaithfulInjectives

section ProjectiveInjectives

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The kernel realization for arrows between projective-injective objects. -/
abbrev projectiveInjectiveKernelFunctor :
    Preadditive.LeftFreyd (ProjectiveInjectiveObject C) ⥤ C :=
  kernelFunctor (ProjectiveInjectiveObject.ι C)

variable {C}

instance : (projectiveInjectiveKernelFunctor C).Full :=
  kernelFunctor_full_of_injective_objects
    (ProjectiveInjectiveObject.ι C) (fun X ↦ X.property.2)

instance : (projectiveInjectiveKernelFunctor C).Faithful :=
  kernelFunctor_faithful_of_injective_objects
    (ProjectiveInjectiveObject.ι C) (fun X ↦ X.property.2)

section ProjectiveDimension

/-- In global dimension at most two, the kernel of a map between projectives
is projective. -/
theorem kernel_projective_of_projectiveDimensionLE_two
    {P₀ P₁ : C} [Projective P₀] [Projective P₁] (d : P₀ ⟶ P₁)
    (hglobal : ∀ X : C, HasProjectiveDimensionLE X 2) :
    Projective (kernel d) := by
  let Q : C := Abelian.coimage d
  let T : C := cokernel (Abelian.factorThruCoimage d)
  let S₁ : ShortComplex C :=
    ShortComplex.mk (Abelian.factorThruCoimage d)
      (cokernel.π (Abelian.factorThruCoimage d))
      (cokernel.condition (Abelian.factorThruCoimage d))
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel (Abelian.factorThruCoimage d)
      mono_f := inferInstance
      epi_g := inferInstance }
  have hQ : HasProjectiveDimensionLE Q 1 :=
    hS₁.hasProjectiveDimensionLT_X₁ 2 inferInstance (hglobal T)
  let S₀ : ShortComplex C :=
    ShortComplex.mk (kernel.ι d) (Abelian.coimage.π d)
      (cokernel.condition (kernel.ι d))
  have hS₀ : S₀.ShortExact :=
    { exact := ShortComplex.exact_cokernel (kernel.ι d)
      mono_f := inferInstance
      epi_g := inferInstance }
  have hkernel : HasProjectiveDimensionLT (kernel d) 1 :=
    hS₀.hasProjectiveDimensionLT_X₁ 1 inferInstance hQ
  exact projective_iff_hasProjectiveDimensionLT_one.mpr hkernel

/-- Under a global-dimension-two hypothesis, the kernel realization lands in
the full subcategory of projective objects. -/
def projectiveInjectiveKernelFunctorToProjectives
    (hglobal : ∀ X : C, HasProjectiveDimensionLE X 2) :
    Preadditive.LeftFreyd (ProjectiveInjectiveObject C) ⥤ ProjectiveObject C :=
  (isProjective C).lift (projectiveInjectiveKernelFunctor C) (fun X ↦ by
    change Projective (kernel X.as.hom.hom)
    exact kernel_projective_of_projectiveDimensionLE_two X.as.hom.hom hglobal)

instance (hglobal : ∀ X : C, HasProjectiveDimensionLE X 2) :
    (projectiveInjectiveKernelFunctorToProjectives (C := C) hglobal).Full where
  map_surjective f := by
    obtain ⟨g, hg⟩ := (projectiveInjectiveKernelFunctor C).map_surjective f.hom
    refine ⟨g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

instance (hglobal : ∀ X : C, HasProjectiveDimensionLE X 2) :
    (projectiveInjectiveKernelFunctorToProjectives (C := C) hglobal).Faithful where
  map_injective {X Y} f g h := by
    apply (projectiveInjectiveKernelFunctor C).map_injective
    exact congrArg (ProjectiveObject.ι C).map h

/-- A two-term projective-injective copresentation of an object.  Exactness
and monicity identify the object with the kernel of the displayed
differential. -/
structure ProjectiveInjectiveCopresentation (P : C) where
  I₀ : ProjectiveInjectiveObject C
  I₁ : ProjectiveInjectiveObject C
  augmentation : P ⟶ I₀.obj
  differential : I₀ ⟶ I₁
  zero : augmentation ≫ differential.hom = 0
  [augmentation_mono : Mono augmentation]
  exact :
    (ShortComplex.mk augmentation differential.hom zero).Exact

attribute [instance] ProjectiveInjectiveCopresentation.augmentation_mono

namespace ProjectiveInjectiveCopresentation

variable {P : C}

/-- The arrow between projective-injectives underlying a copresentation. -/
def arrow (I : ProjectiveInjectiveCopresentation P) :
    Arrow (ProjectiveInjectiveObject C) :=
  Arrow.mk I.differential

/-- The kernel of the displayed differential is the copresented object. -/
def kernelIso (I : ProjectiveInjectiveCopresentation P) :
    kernel I.differential.hom ≅ P :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel I.differential.hom)
    I.exact.fIsKernel

/-- Transport a projective-injective copresentation across an isomorphism of
the copresented object. -/
def ofIso {Q : C} (I : ProjectiveInjectiveCopresentation P) (e : P ≅ Q) :
    ProjectiveInjectiveCopresentation Q := by
  let augmentation : Q ⟶ I.I₀.obj := e.inv ≫ I.augmentation
  have zero : augmentation ≫ I.differential.hom = 0 := by
    simp [augmentation, I.zero]
  let S : ShortComplex C :=
    ShortComplex.mk augmentation I.differential.hom zero
  let eS : ShortComplex.mk I.augmentation I.differential.hom I.zero ≅ S :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)
  exact
    { I₀ := I.I₀
      I₁ := I.I₁
      augmentation := augmentation
      differential := I.differential
      zero := zero
      exact := ShortComplex.exact_of_iso eS I.exact }

section Biproduct

variable {J : Type} [Fintype J] [HasFiniteBiproducts C]
variable (P : J → C) (I : ∀ j, ProjectiveInjectiveCopresentation (P j))

private local instance (j : J) : Projective (I j).I₀.obj := (I j).I₀.property.1
private local instance (j : J) : Injective (I j).I₀.obj := (I j).I₀.property.2
private local instance (j : J) : Projective (I j).I₁.obj := (I j).I₁.property.1
private local instance (j : J) : Injective (I j).I₁.obj := (I j).I₁.property.2
private local instance (j : J) : Mono (I j).augmentation := inferInstance

private abbrev biproductI₀ : C := ⨁ fun j ↦ (I j).I₀.obj

private abbrev biproductI₁ : C := ⨁ fun j ↦ (I j).I₁.obj

private theorem projectiveBiproduct (X : J → C) (hX : ∀ j, Projective (X j)) :
    Projective (⨁ X) where
  factors f e _ := by
    let l (j : J) : X j ⟶ _ := by
      letI : Projective (X j) := hX j
      exact Projective.factorThru (biproduct.ι X j ≫ f) e
    refine ⟨biproduct.desc l, ?_⟩
    apply biproduct.hom_ext'
    intro j
    simp [l]

private theorem injectiveBiproduct (X : J → C) (hX : ∀ j, Injective (X j)) :
    Injective (⨁ X) where
  factors g f _ := by
    let l (j : J) : _ ⟶ X j := by
      letI : Injective (X j) := hX j
      exact Injective.factorThru (g ≫ biproduct.π X j) f
    refine ⟨biproduct.lift l, ?_⟩
    apply biproduct.hom_ext
    intro j
    simp [l]

private theorem monoBiproductMap {X Y : J → C} (p : ∀ j, X j ⟶ Y j)
    (hp : ∀ j, Mono (p j)) : Mono (biproduct.map p) where
  right_cancellation g h e := by
    apply biproduct.hom_ext
    intro j
    letI : Mono (p j) := hp j
    apply (cancel_mono (p j)).1
    have e' := congrArg (fun q ↦ q ≫ biproduct.π Y j) e
    simpa [Category.assoc] using e'

private def biproductI₀ProjectiveInjective : ProjectiveInjectiveObject C :=
  { obj := biproductI₀ P I
    property := ⟨projectiveBiproduct _ (fun j ↦ (I j).I₀.property.1),
      injectiveBiproduct _ (fun j ↦ (I j).I₀.property.2)⟩ }

private def biproductI₁ProjectiveInjective : ProjectiveInjectiveObject C :=
  { obj := biproductI₁ P I
    property := ⟨projectiveBiproduct _ (fun j ↦ (I j).I₁.property.1),
      injectiveBiproduct _ (fun j ↦ (I j).I₁.property.2)⟩ }

private abbrev biproductAugmentation :
    (⨁ P) ⟶ biproductI₀ P I :=
  biproduct.map fun j ↦ (I j).augmentation

private abbrev biproductDifferentialUnderlying :
    biproductI₀ P I ⟶ biproductI₁ P I :=
  biproduct.map fun j ↦ (I j).differential.hom

private def biproductDifferential :
    biproductI₀ProjectiveInjective P I ⟶
      biproductI₁ProjectiveInjective P I :=
  ObjectProperty.homMk (biproductDifferentialUnderlying P I)

private theorem biproduct_zero :
    biproductAugmentation P I ≫ biproductDifferentialUnderlying P I = 0 := by
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc, biproduct.map_π, ← Category.assoc,
    biproduct.map_π, Category.assoc, (I j).zero, comp_zero, zero_comp]

private def biproductIsKernel :
    IsLimit (KernelFork.ofι (biproductAugmentation P I)
      (biproduct_zero P I)) := by
  letI : Mono (biproductAugmentation P I) :=
    monoBiproductMap _ (fun j ↦ inferInstance)
  exact KernelFork.IsLimit.ofι' _ _ (fun {W} k hk ↦ by
    have hcomponent (j : J) :
        (k ≫ biproduct.π (fun j ↦ (I j).I₀.obj) j) ≫
            (I j).differential.hom = 0 := by
      have h := congrArg
        (fun q ↦ q ≫ biproduct.π (fun j ↦ (I j).I₁.obj) j) hk
      change
        (k ≫ biproduct.map (fun j ↦ (I j).differential.hom)) ≫
            biproduct.π (fun j ↦ (I j).I₁.obj) j =
          0 ≫ biproduct.π (fun j ↦ (I j).I₁.obj) j at h
      rw [Category.assoc, biproduct.map_π, zero_comp] at h
      simpa only [Category.assoc] using h
    let l (j : J) : W ⟶ P j :=
      (I j).exact.fIsKernel.lift
        (KernelFork.ofι
          (k ≫ biproduct.π (fun j ↦ (I j).I₀.obj) j)
          (hcomponent j))
    refine ⟨biproduct.lift l, ?_⟩
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.map_π, ← Category.assoc, biproduct.lift_π]
    exact (I j).exact.fIsKernel.fac
      (KernelFork.ofι
        (k ≫ biproduct.π (fun j ↦ (I j).I₀.obj) j)
        (hcomponent j)) WalkingParallelPair.zero)

/-- Finite biproducts of two-term projective-injective copresentations. -/
def biproduct : ProjectiveInjectiveCopresentation (⨁ P) :=
  { I₀ := biproductI₀ProjectiveInjective P I
    I₁ := biproductI₁ProjectiveInjective P I
    augmentation := biproductAugmentation P I
    differential := biproductDifferential P I
    zero := biproduct_zero P I
    augmentation_mono := monoBiproductMap _ (fun _ ↦ inferInstance)
    exact := ShortComplex.exact_of_f_is_kernel _ (biproductIsKernel P I) }

end Biproduct

end ProjectiveInjectiveCopresentation

/-- The Auslander--Bongartz--Gabriel kernel equivalence under global
dimension at most two and two-term projective-injective copresentations of
all projectives. -/
def auslanderBongartzGabrielEquivalence
    (hglobal : ∀ X : C, HasProjectiveDimensionLE X 2)
    (hcopresentation : ∀ P : ProjectiveObject C,
      Nonempty (ProjectiveInjectiveCopresentation P.obj)) :
    Preadditive.LeftFreyd (ProjectiveInjectiveObject C) ≌ ProjectiveObject C := by
  letI : (projectiveInjectiveKernelFunctorToProjectives
      (C := C) hglobal).EssSurj :=
    { mem_essImage := fun P ↦ by
        let I := (hcopresentation P).some
        refine ⟨(LeftFreyd.quotient _).obj I.arrow, ⟨?_⟩⟩
        exact ObjectProperty.isoMk _ I.kernelIso }
  letI : (projectiveInjectiveKernelFunctorToProjectives
      (C := C) hglobal).IsEquivalence := {}
  exact (projectiveInjectiveKernelFunctorToProjectives
    (C := C) hglobal).asEquivalence

end ProjectiveDimension

end ProjectiveInjectives

end Preadditive.LeftFreyd

end CategoryTheory
