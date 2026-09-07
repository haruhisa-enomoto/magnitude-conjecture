import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.FreydCategory.RightFreyd
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Cokernel realization of the right Freyd category

An additive functor `F : V ⥤ C` into an abelian category sends an arrow of
`V` to a morphism of `C`.  Taking its cokernel kills right homotopies, hence
descends to the right Freyd category.  When `F` is fully faithful and its
values are projective, this realization is fully faithful.

This is the cokernel/projective dual of the kernel/injective realization used
elsewhere in the project.  It packages the standard projective-presentation
lifting argument needed for Auslander's coherent duality.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory.Preadditive.RightFreyd

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {C : Type u'} [Category.{v'} C] [Abelian C]

/-- Before quotienting by right homotopy, send an arrow in `V` to the
cokernel of its image under `F`. -/
def rawCokernel (F : V ⥤ C) : Arrow V ⥤ C where
  obj a := cokernel (F.map a.hom)
  map {a b} f := cokernel.desc (F.map a.hom)
    (F.map f.right ≫ cokernel.π (F.map b.hom)) (by
      rw [← Category.assoc, ← F.map_comp, ← f.w, F.map_comp,
        Category.assoc, cokernel.condition, comp_zero])
  map_id a := by
    apply (cancel_epi (cokernel.π (F.map a.hom))).1
    simp only [cokernel.π_desc, Arrow.id_right, Functor.map_id,
      Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply (cancel_epi (cokernel.π (F.map _))).1
    simp

/-- The cokernel realization of a right Freyd category along an additive
functor. -/
def cokernelFunctor (F : V ⥤ C) [F.Additive] :
    Preadditive.RightFreyd V ⥤ C :=
  Quotient.lift (Arrow.rightHomotopic V) (rawCokernel F) (by
    rintro a b f g ⟨h⟩
    apply (cancel_epi (cokernel.π (F.map a.hom))).1
    simp only [rawCokernel, cokernel.π_desc]
    rw [← sub_eq_zero, ← Preadditive.sub_comp, ← F.map_sub, h.comm,
      F.map_comp, Category.assoc, cokernel.condition, comp_zero])

section FullyFaithfulProjectives

private theorem rawCokernel_map_surjective_of_projective_objects
    (F : V ⥤ C) [F.Additive] [F.Full] [F.Faithful]
    (hP : ∀ X : V, Projective (F.obj X))
    (a b : Arrow V)
    (f : cokernel (F.map a.hom) ⟶ cokernel (F.map b.hom)) :
    ∃ s : a ⟶ b, (rawCokernel F).map s = f := by
  letI : Projective (F.obj a.left) := hP a.left
  letI : Projective (F.obj a.right) := hP a.right
  let f₁ : F.obj a.right ⟶ F.obj b.right :=
    Projective.factorThru (cokernel.π (F.map a.hom) ≫ f)
      (cokernel.π (F.map b.hom))
  have hf₁ : f₁ ≫ cokernel.π (F.map b.hom) =
      cokernel.π (F.map a.hom) ≫ f := by
    simp [f₁]
  have hzero : (F.map a.hom ≫ f₁) ≫
      cokernel.π (F.map b.hom) = 0 := by
    rw [Category.assoc, hf₁, ← Category.assoc,
      cokernel.condition, zero_comp]
  let q : F.obj a.left ⟶ Abelian.image (F.map b.hom) :=
    kernel.lift (cokernel.π (F.map b.hom))
      (F.map a.hom ≫ f₁) hzero
  let f₀ : F.obj a.left ⟶ F.obj b.left :=
    Projective.factorThru q (Abelian.factorThruImage (F.map b.hom))
  have hsquare : F.map a.hom ≫ f₁ = f₀ ≫ F.map b.hom := by
    calc
      F.map a.hom ≫ f₁ = q ≫ Abelian.image.ι (F.map b.hom) := by
        simp [q]
      _ = (f₀ ≫ Abelian.factorThruImage (F.map b.hom)) ≫
          Abelian.image.ι (F.map b.hom) := by simp [f₀]
      _ = f₀ ≫ (Abelian.factorThruImage (F.map b.hom) ≫
          Abelian.image.ι (F.map b.hom)) := Category.assoc _ _ _
      _ = f₀ ≫ F.map b.hom := by rw [Abelian.image.fac]
  obtain ⟨g₀, hg₀⟩ := F.map_surjective f₀
  obtain ⟨g₁, hg₁⟩ := F.map_surjective f₁
  have hsquareV : a.hom ≫ g₁ = g₀ ≫ b.hom := by
    apply F.map_injective
    simpa only [F.map_comp, hg₀, hg₁] using hsquare
  let s : a ⟶ b := Arrow.homMk g₀ g₁ hsquareV.symm
  refine ⟨s, ?_⟩
  apply (cancel_epi (cokernel.π (F.map a.hom))).1
  simpa [s, rawCokernel, hg₁] using hf₁

private def rightHomotopy_of_rawCokernel_map_eq_of_projective_objects
    (F : V ⥤ C) [F.Additive] [F.Full] [F.Faithful]
    (hP : ∀ X : V, Projective (F.obj X))
    {a b : Arrow V} (s t : a ⟶ b)
    (hst : (rawCokernel F).map s = (rawCokernel F).map t) :
    Arrow.RightHomotopy s t := by
  letI : Projective (F.obj a.right) := hP a.right
  have hcokernel : (F.map s.right - F.map t.right) ≫
      cokernel.π (F.map b.hom) = 0 := by
    rw [Preadditive.sub_comp, sub_eq_zero]
    have h := congrArg
      (fun k ↦ cokernel.π (F.map a.hom) ≫ k) hst
    change
      cokernel.π (F.map a.hom) ≫
          cokernel.desc (F.map a.hom)
            (F.map s.right ≫ cokernel.π (F.map b.hom)) _ =
        cokernel.π (F.map a.hom) ≫
          cokernel.desc (F.map a.hom)
            (F.map t.right ≫ cokernel.π (F.map b.hom)) _ at h
    simpa only [cokernel.π_desc] using h
  let q : F.obj a.right ⟶ Abelian.image (F.map b.hom) :=
    kernel.lift (cokernel.π (F.map b.hom))
      (F.map s.right - F.map t.right) hcokernel
  let h : F.obj a.right ⟶ F.obj b.left :=
    Projective.factorThru q (Abelian.factorThruImage (F.map b.hom))
  have hfactor : F.map s.right - F.map t.right = h ≫ F.map b.hom := by
    calc
      F.map s.right - F.map t.right =
          q ≫ Abelian.image.ι (F.map b.hom) := by simp [q]
      _ = (h ≫ Abelian.factorThruImage (F.map b.hom)) ≫
          Abelian.image.ι (F.map b.hom) := by simp [h]
      _ = h ≫ (Abelian.factorThruImage (F.map b.hom) ≫
          Abelian.image.ι (F.map b.hom)) := Category.assoc _ _ _
      _ = h ≫ F.map b.hom := by rw [Abelian.image.fac]
  let hV : a.right ⟶ b.left := F.preimage h
  have hhV : F.map hV = h := F.map_preimage h
  exact
    { hom := hV
      comm := by
        apply F.map_injective
        simpa only [F.map_sub, F.map_comp, hhV] using hfactor }

/-- Cokernel realization along a fully faithful functor with projective
values is full. -/
theorem cokernelFunctor_full_of_projective_objects
    (F : V ⥤ C) [F.Additive] [F.Full] [F.Faithful]
    (hP : ∀ X : V, Projective (F.obj X)) :
    (cokernelFunctor F).Full where
  map_surjective {X Y} f := by
    rcases X with ⟨a⟩
    rcases Y with ⟨b⟩
    obtain ⟨s, hs⟩ :=
      rawCokernel_map_surjective_of_projective_objects F hP a b f
    exact ⟨(Preadditive.RightFreyd.quotient _).map s, hs⟩

/-- Cokernel realization along a fully faithful functor with projective
values is faithful. -/
theorem cokernelFunctor_faithful_of_projective_objects
    (F : V ⥤ C) [F.Additive] [F.Full] [F.Faithful]
    (hP : ∀ X : V, Projective (F.obj X)) :
    (cokernelFunctor F).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨f, rfl⟩ := (Preadditive.RightFreyd.quotient _).map_surjective f
    obtain ⟨g, rfl⟩ := (Preadditive.RightFreyd.quotient _).map_surjective g
    apply Preadditive.RightFreyd.eq_of_rightHomotopy
    exact rightHomotopy_of_rawCokernel_map_eq_of_projective_objects
      F hP f g h

end FullyFaithfulProjectives

section DenseCovers

/-- If every target object is an epimorphic image of an object in the image
of `F`, then every target object is the cokernel realization of a right-Freyd
presentation.  Applying the same hypothesis to the kernel of a chosen cover
produces the two-term presentation. -/
theorem cokernelFunctor_essSurj_of_epi_covers
    (F : V ⥤ C) [F.Additive] [F.Full]
    (hcover : ∀ Y : C, ∃ (X : V) (p : F.obj X ⟶ Y), Epi p) :
    (cokernelFunctor F).EssSurj where
  mem_essImage Y := by
    obtain ⟨X₀, p₀, hp₀⟩ := hcover Y
    letI : Epi p₀ := hp₀
    obtain ⟨X₁, p₁, hp₁⟩ := hcover (kernel p₀)
    letI : Epi p₁ := hp₁
    let d : F.obj X₁ ⟶ F.obj X₀ := p₁ ≫ kernel.ι p₀
    let f : X₁ ⟶ X₀ := F.preimage d
    have hf : F.map f = d := F.map_preimage d
    let T : ShortComplex C :=
      ShortComplex.mk d p₀ (by simp [d])
    have hT : T.Exact := by
      apply (ShortComplex.exact_iff_epi_kernel_lift _).2
      have hlift : kernel.lift p₀ d (by simp [d]) = p₁ := by
        apply (cancel_mono (kernel.ι p₀)).1
        simp [d]
      change Epi (kernel.lift p₀ d _)
      rw [hlift]
      infer_instance
    have hCokernel :
        IsColimit (CokernelCofork.ofπ p₀ T.zero) :=
      (T.exact_and_epi_g_iff_g_is_cokernel.1 ⟨hT, inferInstance⟩).some
    have hFzero : F.map f ≫ p₀ = 0 := by
      rw [hf]
      simp [d]
    have hRealization :
        IsColimit (CokernelCofork.ofπ p₀ hFzero) :=
      IsCokernel.ofIso d hCokernel _ (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (by simp [hf, d]) (by simp)
    refine ⟨(Preadditive.RightFreyd.quotient V).obj (Arrow.mk f), ⟨?_⟩⟩
    exact IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (F.map f)) hRealization

end DenseCovers

end CategoryTheory.Preadditive.RightFreyd
