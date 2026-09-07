import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Realization of degree-one Ext classes

In an abelian category with enough projectives, every degree-one Ext class is
represented by a short exact sequence.  The construction pushes the kernel of
a projective presentation out along a degree-zero representative supplied by
the long exact Ext sequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.ExtOneRealization

universe w v u

variable {D : Type u} [Category.{v} D] [Abelian D]

namespace PushoutExtension

variable {P X T : D} (p : P ⟶ X)
variable (f : kernel p ⟶ T)

/-- The map from the pushout middle object to the presented endpoint. -/
def projection : pushout (kernel.ι p) f ⟶ X :=
  pushout.desc p 0 (by simp)

@[simp, reassoc]
theorem inl_projection :
    pushout.inl (kernel.ι p) f ≫ projection p f = p := by
  exact pushout.inl_desc _ _ _

@[simp, reassoc]
theorem inr_projection :
    pushout.inr (kernel.ι p) f ≫ projection p f = 0 := by
  exact pushout.inr_desc _ _ _

/-- The pushout short complex. -/
def shortComplex : ShortComplex D :=
  ShortComplex.mk (pushout.inr (kernel.ι p) f) (projection p f)
    (inr_projection p f)

variable [Epi p]

instance projection_epi : Epi (projection p f) := by
  apply epi_of_epi_fac (inl_projection p f)

/-- The pushout projection is a cokernel of the pushed kernel inclusion. -/
def projectionIsCokernel :
    IsColimit (CokernelCofork.ofπ (projection p f) (inr_projection p f)) := by
  let S₀ : ShortComplex D :=
    ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let hS₀ : S₀.ShortExact :=
    { exact := ShortComplex.exact_kernel p }
  let hpCokernel :
      IsColimit (CokernelCofork.ofπ p (kernel.condition p)) :=
    hS₀.gIsCokernel
  apply CokernelCofork.IsColimit.ofπ'
  intro A g hg
  have hj : kernel.ι p ≫
      (pushout.inl (kernel.ι p) f ≫ g) = 0 := by
    calc
      kernel.ι p ≫ (pushout.inl (kernel.ι p) f ≫ g) =
          f ≫ (pushout.inr (kernel.ι p) f ≫ g) := by
        rw [← Category.assoc, ← Category.assoc, pushout.condition]
      _ = 0 := by rw [hg, comp_zero]
  let d : X ⟶ A := hpCokernel.desc
    (CokernelCofork.ofπ
      (pushout.inl (kernel.ι p) f ≫ g) hj)
  have hd : p ≫ d = pushout.inl (kernel.ι p) f ≫ g :=
    hpCokernel.fac _ WalkingParallelPair.one
  refine ⟨d, ?_⟩
  apply pushout.hom_ext
  · rw [← Category.assoc, inl_projection, hd]
  · rw [← Category.assoc, inr_projection, zero_comp, hg]

/-- The pushout complex is short exact. -/
theorem shortExact : (shortComplex p f).ShortExact := by
  haveI : Mono (pushout.inr (kernel.ι p) f) := inferInstance
  haveI : Epi (projection p f) := projection_epi p f
  exact
    { exact := ShortComplex.exact_of_g_is_cokernel _
        (projectionIsCokernel p f)
      mono_f := by
        change Mono (pushout.inr (kernel.ι p) f)
        infer_instance
      epi_g := by
        change Epi (projection p f)
        infer_instance }

/-- The comparison from the kernel presentation to its pushout. -/
def fromPresentation :
    ShortComplex.mk (kernel.ι p) p (kernel.condition p) ⟶
      shortComplex p f where
  τ₁ := f
  τ₂ := pushout.inl (kernel.ι p) f
  τ₃ := 𝟙 X
  comm₁₂ := pushout.condition.symm
  comm₂₃ := by
    change pushout.inl (kernel.ι p) f ≫ projection p f = p ≫ 𝟙 X
    simp

/-- The pushout realizes the connecting image of `f`. -/
theorem extClass_eq_precomp [HasExt.{w} D] :
    (shortExact p f).extClass =
      ({ exact := ShortComplex.exact_kernel p } :
          (ShortComplex.mk (kernel.ι p) p
            (kernel.condition p)).ShortExact).extClass.comp
        (Ext.mk₀ f) (add_zero 1) := by
  let hS₀ :
      (ShortComplex.mk (kernel.ι p) p
        (kernel.condition p)).ShortExact :=
    { exact := ShortComplex.exact_kernel p }
  have hnat := ShortComplex.ShortExact.extClass_naturality
    hS₀ (shortExact p f) (fromPresentation p f)
  dsimp [fromPresentation] at hnat
  rw [Ext.mk₀_id_comp] at hnat
  exact hnat.symm

end PushoutExtension

variable [HasExt.{w} D] [EnoughProjectives D]

/-- Every degree-one Ext class in an abelian category with enough projectives
has a short exact realization. -/
theorem exists_shortExact_with_extClass_eq
    (X T : D) (xi : Ext.{w} X T 1) :
    ∃ (E : D) (i : T ⟶ E) (q : E ⟶ X)
      (zero : i ≫ q = 0)
      (hS : (ShortComplex.mk i q zero).ShortExact),
      hS.extClass = xi := by
  let P : ProjectivePresentation X :=
    Classical.choice (EnoughProjectives.presentation X)
  let S₀ : ShortComplex D :=
    ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)
  let hS₀ : S₀.ShortExact :=
    { exact := ShortComplex.exact_kernel P.f }
  obtain ⟨x₀, hx₀⟩ :=
    Ext.contravariant_sequence_exact₃ hS₀ T xi
      (Ext.eq_zero_of_projective _) (rfl : 1 + 0 = 1)
  let f : kernel P.f ⟶ T := (Ext.addEquiv₀ x₀)
  refine ⟨pushout (kernel.ι P.f) f,
    pushout.inr (kernel.ι P.f) f,
    PushoutExtension.projection P.f f,
    PushoutExtension.inr_projection P.f f,
    PushoutExtension.shortExact P.f f, ?_⟩
  rw [PushoutExtension.extClass_eq_precomp P.f f]
  change hS₀.extClass.comp (Ext.mk₀ (Ext.addEquiv₀ x₀))
      (add_zero 1) = xi
  rw [Ext.mk₀_addEquiv₀_apply]
  exact hx₀

end MagnitudeConjecture.ExtOneRealization
