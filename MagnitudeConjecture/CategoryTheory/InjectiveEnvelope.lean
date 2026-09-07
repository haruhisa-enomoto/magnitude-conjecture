import MagnitudeConjecture.CategoryTheory.AlmostSplitLocalFunctor
import MagnitudeConjecture.CategoryTheory.ProjectiveCover
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.ArtinianObject

/-!
# Categorical injective envelopes

An injective envelope is an injective monomorphism which is left minimal.
This file records the direct dual of the projective-cover calculus already
used in the formalization and relates left minimality to essential
monomorphisms.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v

variable {C : Type u} [Category.{v} C]

/-- An injective presentation whose monomorphism is left minimal. -/
structure MinimalInjectivePresentation (X : C)
    extends InjectivePresentation X where
  leftMinimal : IsLeftMinimal f

namespace MinimalInjectivePresentation

variable {X Y : C}

instance (I : MinimalInjectivePresentation X) : Injective I.J :=
  I.toInjectivePresentation.injective

instance (I : MinimalInjectivePresentation X) : Mono I.f :=
  I.toInjectivePresentation.mono

/-- Precomposing the envelope map with an isomorphism gives a minimal
injective presentation of the new source. -/
def preIso (I : MinimalInjectivePresentation X) (e : Y ≅ X) :
    MinimalInjectivePresentation Y where
  J := I.J
  f := e.hom ≫ I.f
  leftMinimal := by
    intro a ha
    apply I.leftMinimal a
    rw [← cancel_epi e.hom]
    simpa only [Category.assoc] using ha

/-- The injective targets of two minimal injective presentations of the
same object are isomorphic compatibly with their envelope maps. -/
noncomputable def objectIso
    (I J : MinimalInjectivePresentation X) : I.J ≅ J.J := by
  let a : I.J ⟶ J.J := Injective.factorThru J.f I.f
  let b : J.J ⟶ I.J := Injective.factorThru I.f J.f
  have ha : I.f ≫ a = J.f := Injective.comp_factorThru J.f I.f
  have hb : J.f ≫ b = I.f := Injective.comp_factorThru I.f J.f
  haveI hab : IsIso (a ≫ b) := I.leftMinimal (a ≫ b) (by
    rw [← Category.assoc, ha, hb])
  haveI hba : IsIso (b ≫ a) := J.leftMinimal (b ≫ a) (by
    rw [← Category.assoc, hb, ha])
  letI : IsIso a := isIso_of_isIso_comp_both a b
  exact asIso a

@[reassoc]
theorem comp_objectIso_hom
    (I J : MinimalInjectivePresentation X) :
    I.f ≫ (I.objectIso J).hom = J.f :=
  Injective.comp_factorThru J.f I.f

/-- Minimal injective presentations of isomorphic sources have isomorphic
injective targets. -/
noncomputable def objectIsoOfSourceIso
    (I : MinimalInjectivePresentation X)
    (J : MinimalInjectivePresentation Y) (e : X ≅ Y) : I.J ≅ J.J :=
  I.objectIso (J.preIso e)

@[reassoc]
theorem comp_objectIsoOfSourceIso_hom
    (I : MinimalInjectivePresentation X)
    (J : MinimalInjectivePresentation Y) (e : X ≅ Y) :
    I.f ≫ (I.objectIsoOfSourceIso J e).hom = e.hom ≫ J.f :=
  I.comp_objectIso_hom (J.preIso e)

end MinimalInjectivePresentation

section LocalEnd

variable [Preadditive C]

/-- A nonzero monomorphism into an object with local endomorphism ring is
left minimal. -/
theorem isLeftMinimal_of_mono_nonzero_of_local_end
    {X I : C} [IsLocalRing (End I)] (f : X ⟶ I) [Mono f]
    (hf : f ≠ 0) : IsLeftMinimal f := by
  intro e he
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := End I) (a := e) (b := 𝟙 I - e)
      (add_sub_cancel e (𝟙 I)) with heUnit | hsubUnit
  · exact (isUnit_iff_isIso e).1 heUnit
  · letI : IsIso (𝟙 I - e) :=
      (isUnit_iff_isIso (𝟙 I - e)).1 hsubUnit
    exfalso
    apply hf
    apply (cancel_mono (𝟙 I - e)).1
    rw [Preadditive.comp_sub, he]
    simp

end LocalEnd

section Abelian

variable [Abelian C]

/-- A two-step minimal injective presentation consists of injective envelopes
of an object and of the cokernel of its envelope. -/
structure TwoStepMinimalInjectivePresentation (X : C) where
  augmentation : MinimalInjectivePresentation X
  cosyzygyPresentation :
    MinimalInjectivePresentation (cokernel augmentation.f)

namespace TwoStepMinimalInjectivePresentation

variable {X : C}

/-- The first injective differential `I₀ ⟶ I₁`. -/
def differential (I : TwoStepMinimalInjectivePresentation X) :
    I.augmentation.J ⟶ I.cosyzygyPresentation.J :=
  cokernel.π I.augmentation.f ≫ I.cosyzygyPresentation.f

@[simp]
theorem augmentation_comp_differential
    (I : TwoStepMinimalInjectivePresentation X) :
    I.augmentation.f ≫ I.differential = 0 := by
  simp [differential]

/-- The associated exact injective complex `X ⟶ I₀ ⟶ I₁`. -/
def presentationComplex (I : TwoStepMinimalInjectivePresentation X) :
    ShortComplex C :=
  ShortComplex.mk I.augmentation.f I.differential
    I.augmentation_comp_differential

/-- The stored envelope of the first cosyzygy certifies exactness of the
two-step injective presentation. -/
theorem presentationComplex_exact
    (I : TwoStepMinimalInjectivePresentation X) :
    I.presentationComplex.Exact := by
  change (ShortComplex.mk I.augmentation.f I.differential
    I.augmentation_comp_differential).Exact
  apply (ShortComplex.exact_iff_mono_cokernel_desc _).2
  have hDesc :
      cokernel.desc I.augmentation.f I.differential
          I.augmentation_comp_differential =
        I.cosyzygyPresentation.f := by
    apply (cancel_epi (cokernel.π I.augmentation.f)).1
    simp [differential]
  rw [hDesc]
  infer_instance

end TwoStepMinimalInjectivePresentation

end Abelian

/-- A monomorphism is essential if monicity after postcomposition forces
monicity of the postcomposed morphism. -/
def IsEssentialMono {X Y : C} (f : X ⟶ Y) : Prop :=
  Mono f ∧ ∀ ⦃Z : C⦄ (g : Y ⟶ Z), Mono (f ≫ g) → Mono g

/-- A left-minimal monomorphism into an injective object is essential. -/
theorem isEssentialMono_of_isLeftMinimal
    {X I : C} [Injective I] (f : X ⟶ I) [Mono f]
    (hmin : IsLeftMinimal f) : IsEssentialMono f := by
  constructor
  · infer_instance
  · intro Z g hg
    letI : Mono (f ≫ g) := hg
    let l : Z ⟶ I := Injective.factorThru f (f ≫ g)
    have hl : f ≫ (g ≫ l) = f := by
      simpa only [Category.assoc] using Injective.comp_factorThru f (f ≫ g)
    haveI : IsIso (g ≫ l) := hmin (g ≫ l) hl
    exact mono_of_mono g l

/-- A nonzero monomorphism into an injective object with local endomorphism
ring is an essential monomorphism. -/
theorem isEssentialMono_of_mono_nonzero_of_injective_local_end
    [Preadditive C] {X I : C} [Injective I] [IsLocalRing (End I)]
    (f : X ⟶ I) [Mono f] (hf : f ≠ 0) : IsEssentialMono f :=
  isEssentialMono_of_isLeftMinimal f
    (isLeftMinimal_of_mono_nonzero_of_local_end f hf)

/-- An essential monomorphism into an injective object is left minimal when
monic endomorphisms of the injective target are invertible. -/
theorem isLeftMinimal_of_isEssentialMono
    {X I : C} [Injective I] (f : X ⟶ I)
    (hessential : IsEssentialMono f)
    (hendo : ∀ e : I ⟶ I, Mono e → IsIso e) : IsLeftMinimal f := by
  letI : Mono f := hessential.1
  intro e he
  have hmonoComp : Mono (f ≫ e) := by
    rw [he]
    infer_instance
  exact hendo e (hessential.2 e hmonoComp)

/-- For an injective target whose monic endomorphisms are invertible,
categorical left minimality is equivalent to essentiality. -/
theorem isEssentialMono_iff_isLeftMinimal
    {X I : C} [Injective I] (f : X ⟶ I) [Mono f] :
    (∀ e : I ⟶ I, Mono e → IsIso e) →
      (IsEssentialMono f ↔ IsLeftMinimal f) := by
  intro hendo
  constructor
  · exact fun h ↦ isLeftMinimal_of_isEssentialMono f h hendo
  · exact isEssentialMono_of_isLeftMinimal f

section EssentialSimple

variable [Abelian C]

/-- A nonzero simple subobject of the target of an essential monomorphism is
already contained in its source.  This is the categorical form of the
socle-intersection property of an injective envelope. -/
theorem exists_factor_thru_of_isEssentialMono_of_simple
    {X I S : C} (f : X ⟶ I) (hessential : IsEssentialMono f)
    [Simple S] (s : S ⟶ I) [Mono s] (hs : s ≠ 0) :
    ∃ t : S ⟶ X, t ≫ f = s := by
  letI : Mono f := hessential.1
  have hnotMono : ¬ Mono (f ≫ cokernel.π s) := by
    intro hmono
    letI : Mono (f ≫ cokernel.π s) := hmono
    letI : Mono (cokernel.π s) :=
      hessential.2 (cokernel.π s) inferInstance
    apply hs
    apply (cancel_mono (cokernel.π s)).1
    simp
  let q := kernel.ι (f ≫ cokernel.π s)
  have hq : q ≠ 0 := by
    intro hzero
    apply hnotMono
    exact Abelian.mono_of_kernel_ι_eq_zero (f ≫ cokernel.π s) hzero
  have hqfs : (q ≫ f) ≫ cokernel.π s = 0 := by
    simp only [Category.assoc]
    exact kernel.condition (f ≫ cokernel.π s)
  let a : kernel (f ≫ cokernel.π s) ⟶ S :=
    Abelian.monoLift s (q ≫ f) hqfs
  have ha_comp : a ≫ s = q ≫ f :=
    Abelian.monoLift_comp s (q ≫ f) hqfs
  have ha : a ≠ 0 := by
    intro hzero
    apply hq
    apply (cancel_mono f).1
    rw [← ha_comp, hzero]
    simp
  haveI : Mono (a ≫ s) := by
    rw [ha_comp]
    infer_instance
  haveI : Mono a := mono_of_mono a s
  haveI : IsIso a := isIso_of_mono_of_nonzero ha
  refine ⟨inv a ≫ q, ?_⟩
  rw [Category.assoc, ← ha_comp]
  simp

/-- Every map from a simple object into an essential extension lands in
the essential subobject.  Equivalently, its composite with the canonical
cokernel projection vanishes. -/
theorem simple_comp_cokernel_π_eq_zero_of_isEssentialMono
    {X I S : C} (f : X ⟶ I) (hessential : IsEssentialMono f)
    [Simple S] (s : S ⟶ I) :
    s ≫ cokernel.π f = 0 := by
  letI : Mono f := hessential.1
  by_cases hs : s = 0
  · rw [hs, zero_comp]
  · letI : Mono s := mono_of_nonzero_from_simple hs
    obtain ⟨t, ht⟩ :=
      exists_factor_thru_of_isEssentialMono_of_simple f hessential s hs
    rw [← ht, Category.assoc, cokernel.condition, comp_zero]

end EssentialSimple

section EssentialSocle

variable [Abelian C]

/-- A simple subobject through which every simple subobject factors is
essential, provided every nonzero subobject contains a simple subobject. -/
theorem isEssentialMono_of_simple_factors_of_exists_simple_subobject
    {L F : C} [Simple L]
    (l : L ⟶ F) [Mono l]
    (hsimple : ∀ {K : C} (i : K ⟶ F) [Mono i], ¬ IsZero K →
      ∃ (T : C) (s : T ⟶ K), Simple T ∧ Mono s)
    (hfactor : ∀ {T : C} [Simple T] (t : T ⟶ F) [Mono t],
      t ≠ 0 → ∃ a : T ⟶ L, a ≫ l = t) :
    IsEssentialMono l := by
  constructor
  · infer_instance
  · intro Z q hlq
    letI : Mono (l ≫ q) := hlq
    by_contra hq
    let K := kernel q
    let i : K ⟶ F := kernel.ι q
    have hK : ¬ IsZero K := by
      intro hKzero
      apply hq
      exact Abelian.mono_of_kernel_ι_eq_zero q (hKzero.eq_of_src i 0)
    obtain ⟨T, s, hTs, hs⟩ := hsimple i hK
    letI : Simple T := hTs
    letI : Mono s := hs
    let t : T ⟶ F := s ≫ i
    have ht : t ≠ 0 := by
      intro hzero
      apply CategoryTheory.id_nonzero T
      apply (cancel_mono t).1
      rw [hzero, Category.id_comp, zero_comp]
    obtain ⟨a, ha⟩ := hfactor t ht
    have hzero : a ≫ l ≫ q = 0 := by
      rw [← Category.assoc, ha]
      dsimp only [t]
      rw [Category.assoc, kernel.condition, comp_zero]
    have haZero : a = 0 := by
      apply (cancel_mono (l ≫ q)).1
      simpa only [Category.assoc, zero_comp] using hzero
    exact ht (by rw [← ha, haZero, zero_comp])

/-- In an Artinian object, a simple subobject containing every simple
subobject is essential. -/
theorem isEssentialMono_of_simple_factors
    {L F : C} [IsArtinianObject F] [Simple L]
    (l : L ⟶ F) [Mono l]
    (hfactor : ∀ {T : C} [Simple T] (t : T ⟶ F) [Mono t],
      t ≠ 0 → ∃ a : T ⟶ L, a ≫ l = t) :
    IsEssentialMono l := by
  apply isEssentialMono_of_simple_factors_of_exists_simple_subobject l ?_ hfactor
  intro K i _ hK
  letI : IsArtinianObject K := isArtinianObject_of_mono i
  refine ⟨simpleSubobject hK, simpleSubobjectArrow hK, inferInstance,
    inferInstance⟩

end EssentialSocle

/-- Right minimality becomes left minimality after taking the opposite
morphism. -/
theorem leftMinimal_unop {X Y : Cᵒᵖ} {f : X ⟶ Y}
    (hf : IsRightMinimal f) : IsLeftMinimal f.unop := by
  intro e he
  have heOp : e.op ≫ f = f := by
    simpa using congrArg (fun q ↦ q.op) he
  haveI : IsIso e.op := hf e.op heOp
  exact isIso_of_op e

end MagnitudeConjecture
