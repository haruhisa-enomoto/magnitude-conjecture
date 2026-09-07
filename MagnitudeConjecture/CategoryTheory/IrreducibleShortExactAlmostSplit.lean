import MagnitudeConjecture.CategoryTheory.AlmostSplitDuality
import MagnitudeConjecture.CategoryTheory.AlmostSplitShortExact
import MagnitudeConjecture.CategoryTheory.IrreducibleAbelian

/-!
# Irreducible short exact sequences are almost split

We formalize the comparison argument of Auslander--Reiten--Smalø,
Proposition V.5.9, in the direction needed for the Butler--Ringel canonical
string sequences.  A short exact sequence whose two differentials are
irreducible is compared with an existing almost-split sequence at the same
right endpoint.  Irreducibility makes the comparison maps split monic; the
local endomorphism ring of the comparison kernel upgrades the left comparison
to an isomorphism, and the short five lemma upgrades the middle comparison.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An irreducible morphism in an abelian category is nonzero. -/
theorem isIrreducibleMorphism_ne_zero
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f) : f ≠ 0 := by
  intro hzero
  let Z : C := ⊥_ C
  let a : X ⟶ Z := 0
  let b : Z ⟶ Y := 0
  have hab : a ≫ b = f := by simp [a, b, hzero]
  rcases hf.factorization a b hab with ha | hb
  · letI : IsSplitMono a := ha
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := 0
        id := by
          rw [hzero, zero_comp]
          simpa only [a, zero_comp] using IsSplitMono.id a }
  · letI : IsSplitEpi b := hb
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := 0
        id := by
          rw [hzero, comp_zero]
          simpa only [b, comp_zero] using IsSplitEpi.id b }

/-- Exactness plus irreducibility of both differentials already forces a
short complex in an abelian category to be short exact. -/
theorem ShortComplex.shortExact_of_exact_of_irreducible
    {S : ShortComplex C} (hexact : S.Exact)
    (hf : IsIrreducibleMorphism S.f)
    (hg : IsIrreducibleMorphism S.g) : S.ShortExact := by
  have hfmono : Mono S.f :=
    hf.mono_or_epi.resolve_right (fun hfepi ↦ by
      letI : Epi S.f := hfepi
      have hgzero : S.g = 0 := by
        apply (cancel_epi S.f).1
        simpa only [comp_zero] using S.zero
      exact isIrreducibleMorphism_ne_zero hg hgzero)
  have hgepi : Epi S.g :=
    hg.mono_or_epi.resolve_left (fun hgmono ↦ by
      letI : Mono S.g := hgmono
      have hfzero : S.f = 0 := by
        apply (cancel_mono S.g).1
        simpa only [zero_comp] using S.zero
      exact isIrreducibleMorphism_ne_zero hf hfzero)
  exact ShortComplex.ShortExact.mk' hexact hfmono hgepi

/-- An object with local endomorphism ring is nonzero. -/
private theorem not_isZero_of_local_end
    (X : C) [IsLocalRing (End X)] : ¬ IsZero X := by
  intro hX
  have h : (1 : End X) = 0 := by
    change (𝟙 X : X ⟶ X) = 0
    exact (IsZero.iff_id_eq_zero X).mp hX
  exact one_ne_zero h

/-- A split monomorphism into an object with local endomorphism ring is an
isomorphism when its source is nonzero. -/
private theorem isIso_of_isSplitMono_to_local_end
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
    exact ⟨r, IsSplitMono.id f, hpone⟩

/-- No morphism obtained by postcomposing a left almost-split map can be
split epic onto a nonzero object when the source has local endomorphism
ring. -/
private theorem not_isSplitEpi_comp_of_leftAlmostSplit
    {X Y Z : C} [IsLocalRing (End X)]
    (f : X ⟶ Y) (hf : IsLeftAlmostSplit f)
    (g : Y ⟶ Z) (hZ : ¬ IsZero Z) :
    ¬ IsSplitEpi (f ≫ g) := by
  intro hsplit
  letI : IsSplitEpi (f ≫ g) := hsplit
  let r : Z ⟶ X := section_ (f ≫ g)
  let e : End X := End.of ((f ≫ g) ≫ r)
  have he : IsIdempotentElem e := by
    change e * e = e
    apply End.ext
    change ((f ≫ g) ≫ r) ≫ (f ≫ g) ≫ r = (f ≫ g) ≫ r
    rw [← Category.assoc ((f ≫ g) ≫ r) (f ≫ g) r,
      Category.assoc (f ≫ g) r (f ≫ g), IsSplitEpi.id,
      Category.comp_id]
  rcases
      QuotientSubmoduleEquidistribution.Foundation.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
        he with hezero | heone
  · apply hZ
    apply (IsZero.iff_id_eq_zero Z).mpr
    have hezeroHom : (f ≫ g) ≫ r = 0 := hezero
    have hpzero : f ≫ g = 0 := by
      calc
        f ≫ g = ((f ≫ g) ≫ r) ≫ (f ≫ g) := by
          rw [Category.assoc, IsSplitEpi.id, Category.comp_id]
        _ = 0 := by rw [hezeroHom, zero_comp]
    calc
      𝟙 Z = r ≫ (f ≫ g) := (IsSplitEpi.id (f ≫ g)).symm
      _ = 0 := by rw [hpzero, comp_zero]
  · apply hf.not_isSplitMono
    have heoneHom : (f ≫ g) ≫ r = 𝟙 X := heone
    exact IsSplitMono.mk'
      { retraction := g ≫ r
        id := by simpa only [Category.assoc] using heoneHom }

/-- Auslander--Reiten--Smalø V.5.9, comparison form.  If `S` is short exact
and both its maps are irreducible, then its terminal map is right almost
split as soon as an almost-split short exact sequence `T` with the same
right endpoint is available. -/
theorem ShortComplex.ShortExact.isRightAlmostSplit_of_irreducible
    {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (hf : IsIrreducibleMorphism S.f)
    (hg : IsIrreducibleMorphism S.g)
    (hTf : IsLeftAlmostSplit T.f)
    (hTg : IsRightAlmostSplit T.g)
    [IsLocalRing (End T.X₁)]
    (e₃ : S.X₃ ≅ T.X₃) :
    IsRightAlmostSplit S.g := by
  have hg₃ : IsIrreducibleMorphism (S.g ≫ e₃.hom) :=
    hg.postcomp_iso e₃
  obtain ⟨t, ht⟩ := hTg.factors (S.g ≫ e₃.hom) hg₃.not_isSplitEpi
  have htSplit : IsSplitMono t :=
    (hg₃.factorization t T.g ht).resolve_right hTg.not_isSplitEpi
  letI : IsSplitMono t := htSplit
  let h : T.X₂ ⟶ S.X₂ := retraction t
  letI : Mono T.f := hT.mono_f
  obtain ⟨s, hs⟩ := hT.exact.lift' (S.f ≫ t) (by
    rw [Category.assoc, ht, ← Category.assoc, S.zero, zero_comp])
  have hfactor : s ≫ (T.f ≫ h) = S.f := by
    calc
      s ≫ (T.f ≫ h) = (s ≫ T.f) ≫ h := (Category.assoc _ _ _).symm
      _ = (S.f ≫ t) ≫ h := by rw [hs]
      _ = S.f := by rw [Category.assoc, IsSplitMono.id, Category.comp_id]
  have hS₂ : ¬ IsZero S.X₂ := by
    intro hzero
    apply hg.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := 0
        id := hzero.eq_of_src _ _ }
  have hTh_not : ¬ IsSplitEpi (T.f ≫ h) :=
    not_isSplitEpi_comp_of_leftAlmostSplit T.f hTf h hS₂
  have hsSplit : IsSplitMono s :=
    (hf.factorization s (T.f ≫ h) hfactor).resolve_right hTh_not
  letI : IsSplitMono s := hsSplit
  have hS₁ : ¬ IsZero S.X₁ := by
    intro hzero
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := 0
        id := hzero.eq_of_src _ _ }
  letI : IsIso s := isIso_of_isSplitMono_to_local_end s hS₁
  let phi : S ⟶ T :=
    { τ₁ := s
      τ₂ := t
      τ₃ := e₃.hom
      comm₁₂ := hs
      comm₂₃ := ht }
  haveI : IsIso phi.τ₁ := inferInstanceAs (IsIso s)
  haveI : IsIso phi.τ₃ := inferInstanceAs (IsIso e₃.hom)
  haveI : IsIso t :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ phi hS hT
  have hpre := rightAlmostSplit_precomp_iso (asIso t) hTg
  change IsRightAlmostSplit (t ≫ T.g) at hpre
  rw [ht] at hpre
  have hback := hpre.postcomp_iso e₃.symm
  change IsRightAlmostSplit ((S.g ≫ e₃.hom) ≫ e₃.inv) at hback
  simpa only [Category.assoc, e₃.hom_inv_id, Category.comp_id] using hback

end MagnitudeConjecture.CategoryTheory
