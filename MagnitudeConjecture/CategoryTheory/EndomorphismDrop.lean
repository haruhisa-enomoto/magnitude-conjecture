import MagnitudeConjecture.CategoryTheory.LinearBiproduct
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Endomorphism dimension drops under nonsplit extension

This file formalizes the dimension comparison used in Ringel Section 2.3,
Lemma 1.  Exactness bounds Hom dimensions for the middle term by those for
the two endpoints.  If the extension is nonsplit, one of these bounds is
strict, hence replacing the endpoints by the middle term strictly lowers the
endomorphism dimension, even in the presence of an unchanged direct summand.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture

universe u v w

namespace LinearMap

variable {k : Type u} [Field k]
variable {U : Type v} {V : Type v} {W : Type v}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [Module k U] [Module k V] [Module k W]
  [FiniteDimensional k U] [FiniteDimensional k V]
  [FiniteDimensional k W]

/-- Exactness at the middle term gives the elementary dimension bound
`dim V ≤ dim U + dim W`. -/
theorem finrank_le_add_of_exact
    (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hfg : Function.Exact f g) :
    Module.finrank k V ≤ Module.finrank k U + Module.finrank k W := by
  have hker : g.ker = f.range := hfg.linearMap_ker_eq
  calc
    Module.finrank k V =
        Module.finrank k g.range + Module.finrank k g.ker :=
      (g.finrank_range_add_finrank_ker).symm
    _ = Module.finrank k g.range + Module.finrank k f.range := by
      rw [hker]
    _ ≤ Module.finrank k W + Module.finrank k U :=
      Nat.add_le_add (Submodule.finrank_le g.range)
        f.finrank_range_le
    _ = Module.finrank k U + Module.finrank k W := Nat.add_comm _ _

/-- If the second map in an exact pair is not onto, the middle dimension
bound is strict. -/
theorem finrank_lt_add_of_exact_of_not_surjective
    (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hfg : Function.Exact f g)
    (hg : ¬ Function.Surjective g) :
    Module.finrank k V < Module.finrank k U + Module.finrank k W := by
  have hker : g.ker = f.range := hfg.linearMap_ker_eq
  have hrange : g.range ≠ ⊤ := by
    intro hrange
    exact hg (LinearMap.range_eq_top.mp hrange)
  calc
    Module.finrank k V =
        Module.finrank k g.range + Module.finrank k g.ker :=
      (g.finrank_range_add_finrank_ker).symm
    _ = Module.finrank k g.range + Module.finrank k f.range := by
      rw [hker]
    _ < Module.finrank k W + Module.finrank k U :=
      Nat.add_lt_add_of_lt_of_le
        (Submodule.finrank_lt hrange) f.finrank_range_le
    _ = Module.finrank k U + Module.finrank k W := Nat.add_comm _ _

omit [FiniteDimensional k U] [FiniteDimensional k W] in
/-- A short exact pair of linear maps gives additivity of finite
dimensions. -/
theorem finrank_eq_add_of_exact_of_injective_of_surjective
    (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.finrank k V = Module.finrank k U + Module.finrank k W := by
  have hker : g.ker = f.range := hfg.linearMap_ker_eq
  have hfrange : Module.finrank k f.range = Module.finrank k U :=
    (LinearEquiv.ofInjective f hf).finrank_eq.symm
  have hgrange : g.range = ⊤ := LinearMap.range_eq_top.mpr hg
  calc
    Module.finrank k V =
        Module.finrank k g.range + Module.finrank k g.ker :=
      (g.finrank_range_add_finrank_ker).symm
    _ = Module.finrank k W + Module.finrank k U := by
      rw [hker, hfrange, hgrange, finrank_top]
    _ = Module.finrank k U + Module.finrank k W := Nat.add_comm _ _

end LinearMap

namespace CategoryTheory

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
  [Balanced C] [HasBinaryBiproducts C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Reorganize a finite biproduct by displaying two distinct summands first
and collecting all remaining summands in a complementary biproduct. -/
def biproductIsoPairComplement
    {J : Type*} [Fintype J] [DecidableEq J]
    (F : J → C) (i j : J) (hij : i ≠ j) :
    (⨁ F) ≅
      ((F i ⊞ F j) ⊞
        (⨁ fun t : {t : J // t ≠ i ∧ t ≠ j} ↦ F t.1)) := by
  let K := {t : J // t ≠ i ∧ t ≠ j}
  let G : K → C := fun t ↦ F t.1
  let q : (⨁ F) ⟶ (F i ⊞ F j) :=
    biprod.lift (biproduct.π F i) (biproduct.π F j)
  let r : (⨁ F) ⟶ (⨁ G) :=
    biproduct.lift fun t : K ↦ biproduct.π F t.1
  let u : (F i ⊞ F j) ⟶ (⨁ F) :=
    biprod.desc (biproduct.ι F i) (biproduct.ι F j)
  let v : (⨁ G) ⟶ (⨁ F) :=
    biproduct.desc fun t : K ↦ biproduct.ι F t.1
  have hiq : biproduct.ι F i ≫ q = biprod.inl := by
    apply biprod.hom_ext <;> simp [q, hij]
  have hjq : biproduct.ι F j ≫ q = biprod.inr := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst,
        biproduct.ι_π_ne F hij.symm]
      simp
    · simp [q]
  have htq (t : K) : biproduct.ι F t.1 ≫ q = 0 := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst,
        biproduct.ι_π_ne F t.2.1]
      simp
    · rw [Category.assoc, biprod.lift_snd,
        biproduct.ι_π_ne F t.2.2]
      simp
  have hir : biproduct.ι F i ≫ r = 0 := by
    apply biproduct.hom_ext
    intro t
    rw [Category.assoc, biproduct.lift_π, zero_comp,
      biproduct.ι_π_ne F (Ne.symm t.2.1)]
  have hjr : biproduct.ι F j ≫ r = 0 := by
    apply biproduct.hom_ext
    intro t
    rw [Category.assoc, biproduct.lift_π, zero_comp,
      biproduct.ι_π_ne F (Ne.symm t.2.2)]
  have htr (t : K) : biproduct.ι F t.1 ≫ r = biproduct.ι G t := by
    apply biproduct.hom_ext
    intro s
    rw [Category.assoc, biproduct.lift_π]
    by_cases hst : t = s
    · subst s
      simp [G]
    · rw [biproduct.ι_π_ne G hst]
      apply biproduct.ι_π_ne F
      intro hval
      apply hst
      exact Subtype.ext hval
  have huq : u ≫ q = 𝟙 (F i ⊞ F j) := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, hiq]
      simp
    · rw [← Category.assoc, biprod.inr_desc, hjq]
      simp
  have hur : u ≫ r = 0 := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, hir]
      simp
    · rw [← Category.assoc, biprod.inr_desc, hjr]
      simp
  have hvq : v ≫ q = 0 := by
    apply biproduct.hom_ext'
    intro t
    rw [← Category.assoc, biproduct.ι_desc, htq]
    simp
  have hvr : v ≫ r = 𝟙 (⨁ G) := by
    apply biproduct.hom_ext'
    intro t
    rw [← Category.assoc, biproduct.ι_desc, htr, Category.comp_id]
  exact {
    hom := biprod.lift q r
    inv := biprod.desc u v
    hom_inv_id := by
      apply biproduct.hom_ext'
      intro t
      rw [biprod.lift_desc, Preadditive.comp_add]
      by_cases hti : t = i
      · subst t
        rw [← Category.assoc, hiq, ← Category.assoc, hir,
          biprod.inl_desc, zero_comp]
        simp
      · by_cases htj : t = j
        · subst t
          rw [← Category.assoc, hjq, ← Category.assoc, hjr,
            biprod.inr_desc, zero_comp]
          simp
        · let t' : K := ⟨t, hti, htj⟩
          rw [← Category.assoc,
            show biproduct.ι F t ≫ q = 0 from htq t',
            ← Category.assoc,
            show biproduct.ι F t ≫ r = biproduct.ι G t' from htr t',
            zero_comp, zero_add, biproduct.ι_desc]
          rw [Category.comp_id]
    inv_hom_id := by
      apply biprod.hom_ext'
      · apply biprod.hom_ext
        · rw [← Category.assoc, biprod.inl_desc,
            Category.assoc, biprod.lift_fst, huq]
          simp
        · rw [← Category.assoc, biprod.inl_desc,
            Category.assoc, biprod.lift_snd, hur]
          simp
      · apply biprod.hom_ext
        · rw [← Category.assoc, biprod.inr_desc,
            Category.assoc, biprod.lift_fst, hvq]
          simp
        · rw [← Category.assoc, biprod.inr_desc,
            Category.assoc, biprod.lift_snd, hvr]
          simp
          dsimp only [G] }

omit [HasBinaryBiproducts C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
/-- Composition out of a fixed object carries a short exact sequence to an
exact pair of linear maps on Hom spaces. -/
theorem ShortComplex.ShortExact.rightComp_exact
    {S : ShortComplex C} (hS : S.ShortExact) (W : C) :
    Function.Exact
      (Linear.rightComp k W S.f)
      (Linear.rightComp k W S.g) := by
  rw [LinearMap.exact_iff]
  ext a
  constructor
  · intro ha
    rw [LinearMap.mem_ker] at ha
    change a ≫ S.g = 0 at ha
    obtain ⟨b, hb⟩ := KernelFork.IsLimit.lift' hS.fIsKernel a ha
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    rw [LinearMap.mem_ker]
    change (b ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]

omit [HasBinaryBiproducts C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
/-- Composition into a fixed object carries a short exact sequence to the
contravariant exact pair of linear maps on Hom spaces. -/
theorem ShortComplex.ShortExact.leftComp_exact
    {S : ShortComplex C} (hS : S.ShortExact) (W : C) :
    Function.Exact
      (Linear.leftComp k W S.g)
      (Linear.leftComp k W S.f) := by
  rw [LinearMap.exact_iff]
  ext a
  constructor
  · intro ha
    rw [LinearMap.mem_ker] at ha
    change S.f ≫ a = 0 at ha
    obtain ⟨b, hb⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel a ha
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    rw [LinearMap.mem_ker]
    change S.f ≫ S.g ≫ b = 0
    rw [← Category.assoc, S.zero, zero_comp]

omit [HasBinaryBiproducts C] [HasFiniteBiproducts C] in
/-- Hom out of the middle term is no larger than Hom out of the direct sum
of the two endpoints. -/
theorem ShortComplex.ShortExact.finrank_hom_from_middle_le
    {S : ShortComplex C} (hS : S.ShortExact) (W : C) :
    Module.finrank k (S.X₂ ⟶ W) ≤
      Module.finrank k (S.X₃ ⟶ W) +
        Module.finrank k (S.X₁ ⟶ W) :=
  MagnitudeConjecture.LinearMap.finrank_le_add_of_exact
    (Linear.leftComp k W S.g) (Linear.leftComp k W S.f)
      (ShortComplex.ShortExact.leftComp_exact (k := k) hS W)

omit [HasBinaryBiproducts C] [HasFiniteBiproducts C] in
/-- Hom into the middle term is no larger than Hom into the direct sum of
the two endpoints. -/
theorem ShortComplex.ShortExact.finrank_hom_to_middle_le
    {S : ShortComplex C} (hS : S.ShortExact) (W : C) :
    Module.finrank k (W ⟶ S.X₂) ≤
      Module.finrank k (W ⟶ S.X₁) +
        Module.finrank k (W ⟶ S.X₃) :=
  MagnitudeConjecture.LinearMap.finrank_le_add_of_exact
    (Linear.rightComp k W S.f) (Linear.rightComp k W S.g)
      (ShortComplex.ShortExact.rightComp_exact (k := k) hS W)

omit [HasBinaryBiproducts C] [HasFiniteBiproducts C] in
/-- For a nonsplit short exact sequence, the Hom bound into the source is
strict: the identity of the source cannot extend across the monomorphism. -/
theorem ShortComplex.ShortExact.finrank_hom_middle_to_source_lt
    {S : ShortComplex C} (hS : S.ShortExact)
    (hnonsplit : ¬ IsSplitMono S.f) :
    Module.finrank k (S.X₂ ⟶ S.X₁) <
      Module.finrank k (S.X₃ ⟶ S.X₁) +
        Module.finrank k (S.X₁ ⟶ S.X₁) := by
  apply MagnitudeConjecture.LinearMap.finrank_lt_add_of_exact_of_not_surjective
    (Linear.leftComp k S.X₁ S.g) (Linear.leftComp k S.X₁ S.f)
      (ShortComplex.ShortExact.leftComp_exact (k := k) hS S.X₁)
  intro hsurjective
  obtain ⟨r, hr⟩ := hsurjective (𝟙 S.X₁)
  apply hnonsplit
  exact IsSplitMono.mk' { retraction := r, id := hr }

omit [HasBinaryBiproducts C] [HasFiniteBiproducts C] in
/-- Ringel's strict comparison: the middle term of a nonsplit extension has
smaller endomorphism dimension than the direct sum of its endpoints, written
as the sum of the four matrix-block dimensions. -/
theorem ShortComplex.ShortExact.finrank_end_middle_lt_endpoint_blocks
    {S : ShortComplex C} (hS : S.ShortExact)
    (hnonsplit : ¬ IsSplitMono S.f) :
    Module.finrank k (S.X₂ ⟶ S.X₂) <
      Module.finrank k (S.X₁ ⟶ S.X₁) +
      Module.finrank k (S.X₁ ⟶ S.X₃) +
      Module.finrank k (S.X₃ ⟶ S.X₁) +
      Module.finrank k (S.X₃ ⟶ S.X₃) := by
  have hmiddle := ShortComplex.ShortExact.finrank_hom_to_middle_le
    (k := k) hS S.X₂
  have hsource := ShortComplex.ShortExact.finrank_hom_middle_to_source_lt
    (k := k) hS hnonsplit
  have htarget := ShortComplex.ShortExact.finrank_hom_from_middle_le
    (k := k) hS S.X₃
  omega

omit [Balanced C] [HasFiniteBiproducts C] in
/-- Endomorphisms of a binary biproduct are the four Hom matrix blocks. -/
theorem finrank_end_biprod (X Y : C) :
    Module.finrank k ((X ⊞ Y) ⟶ (X ⊞ Y)) =
      Module.finrank k (X ⟶ X) +
      Module.finrank k (X ⟶ Y) +
      Module.finrank k (Y ⟶ X) +
      Module.finrank k (Y ⟶ Y) := by
  let outEquiv : ((X ⊞ Y) ⟶ (X ⊞ Y)) ≃ₗ[k]
      (((X ⊞ Y) ⟶ X) × ((X ⊞ Y) ⟶ Y)) := {
    toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
    invFun f := biprod.lift f.1 f.2
    left_inv f := by apply biprod.hom_ext <;> simp
    right_inv f := by ext <;> simp
    map_add' f g := by ext <;> simp
    map_smul' r f := by ext <;> simp }
  let toXEquiv : ((X ⊞ Y) ⟶ X) ≃ₗ[k] ((X ⟶ X) × (Y ⟶ X)) := {
    toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
    invFun f := biprod.desc f.1 f.2
    left_inv f := by apply biprod.hom_ext' <;> simp
    right_inv f := by ext <;> simp
    map_add' f g := by ext <;> simp
    map_smul' r f := by ext <;> simp }
  let toYEquiv : ((X ⊞ Y) ⟶ Y) ≃ₗ[k] ((X ⟶ Y) × (Y ⟶ Y)) := {
    toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
    invFun f := biprod.desc f.1 f.2
    left_inv f := by apply biprod.hom_ext' <;> simp
    right_inv f := by ext <;> simp
    map_add' f g := by ext <;> simp
    map_smul' r f := by ext <;> simp }
  calc
    Module.finrank k ((X ⊞ Y) ⟶ (X ⊞ Y)) =
        Module.finrank k
          (((X ⊞ Y) ⟶ X) × ((X ⊞ Y) ⟶ Y)) :=
      outEquiv.finrank_eq
    _ = Module.finrank k ((X ⊞ Y) ⟶ X) +
        Module.finrank k ((X ⊞ Y) ⟶ Y) := Module.finrank_prod
    _ = (Module.finrank k (X ⟶ X) + Module.finrank k (Y ⟶ X)) +
        (Module.finrank k (X ⟶ Y) + Module.finrank k (Y ⟶ Y)) := by
      rw [toXEquiv.finrank_eq, toYEquiv.finrank_eq,
        Module.finrank_prod, Module.finrank_prod]
    _ = _ := by omega

omit [HasFiniteBiproducts C] in
/-- Ringel Section 2.3, Lemma 1 in the form needed for the minimization
argument: replacing two summands by a nonsplit extension strictly lowers the
endomorphism dimension even after adjoining an arbitrary unchanged summand. -/
theorem ShortComplex.ShortExact.finrank_end_middle_biprod_lt
    {S : ShortComplex C} (hS : S.ShortExact)
    (hnonsplit : ¬ IsSplitMono S.f) (R : C) :
    Module.finrank k ((S.X₂ ⊞ R) ⟶ (S.X₂ ⊞ R)) <
      Module.finrank k
        (((S.X₁ ⊞ S.X₃) ⊞ R) ⟶ ((S.X₁ ⊞ S.X₃) ⊞ R)) := by
  rw [finrank_end_biprod (k := k), finrank_end_biprod (k := k),
    finrank_end_biprod (k := k)]
  have hend := ShortComplex.ShortExact.finrank_end_middle_lt_endpoint_blocks
    (k := k) hS hnonsplit
  have hfrom := ShortComplex.ShortExact.finrank_hom_from_middle_le
    (k := k) hS R
  have hto := ShortComplex.ShortExact.finrank_hom_to_middle_le
    (k := k) hS R
  have hfromSplit : Module.finrank k ((S.X₁ ⊞ S.X₃) ⟶ R) =
      Module.finrank k (S.X₁ ⟶ R) + Module.finrank k (S.X₃ ⟶ R) := by
    let e : ((S.X₁ ⊞ S.X₃) ⟶ R) ≃ₗ[k]
        ((S.X₁ ⟶ R) × (S.X₃ ⟶ R)) := {
      toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
      invFun f := biprod.desc f.1 f.2
      left_inv f := by apply biprod.hom_ext' <;> simp
      right_inv f := by ext <;> simp
      map_add' f g := by ext <;> simp
      map_smul' r f := by ext <;> simp }
    exact e.finrank_eq.trans Module.finrank_prod
  have htoSplit : Module.finrank k (R ⟶ (S.X₁ ⊞ S.X₃)) =
      Module.finrank k (R ⟶ S.X₁) + Module.finrank k (R ⟶ S.X₃) := by
    let e : (R ⟶ (S.X₁ ⊞ S.X₃)) ≃ₗ[k]
        ((R ⟶ S.X₁) × (R ⟶ S.X₃)) := {
      toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
      invFun f := biprod.lift f.1 f.2
      left_inv f := by apply biprod.hom_ext <;> simp
      right_inv f := by ext <;> simp
      map_add' f g := by ext <;> simp
      map_smul' r f := by ext <;> simp }
    exact e.finrank_eq.trans Module.finrank_prod
  rw [hfromSplit, htoSplit]
  omega

end CategoryTheory

end MagnitudeConjecture
