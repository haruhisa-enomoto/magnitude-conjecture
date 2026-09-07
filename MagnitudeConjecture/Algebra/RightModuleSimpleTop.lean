import MagnitudeConjecture.Algebra.RightModuleEulerRoot
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.EndomorphismDrop
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# Simple tops and positive coordinate vectors

For each selected indecomposable projective, its radical quotient has the
corresponding standard basis vector as its projective-Hom dimension vector.
Finite biproducts of these quotients will therefore realize arbitrary
nonnegative integral coordinate vectors in the weak-positivity argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped BigOperators ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule

universe u

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- A simple module carried by `FGModuleCat` is a simple object of the
finitely generated module category. -/
theorem fgModule_simple_of_isSimpleModule
    (X : FGModuleCat.{u} R) [IsSimpleModule R X] : Simple X := by
  letI : Nontrivial X := IsSimpleModule.nontrivial R X
  constructor
  intro Y f _
  constructor
  · intro hf hzero
    letI : IsIso f := hf
    have hid : (𝟙 X : X ⟶ X) = 0 := by
      have hinv : inv f ≫ f = 𝟙 X :=
        IsIso.inv_hom_id_assoc f (𝟙 X)
      have hzeroInv : inv f ≫ f = 0 := by
        calc
          inv f ≫ f = inv f ≫ 0 :=
            congrArg (fun q ↦ inv f ≫ q) hzero
          _ = 0 := comp_zero
      exact hinv.symm.trans hzeroInv
    obtain ⟨x, hx⟩ : ∃ x : X, x ≠ 0 := exists_ne 0
    apply hx
    have hvalue := congrArg (fun q : X ⟶ X ↦ q.hom.hom x) hid
    simpa using hvalue
  · intro hne
    have hlinear : f.hom.hom ≠ 0 := by
      intro hzero
      apply hne
      apply FGModuleCat.hom_ext
      exact hzero
    have hsurjective : Function.Surjective f.hom.hom :=
      LinearMap.surjective_of_ne_zero hlinear
    letI : Epi f :=
      (IndecomposableSkeleton.fg_epi_iff_surjective f).2 hsurjective
    exact isIso_of_mono_of_epi f

/-- Conversely, a simple object of the finitely generated module category
is a simple module.  Noetherianity is used only to bundle an arbitrary
submodule as a finitely generated test object. -/
theorem fgModule_isSimpleModule_of_simple
    (X : FGModuleCat.{u} R) [Simple X] : IsSimpleModule R X := by
  have hnontrivial : Nontrivial X := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    letI : Subsingleton X := hsub
    apply CategoryTheory.id_nonzero X
    apply FGModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _
  letI : Nontrivial X := hnontrivial
  rw [isSimpleModule_iff]
  apply IsSimpleOrder.mk
  intro W
  letI : Module.Finite R W := inferInstance
  let Y := FGModuleCat.of R W
  let f : Y ⟶ X := FGModuleCat.ofHom W.subtype
  haveI : Mono f :=
    (IndecomposableSkeleton.fg_mono_iff_injective f).2
      W.injective_subtype
  by_cases hf : f = 0
  · left
    apply le_antisymm
    · intro x hx
      change x = 0
      let y : Y := ⟨x, hx⟩
      have hy := congrArg (fun q : Y ⟶ X ↦ q.hom.hom y) hf
      exact hy
    · exact bot_le
  · right
    haveI : IsIso f := (Simple.mono_isIso_iff_nonzero f).2 hf
    have hsurjective : Function.Surjective f.hom.hom :=
      (IndecomposableSkeleton.fg_epi_iff_surjective f).1 inferInstance
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hsurjective x
    rw [← hy]
    exact y.2

/-- Simplicity in `FGModuleCat` is exactly module-theoretic simplicity. -/
theorem fgModule_simple_iff_isSimpleModule (X : FGModuleCat.{u} R) :
    Simple X ↔ IsSimpleModule R X :=
  ⟨fun _ ↦ fgModule_isSimpleModule_of_simple X,
    fun _ ↦ fgModule_simple_of_isSimpleModule X⟩

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k B)

/-- The quotient of a finite module by its module Jacobson radical. -/
def radicalQuotientFGObj (P : FGModuleCat.{u} Bᵐᵒᵖ) :
    FGModuleCat.{u} Bᵐᵒᵖ :=
  FGModuleCat.of Bᵐᵒᵖ
    (P ⧸ Module.jacobson Bᵐᵒᵖ P)

/-- The quotient map to the module-Jacobson-radical quotient. -/
def radicalQuotientFGObjProjection (P : FGModuleCat.{u} Bᵐᵒᵖ) :
    P ⟶ radicalQuotientFGObj P :=
  FGModuleCat.ofHom (Module.jacobson Bᵐᵒᵖ P).mkQ

/-- The radical quotient of a selected indecomposable projective. -/
def projectiveSimpleTop (p : S.ProjectiveLabel) :
    FGModuleCat.{u} Bᵐᵒᵖ :=
  radicalQuotientFGObj (S.fgObj p.label)

/-- The canonical projection from a selected projective to its radical
quotient. -/
def projectiveSimpleTopProjection (p : S.ProjectiveLabel) :
    S.fgObj p.label ⟶ S.projectiveSimpleTop p :=
  radicalQuotientFGObjProjection (S.fgObj p.label)

omit [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
/-- The canonical projection to the radical quotient is epic. -/
theorem projectiveSimpleTopProjection_epi (p : S.ProjectiveLabel) :
    Epi (S.projectiveSimpleTopProjection p) := by
  apply (IndecomposableSkeleton.fg_epi_iff_surjective _).2
  change Function.Surjective
    (Module.jacobson Bᵐᵒᵖ (S.fgObj p.label)).mkQ
  exact Submodule.mkQ_surjective _

/-- The canonical projection to the radical quotient is nonzero. -/
theorem projectiveSimpleTopProjection_ne_zero (p : S.ProjectiveLabel) :
    S.projectiveSimpleTopProjection p ≠ 0 := by
  intro hzero
  have hmkQ :
      (Module.jacobson Bᵐᵒᵖ (S.fgObj p.label)).mkQ = 0 := by
    apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun
      (congrArg (fun f ↦ f.hom.hom) hzero) x
    change (Module.jacobson Bᵐᵒᵖ
      (S.fgObj p.label)).mkQ x = 0 at hx
    exact hx
  have hjtop :
      Module.jacobson Bᵐᵒᵖ (S.fgObj p.label) = ⊤ := by
    rw [← (Module.jacobson Bᵐᵒᵖ (S.fgObj p.label)).ker_mkQ,
      hmkQ, LinearMap.ker_zero]
  have hsurjective : Function.Surjective
      (S.projectiveBoundaryRadicalInclusion p.label).hom.hom := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [hjtop]
    trivial
  letI : Epi (S.projectiveBoundaryRadicalInclusion p.label) :=
    (IndecomposableSkeleton.fg_epi_iff_surjective _).2 hsurjective
  letI : Projective (S.fgObj p.label) := p.projective
  obtain ⟨s, hs⟩ := Projective.factors
    (𝟙 (S.fgObj p.label))
    (S.projectiveBoundaryRadicalInclusion p.label)
  exact
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
      p.label p.projective).not_isSplitEpi
      (IsSplitEpi.mk' { section_ := s, id := hs })

/-- The radical quotient of a selected indecomposable projective is a
simple module. -/
theorem projectiveSimpleTop_isSimpleModule (p : S.ProjectiveLabel) :
    IsSimpleModule Bᵐᵒᵖ (S.projectiveSimpleTop p) := by
  apply isSimpleModule_iff_isCoatom.mpr
  exact S.projectiveBoundary_jacobson_isCoatom p.label p.projective

/-- A distinct selected indecomposable projective has no map to the simple
top belonging to `p`. -/
theorem hom_projectiveSimpleTop_eq_zero
    (p q : S.ProjectiveLabel) (hpq : q ≠ p)
    (f : S.fgObj q.label ⟶ S.projectiveSimpleTop p) :
    f = 0 := by
  letI : Projective (S.fgObj q.label) := q.projective
  letI : Epi (S.projectiveSimpleTopProjection p) := by
    exact S.projectiveSimpleTopProjection_epi p
  obtain ⟨g, hg⟩ := Projective.factors f
    (S.projectiveSimpleTopProjection p)
  have hnot : ¬ IsSplitEpi g := by
    intro hsplit
    let hmono : IsSplitMono g :=
      @IndecomposableSkeleton.isSplitMono_of_isSplitEpi_between_obj
        Bᵐᵒᵖ _ _ (Fin S.n) S.almostSplitSkeleton
          q.label p.label g hsplit
    letI : IsSplitMono g := hmono
    letI : IsSplitEpi g := hsplit
    letI : IsIso g := isIso_of_mono_of_epi g
    apply hpq
    have hlabel : q.label = p.label :=
      S.fgObj_skeletal ⟨asIso g⟩
    cases p
    cases q
    simp_all
  obtain ⟨l, hl⟩ :=
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
      p.label p.projective).factors g hnot
  rw [← hg, ← hl, Category.assoc]
  apply FGModuleCat.hom_ext
  ext x
  change (Module.jacobson Bᵐᵒᵖ (S.fgObj p.label)).mkQ
    (l.hom.hom x).1 = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (l.hom.hom x).2

/-- The projective indexed by `p` maps one-dimensionally to its simple top. -/
theorem finrank_hom_projectiveSimpleTop_self_eq_one
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.ProjectiveLabel) :
    Module.finrank k
      (S.fgObj p.label ⟶ S.projectiveSimpleTop p) = 1 := by
  letI : Projective (S.fgObj p.label) := p.projective
  letI : Epi (S.projectiveSimpleTopProjection p) :=
    S.projectiveSimpleTopProjection_epi p
  apply (finrank_eq_one_iff_of_nonzero'
    (S.projectiveSimpleTopProjection p)
    (S.projectiveSimpleTopProjection_ne_zero p)).2
  intro f
  obtain ⟨g, hg⟩ := Projective.factors f
    (S.projectiveSimpleTopProjection p)
  obtain ⟨c, hc⟩ := H.endomorphism_eq_smul_id S p.label g
  refine ⟨c, ?_⟩
  rw [← hg, ← hc, CategoryTheory.Linear.smul_comp, Category.id_comp]

/-- The radical quotient of `p` has the standard basis vector at `p` as its
projective-Hom dimension vector. -/
theorem projectiveHomVectorFGObj_projectiveSimpleTop
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.ProjectiveLabel) :
    S.projectiveHomVectorFGObj (S.projectiveSimpleTop p) =
      Pi.single p 1 := by
  classical
  funext q
  by_cases hqp : q = p
  · subst q
    simp [projectiveHomVectorFGObj,
      S.finrank_hom_projectiveSimpleTop_self_eq_one H]
  · have hzero : Subsingleton
        (S.fgObj q.label ⟶ S.projectiveSimpleTop p) :=
      ⟨fun f g ↦ by
        rw [S.hom_projectiveSimpleTop_eq_zero p q hqp f,
          S.hom_projectiveSimpleTop_eq_zero p q hqp g]⟩
    letI := hzero
    rw [Pi.single_eq_of_ne hqp]
    change (Module.finrank k
      (S.fgObj q.label ⟶ S.projectiveSimpleTop p) : ℤ) = 0
    exact_mod_cast Module.finrank_zero_of_subsingleton

/-- Projective-Hom vectors are additive on binary biproducts. -/
theorem projectiveHomVectorFGObj_biprod
    (X Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    S.projectiveHomVectorFGObj (X ⊞ Y) =
      S.projectiveHomVectorFGObj X + S.projectiveHomVectorFGObj Y := by
  funext p
  change (Module.finrank k (S.fgObj p.label ⟶ (X ⊞ Y)) : ℤ) =
    (Module.finrank k (S.fgObj p.label ⟶ X) : ℤ) +
      (Module.finrank k (S.fgObj p.label ⟶ Y) : ℤ)
  let e : (S.fgObj p.label ⟶ (X ⊞ Y)) ≃ₗ[k]
      ((S.fgObj p.label ⟶ X) × (S.fgObj p.label ⟶ Y)) := {
    toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
    invFun f := biprod.lift f.1 f.2
    left_inv f := by apply biprod.hom_ext <;> simp
    right_inv f := by ext <;> simp
    map_add' f g := by ext <;> simp
    map_smul' r f := by ext <;> simp }
  exact_mod_cast e.finrank_eq.trans Module.finrank_prod

/-- Projective-Hom vectors are additive across a short exact sequence. -/
theorem projectiveHomVectorFGObj_middle_eq_add
    {Q : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ)}
    (hQ : Q.ShortExact) :
    S.projectiveHomVectorFGObj Q.X₂ =
      S.projectiveHomVectorFGObj Q.X₁ +
        S.projectiveHomVectorFGObj Q.X₃ := by
  funext p
  let f := CategoryTheory.Linear.rightComp k (S.fgObj p.label) Q.f
  let g := CategoryTheory.Linear.rightComp k (S.fgObj p.label) Q.g
  have hexact : Function.Exact f g :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.rightComp_exact
      (k := k) hQ (S.fgObj p.label)
  have hf : Function.Injective f := by
    letI := hQ.mono_f
    intro a b hab
    apply (cancel_mono Q.f).1
    exact hab
  have hg : Function.Surjective g := by
    letI := hQ.epi_g
    letI : Projective (S.fgObj p.label) := p.projective
    intro a
    obtain ⟨b, hb⟩ := Projective.factors a Q.g
    exact ⟨b, hb⟩
  change (Module.finrank k (S.fgObj p.label ⟶ Q.X₂) : ℤ) =
    (Module.finrank k (S.fgObj p.label ⟶ Q.X₁) : ℤ) +
      (Module.finrank k (S.fgObj p.label ⟶ Q.X₃) : ℤ)
  exact_mod_cast
    MagnitudeConjecture.LinearMap.finrank_eq_add_of_exact_of_injective_of_surjective
      f g hexact hf hg

/-- A finite biproduct of simple tops realizing the prescribed natural
projective-coordinate multiplicities. -/
def projectiveVectorRealization
    (v : S.ProjectiveLabel → ℕ) : FGModuleCat.{u} Bᵐᵒᵖ :=
  ⨁ fun j : Σ p : S.ProjectiveLabel, Fin (v p) ↦
    S.projectiveSimpleTop j.1

/-- Every nonnegative integral vector is the projective-Hom dimension vector
of the corresponding finite biproduct of simple tops. -/
theorem projectiveHomVectorFGObj_projectiveVectorRealization
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (v : S.ProjectiveLabel → ℕ) :
    S.projectiveHomVectorFGObj (S.projectiveVectorRealization v) =
      fun p ↦ (v p : ℤ) := by
  classical
  funext q
  change (Module.finrank k
      (S.fgObj q.label ⟶ S.projectiveVectorRealization v) : ℤ) =
    (v q : ℤ)
  rw [show Module.finrank k
      (S.fgObj q.label ⟶ S.projectiveVectorRealization v) =
      ∑ j : Σ p : S.ProjectiveLabel, Fin (v p),
        Module.finrank k
          (S.fgObj q.label ⟶ S.projectiveSimpleTop j.1) by
    exact MagnitudeConjecture.CategoryTheory.finrank_hom_eq_sum_of_iso_biproduct
      k (S.fgObj q.label) (S.projectiveVectorRealization v)
        (fun j : Σ p : S.ProjectiveLabel, Fin (v p) ↦
          S.projectiveSimpleTop j.1) (Iso.refl _)]
  push_cast
  simp_rw [show ∀ j : Σ p : S.ProjectiveLabel, Fin (v p),
      (Module.finrank k
        (S.fgObj q.label ⟶ S.projectiveSimpleTop j.1) : ℤ) =
          (Pi.single j.1 (1 : ℤ) : S.ProjectiveLabel → ℤ) q by
    intro j
    exact congrFun
      (S.projectiveHomVectorFGObj_projectiveSimpleTop H j.1) q]
  rw [Fintype.sum_sigma]
  simp [Pi.single_apply]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
