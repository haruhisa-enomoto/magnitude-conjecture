import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite realization of degree-one extension classes

Every degree-one extension class between finitely generated modules over a
Noetherian ring is represented by a short exact sequence whose middle term
is again finitely generated.  The proof constructs the pushout of a finite
free presentation explicitly, then compares extension classes after forgetting
finite generation.

This is the bounded presentation-theoretic construction needed for the
Auslander--Reiten realization argument; it has no dependence on the
OP-conjecture formalization.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.FGExtRealization

universe u

variable {R : Type u} [Ring R]

/-- Module projectivity gives categorical projectivity in the finitely
generated subcategory. -/
private theorem fgProjective_of_moduleProjective
    (X : FGModuleCat.{u} R) (h : Module.Projective R X) :
    Projective X := by
  letI : Module.Projective R X := h
  constructor
  intro E Y f e _hepi
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property e.hom.hom f.hom.hom
      ((QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective e).1
        inferInstance)
  refine ⟨FGModuleCat.ofHom g, ?_⟩
  apply FGModuleCat.hom_ext
  exact hg

/-- The finitely generated module category has enough finite free
projectives. -/
private theorem fgModuleCatEnoughProjectives :
    EnoughProjectives (FGModuleCat.{u} R) where
  presentation X := by
    classical
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
    let P : FGModuleCat.{u} R := FGModuleCat.of R (Fin n → R)
    let q : P ⟶ X := FGModuleCat.ofHom p
    have hP : Projective P := by
      apply fgProjective_of_moduleProjective P
      exact Module.Projective.of_basis (Pi.basisFun R (Fin n))
    have hq : Epi q :=
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective q).2 hp
    exact ⟨{ p := P, projective := hP, f := q, epi := hq }⟩

/-! ## Explicit pushouts of a presentation -/

namespace PushoutExtension

variable {P S T : Type u}
  [AddCommGroup P] [AddCommGroup S] [AddCommGroup T]
  [Module R P] [Module R S] [Module R T]

/-- The relation `(f x, -x)` used to push a kernel presentation out along
`f`. -/
def relationMap (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    LinearMap.ker p →ₗ[R] T × P :=
  f.prod (-(LinearMap.ker p).subtype)

/-- The relation submodule defining the pushout middle term. -/
def relation (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    Submodule R (T × P) :=
  LinearMap.range (relationMap p f)

/-- The explicit pushout middle term. -/
abbrev middle (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :=
  (T × P) ⧸ relation p f

instance [Module.Finite R T] [Module.Finite R P]
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    Module.Finite R (middle p f) := by
  infer_instance

/-- The inclusion of the extension kernel into the pushout. -/
def inclusion (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    T →ₗ[R] middle p f :=
  (relation p f).mkQ.comp (LinearMap.inl R T P)

/-- The map from the presentation projective into the pushout. -/
def presentationMap (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    P →ₗ[R] middle p f :=
  (relation p f).mkQ.comp (LinearMap.inr R T P)

private theorem relation_le_projectionPre_ker
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    relation p f ≤ (p.comp (LinearMap.snd R T P)).ker := by
  rintro y ⟨x, rfl⟩
  simp [relationMap]

/-- The quotient map from the pushout middle term to the presented module. -/
def projection (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    middle p f →ₗ[R] S :=
  Submodule.liftQ (relation p f)
    (p.comp (LinearMap.snd R T P))
    (relation_le_projectionPre_ker p f)

@[simp]
theorem inclusion_apply
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) (t : T) :
    inclusion p f t = (relation p f).mkQ (t, 0) := rfl

@[simp]
theorem presentationMap_apply
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) (x : P) :
    presentationMap p f x = (relation p f).mkQ (0, x) := rfl

@[simp]
theorem projection_mkQ
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) (y : T × P) :
    projection p f ((relation p f).mkQ y) = p y.2 := rfl

theorem inclusion_injective
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    Function.Injective (inclusion p f) := by
  rw [← LinearMap.ker_eq_bot]
  ext t
  constructor
  · intro ht
    have hmem : (t, 0) ∈ relation p f := by
      simpa [inclusion] using ht
    obtain ⟨x, hx⟩ := hmem
    have hxP : -(x : P) = 0 := by
      simpa [relationMap] using congrArg Prod.snd hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      simpa using congrArg Neg.neg hxP
    have hxT : f x = t := by
      simpa [relationMap] using congrArg Prod.fst hx
    simpa [hx0] using hxT.symm
  · rintro rfl
    simp

theorem projection_surjective
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f : LinearMap.ker p →ₗ[R] T) :
    Function.Surjective (projection p f) := by
  intro s
  obtain ⟨x, rfl⟩ := hp s
  exact ⟨(relation p f).mkQ (0, x), projection_mkQ p f (0, x)⟩

theorem exact_inclusion_projection
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    Function.Exact (inclusion p f) (projection p f) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro y hy
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      have hyp : p y.2 = 0 := by
        change projection p f ((relation p f).mkQ y) = 0 at hy
        rw [show projection p f ((relation p f).mkQ y) = p y.2 from
          projection_mkQ p f y] at hy
        exact hy
      let x : LinearMap.ker p := ⟨y.2, hyp⟩
      refine ⟨y.1 + f x, ?_⟩
      apply (Submodule.Quotient.eq (relation p f)).mpr
      refine ⟨x, ?_⟩
      ext
      · simp [relationMap, x]
      · simp [relationMap, x]
  · rintro _ ⟨t, rfl⟩
    change projection p f ((relation p f).mkQ (t, 0)) = 0
    simpa using projection_mkQ p f (t, 0)

/-- The explicit pushout short complex in the ambient module category. -/
abbrev shortComplex
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero
    (inclusion p f) (projection p f) (by
      ext t
      change projection p f ((relation p f).mkQ (t, 0)) = 0
      simpa using projection_mkQ p f (t, 0))

theorem shortExact
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f : LinearMap.ker p →ₗ[R] T) :
    (shortComplex p f).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact exact_inclusion_projection p f
  · exact inclusion_injective p f
  · exact projection_surjective p hp f

theorem presentation_relation
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    (inclusion p f).comp f =
      (presentationMap p f).comp (LinearMap.ker p).subtype := by
  ext x
  change (relation p f).mkQ (f x, 0) =
    (relation p f).mkQ (0, (x : P))
  apply (Submodule.Quotient.eq (relation p f)).mpr
  exact ⟨x, by ext <;> simp [relationMap]⟩

/-- The morphism from the kernel presentation to its explicit pushout. -/
def fromPresentation
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    p.shortComplexKer ⟶ shortComplex p f where
  τ₁ := ModuleCat.ofHom f
  τ₂ := ModuleCat.ofHom (presentationMap p f)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply ModuleCat.hom_ext
    exact presentation_relation p f
  comm₂₃ := by
    apply ModuleCat.hom_ext
    ext x
    exact projection_mkQ p f (0, x)

/-- The explicit pushout realizes the connecting image of `f`. -/
theorem extClass_eq_precomp
    [Small.{u} R]
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f : LinearMap.ker p →ₗ[R] T) :
    (shortExact p hp f).extClass =
      (LinearMap.shortExact_shortComplexKer hp).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom f)) (add_zero 1) := by
  have hnat :=
    ShortComplex.ShortExact.extClass_naturality
      (LinearMap.shortExact_shortComplexKer hp)
      (shortExact p hp f) (fromPresentation p f)
  dsimp [fromPresentation] at hnat
  rw [Ext.mk₀_id_comp] at hnat
  exact hnat.symm

/-- Every ambient `Ext¹` class is represented by one of the explicit
pushouts. -/
theorem exists_pushout_with_extClass_eq
    [Small.{u} R] [Module.Free R P]
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (x : Ext (ModuleCat.of R S) (ModuleCat.of R T) 1) :
    ∃ f : LinearMap.ker p →ₗ[R] T,
      (shortExact p hp f).extClass = x := by
  letI : Projective (ModuleCat.of R P) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R P)
  let hbase := LinearMap.shortExact_shortComplexKer hp
  obtain ⟨x₀, hx₀⟩ :=
    Ext.contravariant_sequence_exact₃ hbase (ModuleCat.of R T) x
      (Ext.eq_zero_of_projective _) (rfl : 1 + 0 = 1)
  let f : LinearMap.ker p →ₗ[R] T := (Ext.addEquiv₀ x₀).hom
  refine ⟨f, ?_⟩
  rw [extClass_eq_precomp p hp f]
  change hbase.extClass.comp
      (Ext.mk₀ (Ext.addEquiv₀ x₀)) (add_zero 1) = x
  rw [Ext.mk₀_addEquiv₀_apply]
  exact hx₀

end PushoutExtension

/-! ## Bundling the construction in finitely generated modules -/

/-- The fully faithful inclusion of finitely generated modules into all
modules. -/
abbrev inclusion : FGModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)

instance inclusion_additive : (inclusion (R := R)).Additive where
  map_add := rfl

/-- A projective finitely generated module remains projective after forgetting
finite generation. -/
instance inclusion_preservesProjectiveObjects [IsNoetherianRing R] :
    (inclusion (R := R)).PreservesProjectiveObjects where
  projective_obj {X} hX := by
    letI : Module.Projective R X :=
      MagnitudeConjecture.moduleProjective_of_fgProjective X hX
    exact X.obj.projective_of_categoryTheory_projective

namespace PushoutExtension

variable {P S T : Type u}
  [AddCommGroup P] [AddCommGroup S] [AddCommGroup T]
  [Module R P] [Module R S] [Module R T]
  [Module.Finite R P] [Module.Finite R S] [Module.Finite R T]

/-- The explicit pushout sequence bundled in finitely generated modules. -/
abbrev fgShortComplex
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk
    (FGModuleCat.ofHom (inclusion p f))
    (FGModuleCat.ofHom (projection p f))
    (by
      apply FGModuleCat.hom_ext
      ext t
      change projection p f ((relation p f).mkQ (t, 0)) = 0
      simpa using projection_mkQ p f (t, 0))

theorem fgShortComplex_map_inclusion
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    (fgShortComplex p f).map (FGExtRealization.inclusion (R := R)) =
      shortComplex p f := by
  rfl

/-- The finite pushout complex is short exact. -/
theorem fgShortExact
    [IsNoetherianRing R]
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f : LinearMap.ker p →ₗ[R] T) :
    (fgShortComplex p f).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful
    (FGExtRealization.inclusion (R := R))
  simpa [fgShortComplex_map_inclusion] using shortExact p hp f

end PushoutExtension

variable [IsNoetherianRing R] [HasExt.{u} (FGModuleCat.{u} R)]

/-- Every degree-one `Ext` class between finitely generated modules is
represented by a finite short exact sequence. -/
theorem exists_shortExact_with_extClass_eq
    (X T : FGModuleCat.{u} R) (xi : Ext X T 1) :
    ∃ (E : FGModuleCat.{u} R) (i : T ⟶ E) (q : E ⟶ X)
      (zero : i ≫ q = 0)
      (hS : (ShortComplex.mk i q zero).ShortExact),
      hS.extClass = xi := by
  letI : EnoughProjectives (FGModuleCat.{u} R) :=
    fgModuleCatEnoughProjectives
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
  let xiAmbient :
      Ext ((inclusion (R := R)).obj X) ((inclusion (R := R)).obj T) 1 :=
    xi.mapExactFunctor (inclusion (R := R))
  obtain ⟨f, hf⟩ :=
    PushoutExtension.exists_pushout_with_extClass_eq p hp xiAmbient
  let S : ShortComplex (FGModuleCat.{u} R) :=
    PushoutExtension.fgShortComplex p f
  let hS : S.ShortExact := PushoutExtension.fgShortExact p hp f
  refine ⟨S.X₂, S.f, S.g, S.zero, hS, ?_⟩
  apply
    ((inclusion (R := R)).mapExt_bijective_of_preservesProjectiveObjects
      X T 1).injective
  change hS.extClass.mapExactFunctor (inclusion (R := R)) =
    xi.mapExactFunctor (inclusion (R := R))
  rw [Ext.mapExactFunctor_extClass]
  convert hf using 1 <;> rfl

end MagnitudeConjecture.FGExtRealization
