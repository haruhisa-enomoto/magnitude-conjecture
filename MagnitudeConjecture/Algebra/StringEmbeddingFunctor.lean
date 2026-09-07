import MagnitudeConjecture.Algebra.StringFiniteModule
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The finite-string embedding functor

For a literal string word `C`, Butler--Ringel's functor `S_C` replaces every
one-dimensional position of the literal string module by a copy of a supplied
vector space.  Concretely, its value at a quiver vertex `x` is

`C.Space x ⊗ V`,

and an arrow acts by the literal string arrow map tensored with the identity
of `V`.  Defining this after the string representation has descended through
the relation quotient makes the relation check automatic.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The right module obtained by replacing each position basis line of a
literal string module by a copy of `V`. -/
def scalarRightModule (C : Word R) (hmono : IsMonomial R)
    (V : ModuleCat.{u} k) :
    (Category R)ᵒᵖ ⥤ ModuleCat.{u} k :=
  C.rightModule hmono ⋙
    (MonoidalCategory.tensorRight V :
      ModuleCat.{u} k ⥤ ModuleCat.{u} k)

instance scalarRightModule_additive (C : Word R) (hmono : IsMonomial R)
    (V : ModuleCat.{u} k) :
    (C.scalarRightModule hmono V).Additive := by
  unfold scalarRightModule
  infer_instance

instance scalarRightModule_linear (C : Word R) (hmono : IsMonomial R)
    (V : ModuleCat.{u} k) :
    (C.scalarRightModule hmono V).Linear k := by
  unfold scalarRightModule
  infer_instance

/-- The coefficient-copy string module evaluates a quotient path by the
literal string path map tensored with the identity of the coefficient
space. -/
@[simp]
theorem scalarRightModule_map_pathMap
    (C : Word R) (hmono : IsMonomial R) (V : ModuleCat.{u} k)
    {x y : Q} (p : Quiver.Path x y) :
    (C.scalarRightModule hmono V).map (pathMap R p).op =
      C.quiverMap p ▷ V := by
  unfold scalarRightModule
  change (C.rightModule hmono).map (pathMap R p).op ▷ V = _
  rw [C.rightModule_map_pathMap]
  rfl

/-- The scalar-copy string representation as a bundled linear module. -/
def scalarRightLinearModule (C : Word R) (hmono : IsMonomial R)
    (V : ModuleCat.{u} k) :
    MagnitudeConjecture.CoveringHom.LinearModuleCategory
      (C := (Category R)ᵒᵖ) k :=
  ⟨C.scalarRightModule hmono V, inferInstance, inferInstance⟩

@[simp]
theorem scalarRightLinearModule_obj (C : Word R) (hmono : IsMonomial R)
    (V : ModuleCat.{u} k) (X : (Category R)ᵒᵖ) :
    (C.scalarRightLinearModule hmono V).obj.obj X =
      (C.rightModule hmono).obj X ⊗ V :=
  rfl

/-- Replacing each position line by the one-dimensional vector space recovers
the literal string module. -/
def scalarRightLinearModuleUnitIso (C : Word R) (hmono : IsMonomial R) :
    C.scalarRightLinearModule hmono (ModuleCat.of k k) ≅
      C.rightLinearModule hmono :=
  ObjectProperty.isoMk
    (MagnitudeConjecture.CoveringHom.IsLinearModule
      (C := (Category R)ᵒᵖ) k)
    (Functor.isoWhiskerLeft (C.rightModule hmono)
        (MonoidalCategory.rightUnitorNatIso (ModuleCat.{u} k)) ≪≫
      (C.rightModule hmono).rightUnitor)

/-- Butler--Ringel's finite-string embedding functor `S_C`. -/
def stringEmbeddingFunctor (C : Word R) (hmono : IsMonomial R) :
    ModuleCat.{u} k ⥤
      MagnitudeConjecture.CoveringHom.LinearModuleCategory
        (C := (Category R)ᵒᵖ) k where
  obj V := C.scalarRightLinearModule hmono V
  map {V W} f := ⟨
    { app := fun X ↦ (C.rightModule hmono).obj X ◁ f
      naturality := by
        intro X Y g
        exact (MonoidalCategory.whisker_exchange
          ((C.rightModule hmono).map g) f).symm }⟩
  map_id V := by
    ext X
    simp
  map_comp f g := by
    ext X
    simp

instance stringEmbeddingFunctor_additive
    (C : Word R) (hmono : IsMonomial R) :
    (C.stringEmbeddingFunctor hmono).Additive where
  map_add {V W} f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    apply funext
    intro X
    exact MonoidalPreadditive.whiskerLeft_add f g

instance stringEmbeddingFunctor_linear
    (C : Word R) (hmono : IsMonomial R) :
    (C.stringEmbeddingFunctor hmono).Linear k where
  map_smul {V W} f r := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    apply funext
    intro X
    exact MonoidalLinear.whiskerLeft_smul (R := k)
      ((C.rightModule hmono).obj X) r f

@[simp]
theorem stringEmbeddingFunctor_obj_obj
    (C : Word R) (hmono : IsMonomial R)
    (V : ModuleCat.{u} k) (X : (Category R)ᵒᵖ) :
    ((C.stringEmbeddingFunctor hmono).obj V).obj.obj X =
      (C.rightModule hmono).obj X ⊗ V :=
  rfl

@[simp]
theorem stringEmbeddingFunctor_map_app
    (C : Word R) (hmono : IsMonomial R)
    {V W : ModuleCat.{u} k} (f : V ⟶ W) (X : (Category R)ᵒᵖ) :
    ((C.stringEmbeddingFunctor hmono).map f).hom.app X =
      (C.rightModule hmono).obj X ◁ f :=
  rfl

section Finite

variable [Fintype Q]

/-- Scalar-copy string modules are finite-dimensional when the coefficient
space is finite-dimensional. -/
theorem scalarRightLinearModule_isFiniteDimensional
    (C : Word R) (hmono : IsMonomial R) (V : FGModuleCat.{u} k) :
    MagnitudeConjecture.CoveringHom.IsFiniteDimensionalModule
      (C := (Category R)ᵒᵖ) k
      (C.scalarRightLinearModule hmono V.obj) := by
  constructor
  · rintro ⟨⟨x⟩⟩
    change FiniteDimensional k (TensorProduct k (C.Space x) V)
    infer_instance
  · letI : Fintype ((Category R)ᵒᵖ) :=
      Fintype.ofEquiv (Category R) Opposite.equivToOpposite
    exact Set.toFinite _

/-- The scalar-copy string module bundled in the finite-dimensional module
category. -/
def scalarFiniteRightModule (C : Word R) (hmono : IsMonomial R)
    (V : FGModuleCat.{u} k) :
    MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k :=
  ⟨C.scalarRightLinearModule hmono V.obj,
    C.scalarRightLinearModule_isFiniteDimensional hmono V⟩

/-- The finite-dimensional restriction of Butler--Ringel's embedding
functor. -/
def finiteStringEmbeddingFunctor (C : Word R) (hmono : IsMonomial R) :
    FGModuleCat.{u} k ⥤
      MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category R)ᵒᵖ) k where
  obj V := C.scalarFiniteRightModule hmono V
  map {V W} f := ⟨(C.stringEmbeddingFunctor hmono).map f.hom⟩
  map_id V := by
    apply ObjectProperty.hom_ext
    exact (C.stringEmbeddingFunctor hmono).map_id V.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (C.stringEmbeddingFunctor hmono).map_comp f.hom g.hom

instance finiteStringEmbeddingFunctor_additive
    (C : Word R) (hmono : IsMonomial R) :
    (C.finiteStringEmbeddingFunctor hmono).Additive where
  map_add {V W} f g := by
    apply ObjectProperty.hom_ext
    exact Functor.map_add (C.stringEmbeddingFunctor hmono)
      (f := f.hom) (g := g.hom)

instance finiteStringEmbeddingFunctor_linear
    (C : Word R) (hmono : IsMonomial R) :
    (C.finiteStringEmbeddingFunctor hmono).Linear k where
  map_smul {V W} f r := by
    apply ObjectProperty.hom_ext
    exact Functor.map_smul (C.stringEmbeddingFunctor hmono) r f.hom

/-- On the one-dimensional coefficient space, the finite embedding functor
recovers the literal finite string module. -/
def scalarFiniteRightModuleUnitIso (C : Word R) (hmono : IsMonomial R) :
    C.scalarFiniteRightModule hmono (FGModuleCat.of k k) ≅
      C.finiteRightModule hmono :=
  ObjectProperty.isoMk
    (MagnitudeConjecture.CoveringHom.IsFiniteDimensionalModule
      (C := (Category R)ᵒᵖ) k)
    (C.scalarRightLinearModuleUnitIso hmono)

end Finite

end MagnitudeConjecture.BoundQuiver.StringWord.Word
