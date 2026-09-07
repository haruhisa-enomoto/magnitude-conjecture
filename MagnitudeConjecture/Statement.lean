import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Morita.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Quotient.Preadditive
import Mathlib.CategoryTheory.Quotient.Linear
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Independent vocabulary for the magnitude theorem

These definitions use only Mathlib. They describe finite representation type,
the inverse Hom-matrix sum, simple modules, and special biserial presentations
in the Morita class. Connections to the proof library belong in separate modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ModuleCat.Algebra

namespace MagnitudeConjecture.Statement
universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- One representative of each finite-dimensional indecomposable right module.
Existence of such a family expresses finite representation type. -/
structure IndecomposableFamily where
  size : ℕ
  obj : Fin size → ModuleCat.{u} Aᵐᵒᵖ
  finite : ∀ i, Module.Finite k (obj i)
  indecomposable : ∀ i, Indecomposable (obj i)
  distinct : ∀ {i j}, Nonempty (obj i ≅ obj j) → i = j
  complete : ∀ M : ModuleCat.{u} Aᵐᵒᵖ,
    Module.Finite k M → Indecomposable M → ∃ i, Nonempty (M ≅ obj i)

/-- The Hom-dimension matrix, with rational coefficients. -/
def homMatrix (S : IndecomposableFamily k A) : Matrix (Fin S.size) (Fin S.size) ℚ :=
  fun i j => (Module.finrank k (S.obj i ⟶ S.obj j) : ℚ)

/-- The sum of the entries of the inverse Hom-dimension matrix.
Nonsingularity is asserted separately in the full statement below. -/
def magnitude (S : IndecomposableFamily k A) : ℚ :=
  ∑ i, ∑ j, (homMatrix k A S)⁻¹ i j

/-- The number of isomorphism classes of simple right modules, counted
inside the complete family; simplicity is Mathlib's module-theoretic notion. -/
def simpleCount (S : IndecomposableFamily k A) : ℕ :=
  Nat.card {i : Fin S.size // IsSimpleModule Aᵐᵒᵖ (S.obj i)}

end MagnitudeConjecture.Statement

namespace MagnitudeConjecture.Statement.QuiverPresentation
universe u
variable (k Q : Type u) [Field k] [Quiver.{u} Q]

/-- The representation freely generated at a vertex: its component at `j`
has a basis consisting of the paths from `i` to `j`. -/
def representable (i : Q) : Paths Q ⥤ ModuleCat k :=
  Paths.lift
    { obj := fun j ↦ ModuleCat.of k (Quiver.Path i j →₀ k)
      map := fun {a _} e ↦
        ModuleCat.ofHom (Finsupp.lmapDomain k k fun p : Quiver.Path i a ↦ p.cons e) }

/-- Paths act by concatenation on the free representation. -/
theorem representable_map_single (i : Q) {a b : Q}
    (p : Quiver.Path a b) (q : Quiver.Path i a) (c : k) :
    (representable k Q i).map p (Finsupp.single q c) =
      Finsupp.single (q.comp p) c := by
  induction p with
  | nil =>
      change (representable k Q i).map (𝟙 (show Paths Q from a)) _ = _
      rw [(representable k Q i).map_id, ModuleCat.id_apply]
      rfl
  | cons p e ih =>
      have hcons : (representable k Q i).map (p.cons e) =
          (representable k Q i).map p ≫ (representable k Q i).map e.toPath :=
        (representable k Q i).map_comp p e.toPath
      rw [hcons, ModuleCat.comp_apply, ih]
      rw [show (representable k Q i).map e.toPath =
        ModuleCat.ofHom (Finsupp.lmapDomain k k fun q ↦ q.cons e) from
          Paths.lift_toPath _ e]
      exact Finsupp.mapDomain_single

/-- The free linear path category, in the reversed orientation supplied by
covariant representables. Its objects are exactly the vertices of `Q`. -/
abbrev FreeCategory := InducedCategory _ (representable k Q)

/-- The coefficient vector of a morphism, obtained by evaluating at the
stationary path. -/
def coefficients {X Y : FreeCategory k Q} (f : X ⟶ Y) :
    Quiver.Path (show Q from Y) (show Q from X) →₀ k :=
  f.hom.app X (Finsupp.single Quiver.Path.nil 1)

/-- Prepending a path gives the corresponding morphism of representables. -/
def pathHom {x y : Q} (p : Quiver.Path x y) :
    (show FreeCategory k Q from y) ⟶ (show FreeCategory k Q from x) :=
  InducedCategory.homMk
    { app z := ModuleCat.ofHom (Finsupp.lmapDomain k k fun q : Quiver.Path y z ↦ p.comp q)
      naturality {a b} r := by
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro q c
        change (Finsupp.lmapDomain k k _)
            ((representable k Q y).map r (Finsupp.single q c)) =
          (representable k Q x).map r ((Finsupp.lmapDomain k k _) (Finsupp.single q c))
        simp only [representable_map_single, Finsupp.lmapDomain_apply,
          Finsupp.mapDomain_single, Quiver.Path.comp_assoc] }

section Ideal
variable {k Q}
variable (R : ∀ X Y : FreeCategory k Q, Set (X ⟶ Y))

/-- The two-sided linear ideal generated by the stated relations. -/
def ideal (X Y : FreeCategory k Q) : Submodule k (X ⟶ Y) :=
  Submodule.span k {f | ∃ (A B : FreeCategory k Q) (r : A ⟶ B), r ∈ R A B ∧
    ∃ (a : X ⟶ A) (b : B ⟶ Y), f = a ≫ r ≫ b}

/-- The generated ideal is closed under precomposition. -/
theorem precomp {X Y Z : FreeCategory k Q} (f : X ⟶ Y)
    {g : Y ⟶ Z} (hg : g ∈ ideal R Y Z) : f ≫ g ∈ ideal R X Z := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨A, B, r, hr, a, b, rfl⟩
      exact Submodule.subset_span ⟨A, B, r, hr, f ≫ a, b, by simp⟩
  | zero => simp
  | add g h _ _ hg hh => simpa using (ideal R X Z).add_mem hg hh
  | smul c g _ hg => simpa using (ideal R X Z).smul_mem c hg

/-- The generated ideal is closed under postcomposition. -/
theorem postcomp {X Y Z : FreeCategory k Q} {f : X ⟶ Y}
    (g : Y ⟶ Z) (hf : f ∈ ideal R X Y) : f ≫ g ∈ ideal R X Z := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨A, B, r, hr, a, b, rfl⟩
      exact Submodule.subset_span ⟨A, B, r, hr, a, b ≫ g, by simp⟩
  | zero => simp
  | add f h _ _ hf hh => simpa using (ideal R X Z).add_mem hf hh
  | smul c f _ hf => simpa using (ideal R X Z).smul_mem c hf

/-- Equality modulo the relation ideal. -/
def rel : HomRel (FreeCategory k Q) := fun {X Y} f g ↦ f - g ∈ ideal R X Y

instance : Congruence (rel R) where
  equivalence := {
    refl := fun f ↦ by simp [rel]
    symm := fun h ↦ by simpa [rel, neg_sub] using (ideal R _ _).neg_mem h
    trans := fun hfg hgh ↦ by simpa [rel] using (ideal R _ _).add_mem hfg hgh }
  comp_left := by
    intro X Y Z f g g' h
    simpa [rel] using precomp R f h
  comp_right := by
    intro X Y Z f f' g h
    simpa [rel] using postcomp R g h

/-- Addition respects equality modulo the generated ideal. -/
theorem add_compatible {X Y : FreeCategory k Q} (f₁ f₂ g₁ g₂ : X ⟶ Y)
    (hf : rel R f₁ f₂) (hg : rel R g₁ g₂) : rel R (f₁ + g₁) (f₂ + g₂) := by
  have h := (ideal R X Y).add_mem hf hg
  change (f₁ + g₁) - (f₂ + g₂) ∈ ideal R X Y
  convert h using 1
  abel

/-- The bound-quiver category obtained by imposing the relations. -/
abbrev QuotientCategory := CategoryTheory.Quotient (rel R)

instance : Preadditive (QuotientCategory R) :=
  CategoryTheory.Quotient.preadditive (rel R) (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦ add_compatible R f₁ f₂ g₁ g₂ hf hg)
instance : (CategoryTheory.Quotient.functor (rel R)).Additive :=
  CategoryTheory.Quotient.functor_additive (rel R) (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦ add_compatible R f₁ f₂ g₁ g₂ hf hg)
instance : Linear k (QuotientCategory R) :=
  CategoryTheory.Quotient.linear k (rel R) (fun c {_ _} f g h ↦ by
    simpa [rel, ← smul_sub] using (ideal R _ _).smul_mem c h)

/-- The image of a path in the relation quotient. -/
def pathMap {x y : Q} (p : Quiver.Path x y) :=
  (CategoryTheory.Quotient.functor (rel R)).map (pathHom k Q p)

end Ideal
section CategoryAlgebra
variable {k}
variable (C : Type u) [Category.{u} C] [Preadditive C] [Linear k C]

/-- Covariant linear modules over a linear category. -/
def IsLinearModule : ObjectProperty (C ⥤ ModuleCat.{u} k) :=
  fun M ↦ M.Additive ∧ M.Linear k
abbrev LinearModules := (IsLinearModule (k := k) C).FullSubcategory

/-- Finite-dimensional modules with finite object support. -/
def IsFiniteModule : ObjectProperty (LinearModules (k := k) C) :=
  fun M ↦ (∀ X : C, FiniteDimensional k (M.obj.obj X)) ∧
    {X : C | Nontrivial (M.obj.obj X)}.Finite
abbrev FiniteModules := (IsFiniteModule (k := k) C).FullSubcategory

variable [Fintype C] (h : ∀ X Y : C, FiniteDimensional k (X ⟶ Y))

/-- A covariant representable, as a finite-dimensional linear module. -/
def finiteRepresentable (X : C) : FiniteModules (k := k) C :=
  ⟨⟨(linearCoyoneda k C).obj (Opposite.op X), inferInstance, {
    map_smul f r := by
      apply ModuleCat.hom_ext
      ext g
      change g ≫ (r • f) = r • (g ≫ f)
      rw [Linear.comp_smul] }⟩, h X, Set.toFinite _⟩

/-- The category algebra is the endomorphism algebra of the direct sum of
its representable modules. The bicone records that finite direct sum by its
universal property, independently of any choice of a library construction. -/
structure CategoryAlgebra (B : Type u) [Ring B] [Algebra k B] where
  generator : Bicone (finiteRepresentable C h)
  isBilimit : generator.IsBilimit
  algebraEquiv : B ≃ₐ[k] End generator.pt

end CategoryAlgebra

variable {k Q}
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]

/-- An admissible bound-quiver presentation with the special-biserial arrow
bounds. The ideal conditions are exactly `J^N ⊆ I ⊆ J²`, where `J` is the
arrow ideal. Morphisms reverse path direction; both incoming and outgoing
conditions are imposed, so the convention is symmetric. -/
structure Presentation (B : Type u) [Ring B] [Algebra k B] where
  relations : ∀ X Y : FreeCategory k Q, Set (X ⟶ Y)
  no_short_relations : ∀ X Y (f : X ⟶ Y), f ∈ ideal relations X Y →
    ∀ p, p.length < 2 → coefficients k Q f p = 0
  long_paths_vanish : ∃ N : ℕ, 2 ≤ N ∧ ∀ {x y : Q} (p : Quiver.Path x y),
    N ≤ p.length → pathHom k Q p ∈ ideal relations y x
  finiteHom : ∀ X Y : QuotientCategory relations, FiniteDimensional k (X ⟶ Y)
  algebra :
    letI : Fintype (QuotientCategory relations) := Fintype.ofEquiv Q
      (CategoryTheory.Quotient.equiv (rel relations)).symm
    CategoryAlgebra (QuotientCategory relations) finiteHom B
  outgoing_le_two : ∀ x : Q, Nat.card (Σ y : Q, x ⟶ y) ≤ 2
  incoming_le_two : ∀ y : Q, Nat.card (Σ x : Q, x ⟶ y) ≤ 2
  successor_le_one : ∀ {x y : Q} (a : x ⟶ y),
    Nat.card {b : (Σ z : Q, y ⟶ z) //
      pathMap relations b.2.toPath ≫ pathMap relations a.toPath ≠ 0} ≤ 1
  predecessor_le_one : ∀ {x y : Q} (a : x ⟶ y),
    Nat.card {b : (Σ z : Q, z ⟶ x) //
      pathMap relations a.toPath ≫ pathMap relations b.2.toPath ≠ 0} ≤ 1

end MagnitudeConjecture.Statement.QuiverPresentation

namespace MagnitudeConjecture.Statement
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- A finite-dimensional special biserial algebra in the Morita class of A.
This includes nonbasic A and uses k-linear Morita equivalence. -/
structure SpecialBiserialModel where
  Carrier : Type u
  [ring : Ring Carrier]
  [algebra : Algebra k Carrier]
  [finiteDimensional : FiniteDimensional k Carrier]
  morita : MoritaEquivalence k A Carrier
  Vertex : Type u
  [vertices : Fintype Vertex]
  [quiver : Quiver.{u} Vertex]
  [arrows : ∀ i j : Vertex, Fintype (i ⟶ j)]
  presentation : QuiverPresentation.Presentation (k := k) (Q := Vertex) Carrier

/-- Special biseriality with the paper's convention for nonbasic algebras. -/
def IsSpecialBiserial : Prop := Nonempty (SpecialBiserialModel k A)

/-- The full magnitude assertion: for every complete finite indecomposable family,
the Hom matrix is invertible and magnitude is at least the simple count,
with equality exactly in the special biserial case.

This definition specifies the proposition; its proof is supplied separately. -/
def MainClaim [IsAlgClosed k] [FiniteDimensional k A] : Prop :=
  ∀ S : IndecomposableFamily k A,
    (homMatrix k A S).det ≠ 0 ∧
    (simpleCount k A S : ℚ) ≤ magnitude k A S ∧
    (magnitude k A S = (simpleCount k A S : ℚ) ↔ IsSpecialBiserial k A)

end MagnitudeConjecture.Statement
