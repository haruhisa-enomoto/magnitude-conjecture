import MagnitudeConjecture.CategoryTheory.AlmostSplitCommutativeSquare

/-! # Equal-height commutative squares identify the AR translate -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution QuotientSubmoduleEquidistribution.Iyama
namespace MagnitudeConjecture.FiniteTauMatrix
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- A square with orthogonal middle objects has a nonzero map from its
source to the first term of the chosen right mesh. -/
theorem exists_nonzero_rightMesh_map_of_square
    (T : FiniteRightTauCategoryData C Ind) {X V W Y : Ind}
    (a : T.obj X ⟶ T.obj V) (b : T.obj V ⟶ T.obj Y)
    (c : T.obj X ⟶ T.obj W) (d : T.obj W ⟶ T.obj Y)
    (ha : a ≠ 0) (hb : IsIrreducibleMorphism b) (hd : ¬ IsSplitEpi d)
    (hWV : ∀ f : T.obj W ⟶ T.obj V, f = 0) (hsquare : a ≫ b = c ≫ d) :
    ∃ f : T.obj X ⟶ (T.rightMesh (T.obj Y)).X₁, f ≠ 0 := by
  let R := T.rightMesh (T.obj Y)
  let e := T.rightTermIso (T.obj Y)
  let S : ShortComplex C := ShortComplex.mk R.f (R.g ≫ e.hom) (by simp [← Category.assoc])
  have hS : ShortComplex.IsWeakKernel S := by
    rw [ShortComplex.isWeakKernel_iff]
    intro Z f hf
    have hz : f ≫ R.g = 0 := by
      apply (cancel_mono e.hom).1
      simpa [S, Category.assoc] using hf
    exact (ShortComplex.isWeakKernel_iff R).mp (T.rightTau (T.obj Y)).minimalWeakKernel.1 f hz
  exact MagnitudeConjecture.CategoryTheory.exists_nonzero_weakKernel_map_of_square
    S hS (rightMesh_terminal_isRightAlmostSplit T Y) a b c d ha hb hd hWV hsquare

/-- The source of a square is the translate of its target when its middle
objects are distinct of equal height and translation lowers height by two. -/
theorem tauPlus_eq_source_of_height_square
    (T : FiniteTauCategoryData C Ind) (height : Ind → ℕ)
    (hh : ∀ {x y : Ind} (f : T.obj x ⟶ T.obj y), f ≠ 0 → ¬ IsIso f → height x < height y)
    (htau : ∀ z : T.Nonprojective, height z.1 = height (T.tauPlus z) + 2)
    {X V W Y : Ind} (hVW : V ≠ W) (heq : height V = height W)
    (hXY : height Y = height X + 2)
    (a : T.obj X ⟶ T.obj V) (b : T.obj V ⟶ T.obj Y)
    (c : T.obj X ⟶ T.obj W) (d : T.obj W ⟶ T.obj Y)
    (ha : a ≠ 0) (hb : IsIrreducibleMorphism b) (hd : ¬ IsSplitEpi d)
    (hsquare : a ≫ b = c ≫ d) :
    ∃ hn : ¬ T.IsProjective Y, T.tauPlus ⟨Y, hn⟩ = X := by
  classical
  have hWV : ∀ f : T.obj W ⟶ T.obj V, f = 0 := by
    intro f
    by_contra hf
    have hn : ¬ IsIso f := by
      intro hI
      let := hI
      exact hVW (T.obj_skeletal ⟨asIso f⟩).symm
    have hlt := hh f hf hn
    omega
  obtain ⟨g, hg⟩ := exists_nonzero_rightMesh_map_of_square T.toFiniteRightTauCategoryData
    a b c d ha hb hd hWV hsquare
  have hn : ¬ T.IsProjective Y := by
    intro hz
    exact hg (hz.eq_of_tgt g 0)
  let z : T.Nonprojective := ⟨Y, hn⟩
  let f := g ≫ (T.tauPlusIso z).hom
  have hf : f ≠ 0 := by
    intro hz
    apply hg
    apply (cancel_mono (T.tauPlusIso z).hom).1
    simpa [f] using hz
  refine ⟨hn, ?_⟩
  by_contra hne
  have hfn : ¬ IsIso f := by
    intro hI
    let := hI
    exact hne (T.obj_skeletal ⟨asIso f⟩).symm
  have hlt := hh f hf hfn
  have ht := htau z
  change height Y = height (T.tauPlus z) + 2 at ht
  omega

end MagnitudeConjecture.FiniteTauMatrix
