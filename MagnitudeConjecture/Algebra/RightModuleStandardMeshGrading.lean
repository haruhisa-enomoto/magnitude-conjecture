import MagnitudeConjecture.CategoryTheory.StandardMeshGrading
import MagnitudeConjecture.CategoryTheory.IrreducibleRadicalSquare
import MagnitudeConjecture.Algebra.RightModulePrimitiveGrading

/-!
# The standard mesh grading after deleting indecomposables

This file isolates the homogeneous-ideal step in Proposition 3.7 of the
frozen manuscript.  A standard mesh presentation grades the ambient skeleton
by path length.  The ideal of maps factoring through the deleted additive
subcategory is then proved homogeneous, so the literal factor category
inherits that grading.

The proof expands a factorization through a finite biproduct of deleted
indecomposables and then expands both coordinate maps into their homogeneous
parts.  No alternative or legacy grading interface is retained.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable [quiver : Quiver.{0} (Fin S.n)]
variable [arrowFintype : ∀ x y : Fin S.n, Fintype (x ⟶ y)]
variable {T : @MeshCategory.RightMeshData (Fin S.n) quiver}

namespace StandardMeshPresentation

/-- The factor ideal in one ambient skeleton Hom space, regarded as a linear
submodule. -/
def factorIdealSubmodule (K : Set (Fin S.n)) (x y : Fin S.n) :
    Submodule k (S.ambientAddPoint x ⟶ S.ambientAddPoint y) where
  carrier := (S.factorThroughSelectedIdeal K).hom
    (S.ambientAddPoint x) (S.ambientAddPoint y)
  zero_mem' := (S.factorThroughSelectedIdeal K).hom _ _ |>.zero_mem
  add_mem' := fun hf hg ↦
    (S.factorThroughSelectedIdeal K).hom _ _ |>.add_mem hf hg
  smul_mem' := fun c _ hf ↦
    (S.factorThroughSelectedIdeal K).smul_mem c hf

/-- The manuscript's homogeneous-deleted-ideal assertion, stated directly
for the ambient path grading supplied by standardness. -/
def FactorIdealIsHomogeneous
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) : Prop :=
  ∀ x y,
    letI : DirectSum.Decomposition (H.component (T := T) x y) :=
      (H.component_isInternal (T := T) x y).chooseDecomposition
    DirectSum.SetLike.IsHomogeneous
      (H.component (T := T) x y) (factorIdealSubmodule K x y)

/-- The set of homogeneous morphisms in one ambient skeleton Hom space. -/
def homogeneousMorphismSet
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (x y : Fin S.n) : Set (S.ambientAddPoint x ⟶ S.ambientAddPoint y) :=
  {f | ∃ d, f ∈ H.component (T := T) x y d}

/-- The homogeneous morphisms span the whole ambient skeleton Hom space. -/
theorem span_homogeneousMorphismSet_eq_top
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (x y : Fin S.n) :
    Submodule.span k (H.homogeneousMorphismSet x y) = ⊤ := by
  apply top_unique
  rw [← (H.component_isInternal (T := T) x y).submodule_iSup_eq_top]
  apply iSup_le
  intro d f hf
  exact Submodule.subset_span ⟨d, hf⟩

/-- Homogeneous composites through one deleted indecomposable. -/
def homogeneousFactorGeneratorSet
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) (x y : Fin S.n) :
    Set (S.ambientAddPoint x ⟶ S.ambientAddPoint y) :=
  {f | ∃ (z : Fin S.n), z ∈ K ∧ ∃ (i j : ℕ)
      (left : S.ambientAddPoint x ⟶ S.ambientAddPoint z)
      (right : S.ambientAddPoint z ⟶ S.ambientAddPoint y),
      left ∈ H.component (T := T) x z i ∧
      right ∈ H.component (T := T) z y j ∧ left ≫ right = f}

/-- An arbitrary composite through one deleted indecomposable lies in the
span of homogeneous such composites. -/
theorem composite_mem_span_homogeneousFactorGeneratorSet
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) {x y z : Fin S.n} (hz : z ∈ K)
    (left : S.ambientAddPoint x ⟶ S.ambientAddPoint z)
    (right : S.ambientAddPoint z ⟶ S.ambientAddPoint y) :
    left ≫ right ∈
      Submodule.span k (H.homogeneousFactorGeneratorSet K x y) := by
  have hleft : left ∈ Submodule.span k (H.homogeneousMorphismSet x z) := by
    rw [H.span_homogeneousMorphismSet_eq_top]
    simp
  induction hleft using Submodule.span_induction with
  | mem left hleft =>
      obtain ⟨i, hi⟩ := hleft
      have hright : right ∈
          Submodule.span k (H.homogeneousMorphismSet z y) := by
        rw [H.span_homogeneousMorphismSet_eq_top]
        simp
      induction hright using Submodule.span_induction with
      | mem right hright =>
          obtain ⟨j, hj⟩ := hright
          apply Submodule.subset_span
          exact ⟨z, hz, i, j, left, right, hi, hj, rfl⟩
      | zero => simp
      | add right₁ right₂ _ _ h₁ h₂ =>
          simpa using Submodule.add_mem _ h₁ h₂
      | smul c right _ hright =>
          simpa using Submodule.smul_mem _ c hright
  | zero => simp
  | add left₁ left₂ _ _ h₁ h₂ =>
      simpa using Submodule.add_mem _ h₁ h₂
  | smul c left _ hleft =>
      simpa using Submodule.smul_mem _ c hleft

/-- Maps factoring through the deleted additive subcategory are exactly the
span of homogeneous composites through individual deleted indecomposables. -/
theorem factorIdealSubmodule_eq_span_homogeneousFactorGeneratorSet
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) (x y : Fin S.n) :
    factorIdealSubmodule (S := S) K x y =
      Submodule.span k (H.homogeneousFactorGeneratorSet K x y) := by
  classical
  apply le_antisymm
  · intro f hf
    change S.FactorsThroughSelected K f.hom at hf
    rcases hf with ⟨M, hM, left, right, hfactor⟩
    obtain ⟨P⟩ := hM
    letI : Fintype P.index := FintypeCat.fintype
    let F : P.index → RightModule.FinitelyGeneratedCategory A :=
      fun j ↦ S.almostSplitSkeleton.obj (P.label j)
    let leftComponent (j : P.index) :
        S.ambientAddPoint x ⟶ S.ambientAddPoint (P.label j) :=
      ObjectProperty.homMk
        (left ≫ P.iso.hom ≫ biproduct.π F j)
    let rightComponent (j : P.index) :
        S.ambientAddPoint (P.label j) ⟶ S.ambientAddPoint y :=
      ObjectProperty.homMk
        (biproduct.ι F j ≫ P.iso.inv ≫ right)
    have hcomponent (j : P.index) :
        leftComponent j ≫ rightComponent j ∈
          Submodule.span k (H.homogeneousFactorGeneratorSet K x y) :=
      H.composite_mem_span_homogeneousFactorGeneratorSet K
        (P.mem j) (leftComponent j) (rightComponent j)
    have hsum : ∑ j, leftComponent j ≫ rightComponent j ∈
        Submodule.span k (H.homogeneousFactorGeneratorSet K x y) :=
      Submodule.sum_mem _ (fun j _ ↦ hcomponent j)
    have hdecomp : left ≫ right =
        ∑ j : P.index,
          (left ≫ P.iso.hom ≫ biproduct.π F j) ≫
            biproduct.ι F j ≫ P.iso.inv ≫ right := by
      calc
        left ≫ right = left ≫ P.iso.hom ≫ P.iso.inv ≫ right := by
          simp
        _ = left ≫ P.iso.hom ≫
              (∑ j : P.index, biproduct.π F j ≫ biproduct.ι F j) ≫
                P.iso.inv ≫ right := by
          dsimp only [F]
          simp only [biproduct.total, Category.id_comp,
            Iso.hom_inv_id_assoc]
        _ = _ := by
          simp only [Preadditive.comp_sum, Preadditive.sum_comp,
            Category.assoc]
    have hsum_eq : ∑ j, leftComponent j ≫ rightComponent j = f := by
      have hcomponent_hom (j : P.index) :
          (leftComponent j ≫ rightComponent j).hom =
            (left ≫ P.iso.hom ≫ biproduct.π F j) ≫
              biproduct.ι F j ≫ P.iso.inv ≫ right := rfl
      let U := ObjectProperty.ι
        (S.almostSplitSkeleton.generated Set.univ).carrier
      apply U.map_injective
      rw [U.map_sum]
      change (∑ j : P.index,
        (leftComponent j ≫ rightComponent j).hom) = f.hom
      simp_rw [hcomponent_hom]
      exact hdecomp.symm.trans hfactor
    rw [← hsum_eq]
    exact hsum
  · apply Submodule.span_le.2
    intro f hf
    rcases hf with ⟨z, hz, i, j, left, right, hleft, hright, hfactor⟩
    change S.FactorsThroughSelected K f.hom
    refine ⟨S.fgObj z, S.almostSplitSkeleton.inAdd_obj hz,
      left.hom, right.hom, ?_⟩
    exact congrArg (fun q ↦ q.hom) hfactor

/-- Every generator in the homogeneous presentation of the deleted-object
ideal belongs to one ambient path-degree component. -/
theorem homogeneousFactorGeneratorSet_isHomogeneous
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) {x y : Fin S.n}
    {f : S.ambientAddPoint x ⟶ S.ambientAddPoint y}
    (hf : f ∈ H.homogeneousFactorGeneratorSet K x y) :
    ∃ d, f ∈ H.component (T := T) x y d := by
  rcases hf with
    ⟨z, hz, i, j, left, right, hleft, hright, hfactor⟩
  refine ⟨i + j, ?_⟩
  rw [← hfactor]
  exact H.comp_mem_component (T := T) hleft hright

/-- The ideal of maps factoring through any chosen additive closure of
deleted indecomposables is homogeneous for the standard mesh grading. -/
theorem factorIdealIsHomogeneous
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) : H.FactorIdealIsHomogeneous K := by
  intro x y
  letI : DirectSum.Decomposition (H.component (T := T) x y) :=
    (H.component_isInternal (T := T) x y).chooseDecomposition
  rw [H.factorIdealSubmodule_eq_span_homogeneousFactorGeneratorSet]
  exact MagnitudeConjecture.Graded.span_isHomogeneous_of_forall_mem_component
    (H.component (T := T) x y)
    (H.homogeneousFactorGeneratorSet K x y)
    (fun _ hf ↦ H.homogeneousFactorGeneratorSet_isHomogeneous K hf)

/-- The quotient map on a Hom space between two selected indecomposables. -/
def factorHomLinearMap (K : Set (Fin S.n)) (x y : Fin S.n) :
    (S.ambientAddPoint x ⟶ S.ambientAddPoint y) →ₗ[k]
      ((S.factorFunctor K).obj (S.ambientAddPoint x) ⟶
        (S.factorFunctor K).obj (S.ambientAddPoint y)) :=
  (S.factorFunctor K).mapLinearMap k

omit quiver arrowFintype in
theorem ker_factorHomLinearMap (K : Set (Fin S.n)) (x y : Fin S.n) :
    LinearMap.ker (factorHomLinearMap (S := S) K x y) =
      factorIdealSubmodule (S := S) K x y := by
  ext f
  change (S.factorFunctor K).map f = 0 ↔
    f ∈ (S.factorThroughSelectedIdeal K).hom
      (S.ambientAddPoint x) (S.ambientAddPoint y)
  exact (S.factorThroughSelectedIdeal K).map_eq_zero_iff f

/-- The degree-`d` component in the literal factor Hom space. -/
def factorComponent
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) (x y : S.SurvivingLabel K) (d : ℕ) :
    Submodule k (S.factorObject K x ⟶ S.factorObject K y) :=
  (H.component (T := T) x.1 y.1 d).map
    (factorHomLinearMap (S := S) K x.1 y.1)

/-- The morphism represented in the literal factor by one quiver path.  The
quiver orientation is opposite to categorical composition: a path `y ⟶ x`
represents a morphism from the object at `x` to the object at `y`. -/
def factorPathHom
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) {x y : Fin S.n} (p : Quiver.Path y x) :
    (S.factorFunctor K).obj (S.ambientAddPoint x) ⟶
      (S.factorFunctor K).obj (S.ambientAddPoint y) :=
  (S.factorFunctor K).map
    (H.homEquiv x y
      ((MeshCategory.quotientFunctor (k := k) T).map
        (LinearPathCategory.pathHom p)))

/-- A path of length `d` represents a degree-`d` morphism in the literal
factor. -/
theorem factorPathHom_mem_factorComponent
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) {x y : S.SurvivingLabel K}
    (p : Quiver.Path y.1 x.1) {d : ℕ} (hp : p.length = d) :
    H.factorPathHom K p ∈ H.factorComponent (T := T) K x y d := by
  refine ⟨H.homEquiv x.1 y.1
      ((MeshCategory.quotientFunctor (k := k) T).map
        (LinearPathCategory.pathHom p)), ?_, rfl⟩
  refine ⟨(MeshCategory.quotientFunctor (k := k) T).map
      (LinearPathCategory.pathHom p), ?_, rfl⟩
  refine ⟨LinearPathCategory.pathHom p, ?_, rfl⟩
  exact (LinearPathCategory.pathHom_mem_lengthComponent_iff p d).2 hp

/-- Concatenation of paths becomes categorical composition in the literal
factor. -/
theorem factorPathHom_comp
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) {x y z : Fin S.n}
    (p : Quiver.Path y x) (q : Quiver.Path z y) :
    H.factorPathHom K (q.comp p) =
      H.factorPathHom K p ≫ H.factorPathHom K q := by
  let X := LinearPathCategory.obj k (Fin S.n) x
  let Y := LinearPathCategory.obj k (Fin S.n) y
  let Z := LinearPathCategory.obj k (Fin S.n) z
  let fp : X ⟶ Y := LinearPathCategory.pathHom p
  let fq : Y ⟶ Z := LinearPathCategory.pathHom q
  let fr : X ⟶ Z := LinearPathCategory.pathHom (q.comp p)
  let QF := MeshCategory.quotientFunctor (k := k) T
  let F := S.factorFunctor K
  have hfree : fr = fp ≫ fq := by
    dsimp only [fr, fp, fq]
    exact (LinearPathCategory.pathHom_comp p q).symm
  have hmesh : QF.map fr = QF.map fp ≫ QF.map fq := by
    rw [hfree, QF.map_comp]
  change F.map (H.homEquiv x z (QF.map fr)) =
    F.map (H.homEquiv x y (QF.map fp)) ≫
      F.map (H.homEquiv y z (QF.map fq))
  rw [hmesh, H.map_comp, F.map_comp]

/-- A homogeneous deleted-object ideal gives an internal grading on every
factor Hom space between surviving skeleton objects. -/
theorem factorComponent_isInternal
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) (x y : S.SurvivingLabel K) :
    DirectSum.IsInternal (H.factorComponent K x y) := by
  letI : DirectSum.Decomposition (H.component (T := T) x.1 y.1) :=
    (H.component_isInternal (T := T) x.1 y.1).chooseDecomposition
  apply MagnitudeConjecture.Graded.image_isInternal_of_surjective_of_ker_isHomogeneous
    (H.component (T := T) x.1 y.1)
    (factorHomLinearMap (S := S) K x.1 y.1)
    (S.factorFunctor K).map_surjective
  rw [ker_factorHomLinearMap]
  exact H.factorIdealIsHomogeneous K x.1 y.1

/-- Composition in the factor grading adds path degrees. -/
theorem factor_comp_mem_component
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) {x y z : S.SurvivingLabel K} {i j : ℕ}
    {f : S.factorObject K x ⟶ S.factorObject K y}
    {g : S.factorObject K y ⟶ S.factorObject K z}
    (hf : f ∈ H.factorComponent (T := T) K x y i)
    (hg : g ∈ H.factorComponent (T := T) K y z j) :
    f ≫ g ∈ H.factorComponent (T := T) K x z (i + j) := by
  rcases hf with ⟨f, hf, rfl⟩
  rcases hg with ⟨g, hg, rfl⟩
  refine ⟨f ≫ g, H.comp_mem_component (T := T) hf hg, ?_⟩
  exact (S.factorFunctor K).map_comp f g

/-- Identities of surviving factor objects have degree zero. -/
theorem factor_id_mem_component_zero
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    𝟙 (S.factorObject K x) ∈ H.factorComponent (T := T) K x x 0 := by
  refine ⟨𝟙 (S.ambientAddPoint x.1),
    H.id_mem_component_zero (T := T) x.1, ?_⟩
  exact (S.factorFunctor K).map_id (S.ambientAddPoint x.1)

/-- Every positive-degree homogeneous morphism between surviving factor
indecomposables belongs to the categorical radical. -/
theorem factorComponent_mem_radical_of_pos [IsAlgClosed k]
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (Hdir : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) {x y : S.SurvivingLabel K} {d : ℕ}
    {f : S.factorObject K x ⟶ S.factorObject K y}
    (hf : f ∈ H.factorComponent (T := T) K x y d) (hd : 0 < d) :
    f ∈ (S.factorFiniteTauCategoryData K).radical.ideal.hom
      (S.factorObject K x) (S.factorObject K y) := by
  by_cases hxy : x = y
  · subst y
    obtain ⟨c, hc⟩ := Hdir.factorObject_endomorphism_eq_smul_id S K x f
    have hfzero : f ∈ H.factorComponent (T := T) K x x 0 := by
      rw [← hc]
      exact Submodule.smul_mem _ c (H.factor_id_mem_component_zero K x)
    have hdisj : Disjoint
        (H.factorComponent (T := T) K x x d)
        (H.factorComponent (T := T) K x x 0) :=
      (H.factorComponent_isInternal K x x).submodule_iSupIndep.pairwiseDisjoint
        hd.ne'
    have hfbot : f ∈ (⊥ : Submodule k
        (S.factorObject K x ⟶ S.factorObject K x)) :=
      hdisj.le_bot ⟨hf, hfzero⟩
    have hzero : f = 0 := by simpa using hfbot
    rw [hzero]
    exact zero_mem _
  · exact S.factorHom_mem_radical_of_ne K hxy f

/-- Every represented path of length at least two belongs to the square of
the categorical radical in the literal factor.  If the first intermediate
vertex was deleted, the path factors through a zero object; otherwise its two
positive-length pieces are radical. -/
theorem factorPathHom_mem_radical_mul [IsAlgClosed k]
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (Hdir : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) {x y : S.SurvivingLabel K}
    (p : Quiver.Path y.1 x.1) (hp : 2 ≤ p.length) :
    H.factorPathHom K p ∈
      ((S.factorFiniteTauCategoryData K).radical.ideal ⋆ᵢ
        (S.factorFiniteTauCategoryData K).radical.ideal).hom
          (S.factorObject K x) (S.factorObject K y) := by
  have hlen : p.length = (p.length - 1) + 1 := by omega
  obtain ⟨m, a, q, hq, hpath⟩ :=
    Quiver.Path.eq_toPath_comp_of_length_eq_succ p hlen
  by_cases hm : m ∈ K
  · have hM := S.factorObject_isZero_of_mem K hm
    rw [hpath, H.factorPathHom_comp K q a.toPath,
      hM.eq_of_tgt (H.factorPathHom K q) 0,
      hM.eq_of_src (H.factorPathHom K a.toPath) 0, zero_comp]
    exact zero_mem _
  · let z : S.SurvivingLabel K := ⟨m, hm⟩
    have hqpos : 0 < q.length := by omega
    have hqcomp : H.factorPathHom K q ∈
        H.factorComponent (T := T) K x z q.length :=
      factorPathHom_mem_factorComponent (T := T) H K
        (x := x) (y := z) q (d := q.length) rfl
    have hqrad :=
      H.factorComponent_mem_radical_of_pos Hdir K hqcomp hqpos
    have hacomp : H.factorPathHom K a.toPath ∈
        H.factorComponent (T := T) K z y 1 :=
      factorPathHom_mem_factorComponent (T := T) H K
        (x := z) (y := y) a.toPath (d := 1) (by simp)
    have harad :=
      H.factorComponent_mem_radical_of_pos Hdir K hacomp Nat.zero_lt_one
    rw [hpath, H.factorPathHom_comp K q a.toPath]
    exact HomIdeal.comp_mem_mul hqrad harad

/-- Every morphism in a factor-category homogeneous component of degree at
least two lies in the square of the categorical radical. -/
theorem factorComponent_mem_radical_mul [IsAlgClosed k]
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (Hdir : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) {x y : S.SurvivingLabel K} {d : ℕ}
    {f : S.factorObject K x ⟶ S.factorObject K y}
    (hf : f ∈ H.factorComponent (T := T) K x y d) (hd : 2 ≤ d) :
    f ∈ ((S.factorFiniteTauCategoryData K).radical.ideal ⋆ᵢ
      (S.factorFiniteTauCategoryData K).radical.ideal).hom
        (S.factorObject K x) (S.factorObject K y) := by
  rcases hf with ⟨f, hf, rfl⟩
  rcases hf with ⟨f, hf, rfl⟩
  rcases hf with ⟨f, hf, rfl⟩
  rw [LinearPathCategory.lengthComponent_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨p, hp, rfl⟩
      apply H.factorPathHom_mem_radical_mul Hdir K p
      change p.length = d at hp
      exact hp.symm ▸ hd
  | zero =>
      simp
  | add f g _ _ hf hg =>
      simpa using add_mem hf hg
  | smul c f _ hf =>
      have hsmul :=
        ((S.factorFiniteTauCategoryData K).radical.ideal ⋆ᵢ
          (S.factorFiniteTauCategoryData K).radical.ideal).precomp
            (c • 𝟙 (S.factorObject K x)) hf
      simpa using hsmul

/-- Degree zero still vanishes between distinct surviving labels. -/
theorem factor_component_zero_eq_bot_of_ne
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T) (K : Set (Fin S.n))
    {x y : S.SurvivingLabel K} (hxy : x ≠ y) :
    H.factorComponent (T := T) K x y 0 = ⊥ := by
  have hxy' : x.1 ≠ y.1 := by
    intro h
    exact hxy (Subtype.ext h)
  rw [factorComponent, H.component_zero_eq_bot_of_ne (T := T) hxy']
  exact Submodule.map_bot _

/-- The path grading supplied by a standard mesh presentation descends to
the exact skeleton-grading interface consumed by the poset-space argument. -/
def factorSkeletonHomGrading
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (K : Set (Fin S.n)) :
    S.SkeletonHomGrading K where
  component := H.factorComponent (T := T) K
  isInternal := H.factorComponent_isInternal (T := T) K
  comp_mem := H.factor_comp_mem_component (T := T) K
  id_mem_zero := H.factor_id_mem_component_zero (T := T) K
  degreeZero_eq_bot_of_ne :=
    H.factor_component_zero_eq_bot_of_ne (T := T) K

/-- In the primitive-factor setting of the manuscript, every irreducible
morphism between surviving indecomposables has path degree one. -/
theorem irreducible_mem_factorComponent_one [IsAlgClosed k]
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (Hdir : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) {D : S.PrimitiveMultiplicityInput K}
    {P : Type u} [Fintype P] [PartialOrder P]
    (R : S.PrimitiveProjectivePosetData D P)
    (hsink : D.multiplicity D.sink.1 = 1)
    {x y : S.SurvivingLabel K}
    {f : S.factorObject K x ⟶ S.factorObject K y}
    (hfirr : IsIrreducibleMorphism f) :
    f ∈ H.factorComponent (T := T) K x y 1 := by
  let G := H.factorSkeletonHomGrading (T := T) K
  let Q := (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData
  have hfne : f ≠ 0 := by
    intro hf
    subst f
    exact (MagnitudeConjecture.FiniteTauMatrix.not_isIrreducibleMorphism_of_mem_radical_mul
      Q (zero_mem _)) hfirr
  have hfniso : ¬ IsIso f := by
    intro hf
    letI : IsIso f := hf
    exact hfirr.not_isSplitMono (inferInstance : IsSplitMono f)
  obtain ⟨d, hfd, hdlevel⟩ :=
    G.exists_degree_mem_and_objLevel_eq R Hdir hsink hfne
  have hlt := G.objLevel_lt_of_nonzero_not_isIso
    R Hdir hsink f hfne hfniso
  have hdpos : 0 < d := by
    rw [← hdlevel] at hlt
    omega
  by_cases hd : d = 1
  · subst d
    exact hfd
  · have hdlarge : 2 ≤ d := by omega
    have hsquare := H.factorComponent_mem_radical_mul Hdir K hfd hdlarge
    exact False.elim
      ((MagnitudeConjecture.FiniteTauMatrix.not_isIrreducibleMorphism_of_mem_radical_mul
        Q hsquare) hfirr)

end StandardMeshPresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
