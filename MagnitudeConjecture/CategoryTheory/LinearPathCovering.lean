import MagnitudeConjecture.CategoryTheory.LinearCovering
import MagnitudeConjecture.CategoryTheory.LinearPathLift
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Coverings of free linear path categories

A quiver prefunctor induces a linear functor between the corresponding free
linear path categories.  This file identifies the path bases occurring in the
two direct-sum Hom maps of a categorical covering.  The fixed-starting-point
half uses Mathlib's path-star lifting; the fixed-terminal-point half uses the
dual path-costar lifting established in `QuiverPathCostar`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.LinearPathCategory

universe u v₁ v₂ w₁ w₂

variable {k : Type u} [Field k]
variable {Q₁ : Type v₁} [Quiver.{w₁} Q₁]
variable {Q₂ : Type v₂} [Quiver.{w₂} Q₂]

/-- The image of a reversed quiver arrow as a path-basis morphism in the
target free linear path category. -/
def prefunctorArrowHom (π : Q₁ ⥤q Q₂) {i j : Q₁} (a : i ⟶ j) :
    obj k Q₂ (π.obj j) ⟶ obj k Q₂ (π.obj i) :=
  pathHom (π.map a).toPath

set_option backward.isDefEq.respectTransparency false in
/-- Mapping a source path under the reversed free realization gives the
path-basis morphism of its mapped path. -/
theorem pathMap_prefunctorArrowHom (π : Q₁ ⥤q Q₂)
    {i j : Q₁} (p : Quiver.Path i j) :
    pathMap (fun x ↦ obj k Q₂ (π.obj x))
        (fun {_ _} a ↦ prefunctorArrowHom (k := k) π a) p =
      pathHom (π.mapPath p) := by
  induction p with
  | nil =>
      rw [pathMap_nil, Prefunctor.mapPath_nil]
      exact (pathHom_nil (obj k Q₂ (π.obj i))).symm
  | cons p a ih =>
      rw [pathMap_cons, ih, prefunctorArrowHom,
        pathHom_comp, Prefunctor.mapPath_cons]
      rfl

/-- The linear functor on free path categories induced by a quiver
prefunctor. -/
def prefunctorFunctor (π : Q₁ ⥤q Q₂) :
    Category k Q₁ ⥤ Category k Q₂ :=
  lift (fun x ↦ obj k Q₂ (π.obj x))
    (fun {_ _} a ↦ prefunctorArrowHom (k := k) π a)

noncomputable instance prefunctorFunctor_additive (π : Q₁ ⥤q Q₂) :
    (prefunctorFunctor (k := k) π).Additive := by
  dsimp only [prefunctorFunctor]
  infer_instance

noncomputable instance prefunctorFunctor_linear (π : Q₁ ⥤q Q₂) :
    (prefunctorFunctor (k := k) π).Linear k := by
  dsimp only [prefunctorFunctor]
  infer_instance

@[simp]
theorem prefunctorFunctor_obj (π : Q₁ ⥤q Q₂) (x : Q₁) :
    (prefunctorFunctor (k := k) π).obj (obj k Q₁ x) =
      obj k Q₂ (π.obj x) :=
  rfl

@[simp]
theorem vertex_prefunctorFunctor_obj (π : Q₁ ⥤q Q₂) (x : Q₁) :
    vertex ((prefunctorFunctor (k := k) π).obj (obj k Q₁ x)) =
      π.obj x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem prefunctorFunctor_map_pathHom (π : Q₁ ⥤q Q₂)
    {i j : Q₁} (p : Quiver.Path i j) :
    (prefunctorFunctor (k := k) π).map (pathHom p) =
      pathHom (π.mapPath p) := by
  change (lift (k := k) (fun x ↦ obj k Q₂ (π.obj x))
      (fun {_ _} a ↦ prefunctorArrowHom (k := k) π a)).map
        (pathHom p) = _
  rw [lift_map_pathHom, pathMap_prefunctorArrowHom]

/-- Path-basis indices with fixed lifted terminal vertex and varying initial
vertex over `y` map to paths downstairs. -/
def targetPathMap (π : Q₁ ⥤q Q₂) (x : Q₁) (y : Q₂) :
    (Σ Z : {z : Q₁ // π.obj z = y}, Quiver.Path Z.1 x) →
      Quiver.Path y (π.obj x) :=
  fun Zp ↦ (π.mapPath Zp.2).cast Zp.1.2 rfl

/-- Path-basis indices with fixed lifted initial vertex and varying terminal
vertex over `x` map to paths downstairs. -/
def sourcePathMap (π : Q₁ ⥤q Q₂) (x : Q₂) (y : Q₁) :
    (Σ Z : {z : Q₁ // π.obj z = x}, Quiver.Path y Z.1) →
      Quiver.Path (π.obj y) x :=
  fun Zp ↦ (π.mapPath Zp.2).cast rfl Zp.1.2

theorem targetPathMap_bijective (π : Q₁ ⥤q Q₂)
    (hπ : π.IsCovering) (x : Q₁) (y : Q₂) :
    Function.Bijective (targetPathMap π x y) := by
  constructor
  · rintro ⟨⟨z, hz⟩, p⟩ ⟨⟨z', hz'⟩, p'⟩ h
    have hpath : HEq (π.mapPath p) (π.mapPath p') :=
      (Quiver.Path.cast_heq hz rfl (π.mapPath p)).symm.trans
        ((heq_of_eq h).trans
          (Quiver.Path.cast_heq hz' rfl (π.mapPath p')))
    have hcostar : π.pathCostar x ⟨z, p⟩ = π.pathCostar x ⟨z', p'⟩ :=
      Sigma.ext (hz.trans hz'.symm) hpath
    cases (hπ.pathCostar_bijective x).1 hcostar
    rfl
  · intro q
    obtain ⟨⟨z, p⟩, hp⟩ :=
      (hπ.pathCostar_bijective x).2
        (show Quiver.PathCostar (π.obj x) from ⟨y, q⟩)
    have hz : π.obj z = y := congrArg Sigma.fst hp
    have hpath : HEq (π.mapPath p) q := by
      exact (Sigma.ext_iff.mp hp).2
    refine ⟨⟨⟨z, hz⟩, p⟩, ?_⟩
    exact (Quiver.Path.cast_eq_iff_heq hz rfl _ _).2 hpath

theorem sourcePathMap_bijective (π : Q₁ ⥤q Q₂)
    (hπ : π.IsCovering) (x : Q₂) (y : Q₁) :
    Function.Bijective (sourcePathMap π x y) := by
  constructor
  · rintro ⟨⟨z, hz⟩, p⟩ ⟨⟨z', hz'⟩, p'⟩ h
    have hpath : HEq (π.mapPath p) (π.mapPath p') :=
      (Quiver.Path.cast_heq rfl hz (π.mapPath p)).symm.trans
        ((heq_of_eq h).trans
          (Quiver.Path.cast_heq rfl hz' (π.mapPath p')))
    have hstar : π.pathStar y ⟨z, p⟩ = π.pathStar y ⟨z', p'⟩ :=
      Sigma.ext (hz.trans hz'.symm) hpath
    cases (hπ.pathStar_bijective y).1 hstar
    rfl
  · intro q
    obtain ⟨⟨z, p⟩, hp⟩ :=
      (hπ.pathStar_bijective y).2
        (show Quiver.PathStar (π.obj y) from ⟨x, q⟩)
    have hz : π.obj z = x := congrArg Sigma.fst hp
    have hpath : HEq (π.mapPath p) q := by
      exact (Sigma.ext_iff.mp hp).2
    refine ⟨⟨⟨z, hz⟩, p⟩, ?_⟩
    exact (Quiver.Path.cast_eq_iff_heq rfl hz _ _).2 hpath

/-- The fixed-terminal path index equivalence of a quiver covering. -/
def targetPathEquiv (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering)
    (x : Q₁) (y : Q₂) :
    (Σ Z : {z : Q₁ // π.obj z = y}, Quiver.Path Z.1 x) ≃
      Quiver.Path y (π.obj x) :=
  Equiv.ofBijective (targetPathMap π x y)
    (targetPathMap_bijective π hπ x y)

/-- The fixed-initial path index equivalence of a quiver covering. -/
def sourcePathEquiv (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering)
    (x : Q₂) (y : Q₁) :
    (Σ Z : {z : Q₁ // π.obj z = x}, Quiver.Path y Z.1) ≃
      Quiver.Path (π.obj y) x :=
  Equiv.ofBijective (sourcePathMap π x y)
    (sourcePathMap_bijective π hπ x y)

@[simp]
theorem targetPathEquiv_apply (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering)
    (x : Q₁) (y : Q₂)
    (p : Σ Z : {z : Q₁ // π.obj z = y}, Quiver.Path Z.1 x) :
    targetPathEquiv π hπ x y p = targetPathMap π x y p :=
  rfl

@[simp]
theorem sourcePathEquiv_apply (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering)
    (x : Q₂) (y : Q₁)
    (p : Σ Z : {z : Q₁ // π.obj z = x}, Quiver.Path y Z.1) :
    sourcePathEquiv π hπ x y p = sourcePathMap π x y p :=
  rfl

/-- A basis assembled on a dependent direct sum evaluates by including the
corresponding component basis vector. -/
theorem dfinsuppBasis_apply
    {ι : Type*} {M : ι → Type*} [DecidableEq ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    {η : ι → Type*} (b : ∀ i, Module.Basis (η i) k (M i))
    (i : ι) (j : η i) :
    DFinsupp.basis b ⟨i, j⟩ = DirectSum.lof k ι M i (b i j) := by
  apply (DFinsupp.basis b).repr.injective
  rw [Module.Basis.repr_self]
  simp only [DFinsupp.basis, LinearEquiv.trans_apply]
  ext q
  change (Finsupp.single ⟨i, j⟩ 1) q =
    ((sigmaFinsuppEquivDFinsupp.symm
      (DFinsupp.mapRange (fun i x ↦ (b i).repr x)
        (fun i ↦ (b i).repr.map_zero)
        (DFinsupp.single i (b i j)))) q)
  rw [sigmaFinsuppEquivDFinsupp_symm_apply, DFinsupp.mapRange_apply,
    DFinsupp.single_apply]
  rcases q with ⟨q, r⟩
  by_cases hi : i = q
  · subst q
    by_cases hj : j = r
    · subst r
      simp
    · simp [hj]
  · simp [hi]

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing a represented reversed path by an object equality casts
the initial vertex of the path. -/
theorem pathHom_comp_eqToHom_eq_cast_start
    {i i' j : Q₂} (p : Quiver.Path i j) (h : i = i') :
    pathHom p ≫ eqToHom (congrArg (obj k Q₂) h) =
      pathHom (p.cast h rfl) := by
  subst i'
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing a represented reversed path by an object equality casts the
terminal vertex of the path. -/
theorem eqToHom_comp_pathHom_eq_cast_end
    {i j j' : Q₂} (p : Quiver.Path i j) (h : j = j') :
    eqToHom (congrArg (obj k Q₂) h).symm ≫ pathHom p =
      pathHom (p.cast rfl h) := by
  subst j'
  simp

set_option backward.isDefEq.respectTransparency false in
/-- A represented path equals its endpoint cast preceded by the corresponding
object equality. -/
theorem pathHom_eq_eqToHom_comp_cast_end
    {i j j' : Q₂} (p : Quiver.Path i j) (h : j = j') :
    pathHom p = eqToHom (congrArg (obj k Q₂) h) ≫
      pathHom (p.cast rfl h) := by
  subst j'
  simp

/-- The fibre of the free path functor is the corresponding fibre of the
underlying quiver map. -/
def functorFiberVertexEquiv (π : Q₁ ⥤q Q₂) (y : Q₂) :
    MagnitudeConjecture.LinearCovering.Fiber
        (prefunctorFunctor (k := k) π) (obj k Q₂ y) ≃
      {z : Q₁ // π.obj z = y} where
  toFun Z := ⟨vertex Z.1, congrArg vertex Z.2⟩
  invFun z := ⟨obj k Q₁ z.1, congrArg (obj k Q₂) z.2⟩
  left_inv Z := by
    rcases Z with ⟨Z, hZ⟩
    rfl
  right_inv z := by
    rcases z with ⟨z, hz⟩
    rfl

/-- Path indices expressed through categorical fibres are equivalent to the
fixed-terminal paths downstairs. -/
def targetFunctorPathEquiv (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering)
    (x : Q₁) (y : Q₂) :
    (Σ Z : MagnitudeConjecture.LinearCovering.Fiber
        (prefunctorFunctor (k := k) π) (obj k Q₂ y),
      Quiver.Path (vertex Z.1) x) ≃
      Quiver.Path y (π.obj x) :=
  (Equiv.sigmaCongr (functorFiberVertexEquiv (k := k) π y)
      (fun _ ↦ Equiv.refl _)).trans
    (targetPathEquiv π hπ x y)

/-- Path indices expressed through categorical fibres are equivalent to the
fixed-initial paths downstairs. -/
def sourceFunctorPathEquiv (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering)
    (x : Q₂) (y : Q₁) :
    (Σ Z : MagnitudeConjecture.LinearCovering.Fiber
        (prefunctorFunctor (k := k) π) (obj k Q₂ x),
      Quiver.Path y (vertex Z.1)) ≃
      Quiver.Path (π.obj y) x :=
  (Equiv.sigmaCongr (functorFiberVertexEquiv (k := k) π x)
      (fun _ ↦ Equiv.refl _)).trans
    (sourcePathEquiv π hπ x y)

/-- The path basis on the fixed-source, varying-target direct sum. -/
def targetFiberHomBasis (π : Q₁ ⥤q Q₂) (x : Q₁) (y : Q₂) :
    Module.Basis
      (Σ Z : MagnitudeConjecture.LinearCovering.Fiber
          (prefunctorFunctor (k := k) π) (obj k Q₂ y),
        Quiver.Path (vertex Z.1) x)
      k
      (DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (prefunctorFunctor (k := k) π) (obj k Q₂ y))
        (fun Z ↦ obj k Q₁ x ⟶ Z.1)) :=
  DFinsupp.basis fun Z ↦ homPathBasis (obj k Q₁ x) Z.1

/-- The path basis on the fixed-target, varying-source direct sum. -/
def sourceFiberHomBasis (π : Q₁ ⥤q Q₂) (x : Q₂) (y : Q₁) :
    Module.Basis
      (Σ Z : MagnitudeConjecture.LinearCovering.Fiber
          (prefunctorFunctor (k := k) π) (obj k Q₂ x),
        Quiver.Path y (vertex Z.1))
      k
      (DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (prefunctorFunctor (k := k) π) (obj k Q₂ x))
        (fun Z ↦ Z.1 ⟶ obj k Q₁ y)) :=
  DFinsupp.basis fun Z ↦ homPathBasis Z.1 (obj k Q₁ y)

theorem targetFiberHomBasis_apply (π : Q₁ ⥤q Q₂)
    (x : Q₁) (y : Q₂)
    (Z : MagnitudeConjecture.LinearCovering.Fiber
      (prefunctorFunctor (k := k) π) (obj k Q₂ y))
    (p : Quiver.Path (vertex Z.1) x) :
    targetFiberHomBasis (k := k) π x y ⟨Z, p⟩ =
      MagnitudeConjecture.LinearCovering.targetFiberLof
        (k := k) (prefunctorFunctor (k := k) π)
        (obj k Q₁ x) (obj k Q₂ y) Z (pathHom p) := by
  classical
  unfold targetFiberHomBasis
  unfold MagnitudeConjecture.LinearCovering.targetFiberLof
  rw [← homPathBasis_apply (k := k) (Q := Q₁)
    (obj k Q₁ x) Z.1 p]
  exact dfinsuppBasis_apply (k := k)
    (ι := MagnitudeConjecture.LinearCovering.Fiber
      (prefunctorFunctor (k := k) π) (obj k Q₂ y))
    (M := fun Z ↦ obj k Q₁ x ⟶ Z.1)
    (η := fun Z ↦ Quiver.Path (vertex Z.1) x)
    (fun Z ↦ homPathBasis (obj k Q₁ x) Z.1) Z p

theorem sourceFiberHomBasis_apply (π : Q₁ ⥤q Q₂)
    (x : Q₂) (y : Q₁)
    (Z : MagnitudeConjecture.LinearCovering.Fiber
      (prefunctorFunctor (k := k) π) (obj k Q₂ x))
    (p : Quiver.Path y (vertex Z.1)) :
    sourceFiberHomBasis (k := k) π x y ⟨Z, p⟩ =
      MagnitudeConjecture.LinearCovering.sourceFiberLof
        (k := k) (prefunctorFunctor (k := k) π)
        (obj k Q₂ x) (obj k Q₁ y) Z (pathHom p) := by
  classical
  unfold sourceFiberHomBasis
  unfold MagnitudeConjecture.LinearCovering.sourceFiberLof
  rw [← homPathBasis_apply (k := k) (Q := Q₁)
    Z.1 (obj k Q₁ y) p]
  exact dfinsuppBasis_apply (k := k)
    (ι := MagnitudeConjecture.LinearCovering.Fiber
      (prefunctorFunctor (k := k) π) (obj k Q₂ x))
    (M := fun Z ↦ Z.1 ⟶ obj k Q₁ y)
    (η := fun Z ↦ Quiver.Path y (vertex Z.1))
    (fun Z ↦ homPathBasis Z.1 (obj k Q₁ y)) Z p

/-- The basis equivalence underlying the fixed-source covering map for a
quiver covering. -/
def targetFiberHomBasisEquiv (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering)
    (x : Q₁) (y : Q₂) :
    DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (prefunctorFunctor (k := k) π) (obj k Q₂ y))
        (fun Z ↦ obj k Q₁ x ⟶ Z.1) ≃ₗ[k]
      ((prefunctorFunctor (k := k) π).obj (obj k Q₁ x) ⟶
        obj k Q₂ y) :=
  (targetFiberHomBasis (k := k) π x y).equiv
    (homPathBasis
      ((prefunctorFunctor (k := k) π).obj (obj k Q₁ x))
      (obj k Q₂ y))
    (targetFunctorPathEquiv (k := k) π hπ x y)

/-- The basis equivalence underlying the fixed-target covering map for a
quiver covering. -/
def sourceFiberHomBasisEquiv (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering)
    (x : Q₂) (y : Q₁) :
    DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (prefunctorFunctor (k := k) π) (obj k Q₂ x))
        (fun Z ↦ Z.1 ⟶ obj k Q₁ y) ≃ₗ[k]
      (obj k Q₂ x ⟶
        (prefunctorFunctor (k := k) π).obj (obj k Q₁ y)) :=
  (sourceFiberHomBasis (k := k) π x y).equiv
    (homPathBasis
      (obj k Q₂ x)
      ((prefunctorFunctor (k := k) π).obj (obj k Q₁ y)))
    (sourceFunctorPathEquiv (k := k) π hπ x y)

set_option backward.isDefEq.respectTransparency false in
theorem targetFiberHomBasisEquiv_eq_map
    (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering) (x : Q₁) (y : Q₂) :
    (targetFiberHomBasisEquiv (k := k) π hπ x y).toLinearMap =
      MagnitudeConjecture.LinearCovering.targetFiberHomMap
        (k := k) (prefunctorFunctor (k := k) π)
        (obj k Q₁ x) (obj k Q₂ y) := by
  apply (targetFiberHomBasis (k := k) π x y).ext
  rintro ⟨Z, p⟩
  change ((targetFiberHomBasis (k := k) π x y).equiv
      (homPathBasis (obj k Q₂ (π.obj x)) (obj k Q₂ y))
      (targetFunctorPathEquiv (k := k) π hπ x y))
        ((targetFiberHomBasis (k := k) π x y) ⟨Z, p⟩) = _
  rw [Module.Basis.equiv_apply]
  rw [targetFiberHomBasis_apply,
    MagnitudeConjecture.LinearCovering.targetFiberHomMap_lof,
    prefunctorFunctor_map_pathHom,
    pathHom_comp_eqToHom_eq_cast_start (k := k) (Q₂ := Q₂)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sourceFiberHomBasisEquiv_eq_map
    (π : Q₁ ⥤q Q₂) (hπ : π.IsCovering) (x : Q₂) (y : Q₁) :
    (sourceFiberHomBasisEquiv (k := k) π hπ x y).toLinearMap =
      MagnitudeConjecture.LinearCovering.sourceFiberHomMap
        (k := k) (prefunctorFunctor (k := k) π)
        (obj k Q₂ x) (obj k Q₁ y) := by
  apply (sourceFiberHomBasis (k := k) π x y).ext
  rintro ⟨Z, p⟩
  change ((sourceFiberHomBasis (k := k) π x y).equiv
      (homPathBasis (obj k Q₂ x) (obj k Q₂ (π.obj y)))
      (sourceFunctorPathEquiv (k := k) π hπ x y))
        ((sourceFiberHomBasis (k := k) π x y) ⟨Z, p⟩) = _
  rw [Module.Basis.equiv_apply]
  rw [sourceFiberHomBasis_apply,
    MagnitudeConjecture.LinearCovering.sourceFiberHomMap_lof,
    prefunctorFunctor_map_pathHom,
    eqToHom_comp_pathHom_eq_cast_end (k := k) (Q₂ := Q₂)]
  rfl

/-- A quiver covering induces a covering functor between its free linear path
categories. -/
theorem prefunctorFunctor_isCovering (π : Q₁ ⥤q Q₂)
    (hπ : π.IsCovering) :
    MagnitudeConjecture.LinearCovering.IsCovering
      (k := k) (prefunctorFunctor (k := k) π) := by
  constructor
  · intro X Y
    change Function.Bijective
      (MagnitudeConjecture.LinearCovering.targetFiberHomMap
        (k := k) (prefunctorFunctor (k := k) π)
        (obj k Q₁ (vertex X)) (obj k Q₂ (vertex Y)))
    rw [← targetFiberHomBasisEquiv_eq_map
      (k := k) π hπ (vertex X) (vertex Y)]
    exact (targetFiberHomBasisEquiv (k := k) π hπ
      (vertex X) (vertex Y)).bijective
  · intro X Y
    change Function.Bijective
      (MagnitudeConjecture.LinearCovering.sourceFiberHomMap
        (k := k) (prefunctorFunctor (k := k) π)
        (obj k Q₂ (vertex X)) (obj k Q₁ (vertex Y)))
    rw [← sourceFiberHomBasisEquiv_eq_map
      (k := k) π hπ (vertex X) (vertex Y)]
    exact (sourceFiberHomBasisEquiv (k := k) π hπ
      (vertex X) (vertex Y)).bijective

end MagnitudeConjecture.LinearPathCategory
