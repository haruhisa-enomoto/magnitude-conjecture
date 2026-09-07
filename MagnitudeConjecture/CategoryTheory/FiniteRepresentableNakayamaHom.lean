import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation
import MagnitudeConjecture.CategoryTheory.LinearBiproduct

/-!
# Nakayama--Hom duality for finite representable sums

For a covariant linear module `M`, dual co-Yoneda identifies maps from `M`
to the coefficient-dual corepresentable at `X` with the coefficient dual of
`M(X)`.  Combined with linear Yoneda, this is the Nakayama--Hom comparison
for a representable projective.  The construction here is presentation-level:
the later Auslander--Reiten argument only needs finite sums of these literal
representables and their representing matrices.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- The definitional value of a bundled dual corepresentable, exposed as a
linear equivalence so that its linear structure can be used without unfolding
the full-subcategory wrappers. -/
def dualLinearYonedaValueLinearEquiv (X Y : C) :
    (dualLinearYonedaLinearModule (k := k) X).obj.obj Y ≃ₗ[k]
      Module.Dual k (Y ⟶ X) :=
  LinearEquiv.refl k _

@[simp]
theorem dualLinearYonedaValueLinearEquiv_apply
    (X Y : C)
    (phi : (dualLinearYonedaLinearModule (k := k) X).obj.obj Y) :
    dualLinearYonedaValueLinearEquiv (k := k) X Y phi =
      (show Module.Dual k (Y ⟶ X) from phi) :=
  rfl

/-- Evaluation at the identity in the dual co-Yoneda lemma. -/
def dualLinearYonedaHomToDualEvaluation
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) (X : C) :
    (M ⟶ dualLinearYonedaLinearModule (k := k) X) →ₗ[k]
      Module.Dual k (M.obj.obj X) where
  toFun a :=
    { toFun := fun x ↦
        dualLinearYonedaValueLinearEquiv (k := k) X X
          (a.hom.app X x) (𝟙 X)
      map_add' := fun x y ↦ by
        rw [map_add, map_add, LinearMap.add_apply]
      map_smul' := fun r x ↦ by
        rw [map_smul, map_smul, LinearMap.smul_apply]
        rfl }
  map_add' a b := by
    apply LinearMap.ext
    intro x
    rfl
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    rfl

/-- A functional on `M(X)` determines a natural map from `M` to the dual
corepresentable at `X`. -/
def dualEvaluationToDualLinearYonedaHom
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) (X : C) :
    Module.Dual k (M.obj.obj X) →ₗ[k]
      (M ⟶ dualLinearYonedaLinearModule (k := k) X) where
  toFun ell := ObjectProperty.homMk
    { app := fun Y ↦ ModuleCat.ofHom
        { toFun := fun y ↦
            { toFun := fun q ↦ ell (M.obj.map q y)
              map_add' := fun q r ↦ by simp
              map_smul' := fun r q ↦ by simp }
          map_add' := fun y z ↦ by
            apply LinearMap.ext
            intro q
            simp
          map_smul' := fun r y ↦ by
            apply LinearMap.ext
            intro q
            simp }
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro q
        change ell (M.obj.map q (M.obj.map f y)) =
          ell (M.obj.map (f ≫ q) y)
        rw [← ModuleCat.comp_apply, ← M.obj.map_comp] }
  map_add' ell psi := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext Y
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro q
    rfl
  map_smul' r ell := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext Y
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro q
    rfl

/-- Linear dual co-Yoneda: maps into a dual corepresentable are exactly
functionals on the value at its representing object. -/
def dualLinearYonedaHomEquiv
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) (X : C) :
    (M ⟶ dualLinearYonedaLinearModule (k := k) X) ≃ₗ[k]
      Module.Dual k (M.obj.obj X) where
  toFun := dualLinearYonedaHomToDualEvaluation M X
  invFun := dualEvaluationToDualLinearYonedaHom M X
  right_inv ell := by
      apply LinearMap.ext
      intro x
      change ell (M.obj.map (𝟙 X) x) = ell x
      rw [M.obj.map_id]
      rfl
  left_inv a := by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext Y
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro q
      have h := ConcreteCategory.congr_hom (a.hom.naturality q) y
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
      change (show Module.Dual k (X ⟶ X) from
          a.hom.app X (M.obj.map q y)) =
        (CategoryTheory.Linear.leftComp k X q).dualMap
          (show Module.Dual k (Y ⟶ X) from a.hom.app Y y) at h
      have hq := LinearMap.congr_fun h (𝟙 X)
      change (show Module.Dual k (X ⟶ X) from
          a.hom.app X (M.obj.map q y)) (𝟙 X) =
        (show Module.Dual k (Y ⟶ X) from a.hom.app Y y) q
      simpa using hq
  map_add' := (dualLinearYonedaHomToDualEvaluation M X).map_add
  map_smul' := (dualLinearYonedaHomToDualEvaluation M X).map_smul

/-- Nakayama--Hom duality for one literal representable projective. -/
def representableNakayamaHomEquiv
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) (X : C) :
    (M ⟶ dualLinearYonedaLinearModule (k := k) X) ≃ₗ[k]
      Module.Dual k
        (linearCoyonedaLinearModule (k := k) X ⟶ M) :=
  (dualLinearYonedaHomEquiv M X).trans
    (linearCoyonedaHomEquiv M X).dualMap

@[simp]
theorem representableNakayamaHomEquiv_apply
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) (X : C)
    (a : M ⟶ dualLinearYonedaLinearModule (k := k) X)
    (f : linearCoyonedaLinearModule (k := k) X ⟶ M) :
    representableNakayamaHomEquiv M X a f =
      dualLinearYonedaValueLinearEquiv (k := k) X X
        (a.hom.app X (f.hom.app X (𝟙 X))) (𝟙 X) :=
  rfl

/-- Naturality of representable Nakayama--Hom duality in the module
variable. -/
theorem representableNakayamaHomEquiv_naturality
    {M N : LinearModuleCategory.{u, v, v, v} (C := C) k}
    (X : C) (g : M ⟶ N)
    (a : N ⟶ dualLinearYonedaLinearModule (k := k) X)
    (f : linearCoyonedaLinearModule (k := k) X ⟶ M) :
    representableNakayamaHomEquiv M X (g ≫ a) f =
      representableNakayamaHomEquiv N X a (f ≫ g) := by
  rfl

/-- Naturality of representable Nakayama--Hom duality in the representing
object. -/
theorem representableNakayamaHomEquiv_projectiveNaturality
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k)
    {X Z : C} (q : X ⟶ Z)
    (a : M ⟶ dualLinearYonedaLinearModule (k := k) Z)
    (f : linearCoyonedaLinearModule (k := k) X ⟶ M) :
    representableNakayamaHomEquiv M X
        (a ≫ dualLinearYonedaLinearModuleMap (k := k) q) f =
      representableNakayamaHomEquiv M Z a
        (linearCoyonedaLinearModuleMap (k := k) q ≫ f) := by
  rw [representableNakayamaHomEquiv_apply,
    representableNakayamaHomEquiv_apply]
  let x := f.hom.app X (𝟙 X)
  have hleft :
      dualLinearYonedaValueLinearEquiv (k := k) X X
          ((a ≫ dualLinearYonedaLinearModuleMap (k := k) q).hom.app X x)
          (𝟙 X) =
        (show Module.Dual k (X ⟶ Z) from a.hom.app X x) q := by
    rw [ObjectProperty.FullSubcategory.comp_hom]
    change dualLinearYonedaValueLinearEquiv (k := k) X X
        ((a.hom ≫ dualLinearYonedaMap (k := k) q).app X x) (𝟙 X) = _
    rw [NatTrans.comp_app, ModuleCat.comp_apply]
    change (CategoryTheory.Linear.rightComp k X q).dualMap
        (show Module.Dual k (X ⟶ Z) from a.hom.app X x) (𝟙 X) = _
    rw [LinearMap.dualMap_apply]
    change (show Module.Dual k (X ⟶ Z) from a.hom.app X x)
        ((𝟙 X) ≫ q) = _
    rw [Category.id_comp]
  have hright :
      dualLinearYonedaValueLinearEquiv (k := k) Z Z
          (a.hom.app Z
            ((linearCoyonedaLinearModuleMap (k := k) q ≫ f).hom.app Z
              (𝟙 Z)))
          (𝟙 Z) =
        (show Module.Dual k (Z ⟶ Z) from a.hom.app Z (f.hom.app Z q))
          (𝟙 Z) := by
    rw [ObjectProperty.FullSubcategory.comp_hom]
    change dualLinearYonedaValueLinearEquiv (k := k) Z Z
        (a.hom.app Z
          ((linearCoyonedaLinearModuleMap (k := k) q).hom.app Z (𝟙 Z) |>
            f.hom.app Z)) (𝟙 Z) = _
    have hmap :
        (linearCoyonedaLinearModuleMap (k := k) q).hom.app Z (𝟙 Z) = q := by
      change (CategoryTheory.Linear.leftComp k Z q) (𝟙 Z) = q
      simp
    rw [hmap]
    simp
  rw [hleft, hright]
  have hf := ConcreteCategory.congr_hom (f.hom.naturality q) (𝟙 X)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hf
  have hqrep :
      (linearCoyonedaLinearModule (k := k) X).obj.map q (𝟙 X) = q := by
    change (CategoryTheory.Linear.rightComp k X q) (𝟙 X) = q
    simp
  rw [hqrep] at hf
  have ha := ConcreteCategory.congr_hom (a.hom.naturality q)
    (f.hom.app X (𝟙 X))
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at ha
  change a.hom.app Z (M.obj.map q (f.hom.app X (𝟙 X))) =
    (dualLinearYoneda (k := k) Z).map q
      (a.hom.app X (f.hom.app X (𝟙 X))) at ha
  rw [hf]
  have haId := congrArg
    (fun phi : (dualLinearYoneda (k := k) Z).obj Z ↦
      (show Module.Dual k (Z ⟶ Z) from phi) (𝟙 Z)) ha
  have haEval :
      (show Module.Dual k (Z ⟶ Z) from
        a.hom.app Z (M.obj.map q (f.hom.app X (𝟙 X)))) (𝟙 Z) =
      (show Module.Dual k (X ⟶ Z) from
        a.hom.app X (f.hom.app X (𝟙 X))) q := by
    change (show Module.Dual k (Z ⟶ Z) from
        a.hom.app Z (M.obj.map q (f.hom.app X (𝟙 X)))) (𝟙 Z) =
      (CategoryTheory.Linear.leftComp k Z q).dualMap
        (show Module.Dual k (X ⟶ Z) from
          a.hom.app X (f.hom.app X (𝟙 X))) (𝟙 Z) at haId
    rw [LinearMap.dualMap_apply] at haId
    change _ = (show Module.Dual k (X ⟶ Z) from
      a.hom.app X (f.hom.app X (𝟙 X))) (q ≫ 𝟙 Z) at haId
    simpa using haId
  exact haEval.symm

/-- The same comparison inside the literal finite-dimensional module
subcategory. -/
def finiteRepresentableNakayamaHomEquiv
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (X : C)
    (hP : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    (M ⟶ finiteDimensionalDualLinearYoneda (k := k) X hI) ≃ₗ[k]
      Module.Dual k
        (finiteDimensionalLinearCoyoneda (k := k) X hP ⟶ M) := by
  let eI :
      (M ⟶ finiteDimensionalDualLinearYoneda (k := k) X hI) ≃ₗ[k]
        (M.obj ⟶ dualLinearYonedaLinearModule (k := k) X) :=
    InducedCategory.homLinearEquiv
  let eP :
      (finiteDimensionalLinearCoyoneda (k := k) X hP ⟶ M) ≃ₗ[k]
        (linearCoyonedaLinearModule (k := k) X ⟶ M.obj) :=
    InducedCategory.homLinearEquiv
  exact eI.trans <| (representableNakayamaHomEquiv M.obj X).trans eP.dualMap

/-- Naturality of the finite-dimensional representable comparison in the
module variable. -/
theorem finiteRepresentableNakayamaHomEquiv_naturality
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (X : C)
    (hP : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (g : M ⟶ N)
    (a : N ⟶ finiteDimensionalDualLinearYoneda (k := k) X hI)
    (f : finiteDimensionalLinearCoyoneda (k := k) X hP ⟶ M) :
    finiteRepresentableNakayamaHomEquiv M X hP hI (g ≫ a) f =
      finiteRepresentableNakayamaHomEquiv N X hP hI a (f ≫ g) := by
  exact representableNakayamaHomEquiv_naturality X g.hom a.hom f.hom

/-- Naturality of the finite-dimensional comparison in the representing
object. -/
theorem finiteRepresentableNakayamaHomEquiv_projectiveNaturality
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    {X Z : C} (q : X ⟶ Z)
    (hPX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hPZ : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) Z))
    (hIX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hIZ : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) Z))
    (a : M ⟶ finiteDimensionalDualLinearYoneda (k := k) Z hIZ)
    (f : finiteDimensionalLinearCoyoneda (k := k) X hPX ⟶ M) :
    finiteRepresentableNakayamaHomEquiv M X hPX hIX
        (a ≫ finiteDimensionalDualLinearYonedaMap (k := k) q hIX hIZ) f =
      finiteRepresentableNakayamaHomEquiv M Z hPZ hIZ a
        (finiteDimensionalLinearCoyonedaMap (k := k) q hPX hPZ ≫ f) := by
  exact representableNakayamaHomEquiv_projectiveNaturality M.obj q a.hom f.hom

/-- Pair a finite family of coefficient functionals with a vector in the
product by summing its component pairings. -/
def finitePiDualToDualPi
    {ι : Type*} [Fintype ι]
    (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] :
    (∀ i, Module.Dual k (V i)) →ₗ[k]
      Module.Dual k (∀ i, V i) where
  toFun Phi :=
    { toFun := fun x ↦ ∑ i, Phi i (x i)
      map_add' := fun x y ↦ by
        simp only [Pi.add_apply, map_add]
        exact Finset.sum_add_distrib
      map_smul' := fun r x ↦ by
        simp only [Pi.smul_apply, map_smul]
        rw [← Finset.smul_sum]
        rfl }
  map_add' Phi Psi := by
    apply LinearMap.ext
    intro x
    simp only [Pi.add_apply, LinearMap.add_apply]
    exact Finset.sum_add_distrib
  map_smul' r Phi := by
    apply LinearMap.ext
    intro x
    change (∑ i, r * Phi i (x i)) = r * ∑ i, Phi i (x i)
    rw [Finset.mul_sum]

/-- Restrict a functional on a finite product to each coordinate. -/
def dualPiToFinitePiDual
    {ι : Type*} [Fintype ι]
    (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] :
    Module.Dual k (∀ i, V i) →ₗ[k]
      (∀ i, Module.Dual k (V i)) := by
  classical
  exact
    { toFun := fun ell i ↦ (LinearMap.single k V i).dualMap ell
      map_add' := fun ell psi ↦ by
        funext i
        apply LinearMap.ext
        intro x
        rfl
      map_smul' := fun r ell ↦ by
        funext i
        apply LinearMap.ext
        intro x
        rfl }

/-- For a finite family, a family of coefficient functionals is canonically
a functional on the product. -/
def finitePiDualEquivDualPi
    {ι : Type*} [Fintype ι]
    (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] :
    (∀ i, Module.Dual k (V i)) ≃ₗ[k]
      Module.Dual k (∀ i, V i) := by
  classical
  exact
    { toFun := finitePiDualToDualPi (k := k) V
      invFun := dualPiToFinitePiDual (k := k) V
      left_inv := fun Phi ↦ by
        funext i
        apply LinearMap.ext
        intro x
        change (∑ j, Phi j (Pi.single i x j)) = Phi i x
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same]
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji]
          simp
        · simp
      right_inv := fun ell ↦ by
        apply LinearMap.ext
        intro x
        change (∑ i, ell (Pi.single i (x i))) = ell x
        rw [← map_sum, LinearMap.sum_single_apply]
      map_add' := (finitePiDualToDualPi (k := k) V).map_add
      map_smul' := (finitePiDualToDualPi (k := k) V).map_smul }

@[simp]
theorem finitePiDualEquivDualPi_apply
    {ι : Type*} [Fintype ι]
    (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (Phi : ∀ i, Module.Dual k (V i)) (x : ∀ i, V i) :
    finitePiDualEquivDualPi (k := k) V Phi x =
      ∑ i, Phi i (x i) :=
  rfl

/-- Nakayama--Hom duality for a literal finite sum of representables.  Both
the projective and Nakayama objects are exactly the values of the two matrix
functors used by the orbit push-down comparison. -/
def finiteRepresentableSumNakayamaHomEquiv
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (Q : Mat_ (Cᵒᵖ))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    (M ⟶ (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q) ≃ₗ[k]
      Module.Dual k
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q ⟶ M) := by
  let P := fun i : Q.ι ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj (Q.X i)
  let I := fun i : Q.ι ↦
    (finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj (Q.X i)
  let eI : (M ⟶ ⨁ I) ≃ₗ[k] (∀ i, M ⟶ I i) :=
    MagnitudeConjecture.CategoryTheory.homBiproductLinearEquiv k M I
  let ePI : (∀ i, M ⟶ I i) ≃ₗ[k]
      (∀ i, Module.Dual k (P i ⟶ M)) :=
    LinearEquiv.piCongrRight fun i ↦
      finiteRepresentableNakayamaHomEquiv M (Q.X i).unop
        (hP (Q.X i).unop) (hI (Q.X i).unop)
  let eP : ((⨁ P) ⟶ M) ≃ₗ[k] (∀ i, P i ⟶ M) :=
    MagnitudeConjecture.CategoryTheory.biproductHomLinearEquiv k M P
  change (M ⟶ ⨁ I) ≃ₗ[k] Module.Dual k ((⨁ P) ⟶ M)
  exact eI.trans <| ePI.trans <|
    (finitePiDualEquivDualPi (k := k)
      (fun i : Q.ι ↦ (P i ⟶ M))).trans eP.dualMap

theorem finiteRepresentableSumNakayamaHomEquiv_apply
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (Q : Mat_ (Cᵒᵖ))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (a : M ⟶ (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q)
    (f : (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q ⟶ M) :
    finiteRepresentableSumNakayamaHomEquiv hP hI Q M a f =
      ∑ i : Q.ι,
        finiteRepresentableNakayamaHomEquiv M (Q.X i).unop
          (hP (Q.X i).unop) (hI (Q.X i).unop)
          (a ≫ biproduct.π
            (fun j : Q.ι ↦
              (finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj
                (Q.X j)) i)
          (biproduct.ι
            (fun j : Q.ι ↦
              (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
                (Q.X j)) i ≫ f) := by
  rfl

/-- Naturality of finite-sum Nakayama--Hom duality in the module variable. -/
theorem finiteRepresentableSumNakayamaHomEquiv_naturality
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (Q : Mat_ (Cᵒᵖ))
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (g : M ⟶ N)
    (a : N ⟶ (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q)
    (f : (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q ⟶ M) :
    finiteRepresentableSumNakayamaHomEquiv hP hI Q M (g ≫ a) f =
      finiteRepresentableSumNakayamaHomEquiv hP hI Q N a (f ≫ g) := by
  rw [finiteRepresentableSumNakayamaHomEquiv_apply,
    finiteRepresentableSumNakayamaHomEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Category.assoc,
    finiteRepresentableNakayamaHomEquiv_naturality]
  rfl

/-- Naturality of finite-sum Nakayama--Hom duality in the literal matrix of
representing objects. -/
theorem finiteRepresentableSumNakayamaHomEquiv_projectiveNaturality
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    {Q' Q : Mat_ (Cᵒᵖ)} (d : Q' ⟶ Q)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (a : M ⟶ (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q')
    (f : (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q ⟶ M) :
    finiteRepresentableSumNakayamaHomEquiv hP hI Q M
        (a ≫ (finiteNakayamaRepresentableSumFunctor (k := k) hI).map d) f =
      finiteRepresentableSumNakayamaHomEquiv hP hI Q' M a
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).map d ≫ f) := by
  rw [finiteRepresentableSumNakayamaHomEquiv_apply,
    finiteRepresentableSumNakayamaHomEquiv_apply]
  classical
  let P' : Q'.ι → FiniteDimensionalModuleCategory (C := C) k := fun i ↦
    finiteDimensionalLinearCoyoneda (k := k) (Q'.X i).unop
      (hP (Q'.X i).unop)
  let P : Q.ι → FiniteDimensionalModuleCategory (C := C) k := fun j ↦
    finiteDimensionalLinearCoyoneda (k := k) (Q.X j).unop
      (hP (Q.X j).unop)
  let I' : Q'.ι → FiniteDimensionalModuleCategory (C := C) k := fun i ↦
    finiteDimensionalDualLinearYoneda (k := k) (Q'.X i).unop
      (hI (Q'.X i).unop)
  let I : Q.ι → FiniteDimensionalModuleCategory (C := C) k := fun j ↦
    finiteDimensionalDualLinearYoneda (k := k) (Q.X j).unop
      (hI (Q.X j).unop)
  let a₀ : M ⟶ ⨁ I' := a
  let f₀ : (⨁ P) ⟶ M := f
  let mP : ∀ i : Q'.ι, ∀ j : Q.ι, P' i ⟶ P j :=
    fun i j ↦ finiteDimensionalLinearCoyonedaMap (k := k) (d i j).unop
      (hP (Q.X j).unop) (hP (Q'.X i).unop)
  let mI : ∀ i : Q'.ι, ∀ j : Q.ι, I' i ⟶ I j :=
    fun i j ↦ finiteDimensionalDualLinearYonedaMap (k := k) (d i j).unop
      (hI (Q.X j).unop) (hI (Q'.X i).unop)
  let aComp (i : Q'.ι) : M ⟶ I' i :=
    a₀ ≫ biproduct.π I' i
  let fComp (j : Q.ι) : P j ⟶ M :=
    biproduct.ι P j ≫ f₀
  let mappedAComp (j : Q.ι) : M ⟶ I j :=
    (a₀ ≫ biproduct.matrix mI) ≫
      biproduct.π I j
  let mappedFComp (i : Q'.ι) : P' i ⟶ M :=
    (biproduct.ι P' i ≫ biproduct.matrix mP) ≫ f₀
  have hN (j : Q.ι) :
      mappedAComp j = ∑ i : Q'.ι, aComp i ≫ mI i j := by
    have hm := biproduct.matrix_π mI j
    calc
      _ = a₀ ≫ (biproduct.matrix mI ≫
          biproduct.π I j) :=
        Category.assoc _ _ _
      _ = a₀ ≫ biproduct.desc (fun i ↦ mI i j) := by rw [hm]
      _ = _ := by
        rw [biproduct.desc_eq, Preadditive.comp_sum]
        apply Finset.sum_congr rfl
        intro i _
        rfl
  have hPcomp (i : Q'.ι) :
      mappedFComp i = ∑ j : Q.ι, mP i j ≫ fComp j := by
    have hm := biproduct.ι_matrix mP i
    change (biproduct.ι P' i ≫ biproduct.matrix mP) ≫ f₀ =
      ∑ j : Q.ι, mP i j ≫ (biproduct.ι P j ≫ f₀)
    calc
      _ = biproduct.lift (fun j ↦ mP i j) ≫ f₀ := by rw [hm]
      _ = _ := by
        rw [biproduct.lift_eq, Preadditive.sum_comp]
        apply Finset.sum_congr rfl
        intro j _
        exact Category.assoc _ _ _
  change
    (∑ j : Q.ι,
      finiteRepresentableNakayamaHomEquiv M (Q.X j).unop
        (hP (Q.X j).unop) (hI (Q.X j).unop)
        (mappedAComp j) (fComp j)) =
    ∑ i : Q'.ι,
      finiteRepresentableNakayamaHomEquiv M (Q'.X i).unop
        (hP (Q'.X i).unop) (hI (Q'.X i).unop)
        (aComp i) (mappedFComp i)
  calc
    _ = ∑ j : Q.ι, ∑ i : Q'.ι,
        finiteRepresentableNakayamaHomEquiv M (Q.X j).unop
          (hP (Q.X j).unop) (hI (Q.X j).unop)
          (aComp i ≫ mI i j) (fComp j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hN, map_sum, LinearMap.sum_apply]
    _ = ∑ i : Q'.ι, ∑ j : Q.ι,
        finiteRepresentableNakayamaHomEquiv M (Q.X j).unop
          (hP (Q.X j).unop) (hI (Q.X j).unop)
          (aComp i ≫ mI i j) (fComp j) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Q'.ι, ∑ j : Q.ι,
        finiteRepresentableNakayamaHomEquiv M (Q'.X i).unop
          (hP (Q'.X i).unop) (hI (Q'.X i).unop)
          (aComp i) (mP i j ≫ fComp j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact finiteRepresentableNakayamaHomEquiv_projectiveNaturality
        M (d i j).unop
          (hP (Q.X j).unop) (hP (Q'.X i).unop)
          (hI (Q.X j).unop) (hI (Q'.X i).unop) _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← map_sum, ← hPcomp]

end MagnitudeConjecture.CoveringHom
