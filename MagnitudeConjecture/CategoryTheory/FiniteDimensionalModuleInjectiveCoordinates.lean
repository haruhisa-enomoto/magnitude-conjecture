import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleEnoughInjectives
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates

/-!
# Dual-corepresentable coordinates on injective modules

Finite dual corepresentables are fully faithful coordinates once their values
are finite-dimensional.  Consequently they are indecomposable over objects
with local endomorphism rings, and every indecomposable injective finite module
is one of them.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v uD vD

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- The dual co-Yoneda coordinate of a map induced by a representing
morphism is ordinary evaluation at that morphism. -/
@[simp]
theorem finiteDualLinearYonedaHomEquiv_functor_map_apply
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (phi : ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj X).obj.obj.obj
      Y.unop) :
    finiteDualLinearYonedaHomEquiv
        ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj X)
        Y.unop (hI Y.unop)
        ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).map f) phi =
      (show Module.Dual k (Y.unop ⟶ X.unop) from phi) f.unop := by
  rw [finiteDualLinearYonedaHomEquiv_apply]
  change
    (CategoryTheory.Linear.rightComp k Y.unop f.unop).dualMap
        (show Module.Dual k (Y.unop ⟶ X.unop) from phi) (𝟙 Y.unop) =
      (show Module.Dual k (Y.unop ⟶ X.unop) from phi) f.unop
  rw [LinearMap.dualMap_apply]
  simp

/-- Finite dual corepresentables faithfully remember the representing
morphism. -/
instance finiteDimensionalDualLinearYonedaFunctor_faithful
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    (finiteDimensionalDualLinearYonedaFunctor (k := k) hI).Faithful := by
  constructor
  intro X Y f g hfg
  apply Quiver.Hom.unop_inj
  apply Module.eval_apply_injective k
  apply LinearMap.ext
  intro phi
  change phi f.unop = phi g.unop
  rw [← finiteDualLinearYonedaHomEquiv_functor_map_apply hI f phi,
    ← finiteDualLinearYonedaHomEquiv_functor_map_apply hI g phi]
  exact congrArg
    (fun a :
        (finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj X ⟶
          (finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj Y ↦
      finiteDualLinearYonedaHomEquiv
        ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj X)
        Y.unop (hI Y.unop) a phi) hfg

/-- Finite-dimensionality makes the double-dual coordinate construction
surjective, hence finite dual corepresentables are full. -/
instance finiteDimensionalDualLinearYonedaFunctor_full
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    (finiteDimensionalDualLinearYonedaFunctor (k := k) hI).Full := by
  constructor
  intro X Y a
  let V := Y.unop ⟶ X.unop
  letI : FiniteDimensional k V :=
    (Module.finite_dual_iff k).mp ((hI X.unop).1 Y.unop)
  let ell : Module.Dual k (Module.Dual k V) :=
    finiteDualLinearYonedaHomEquiv
      ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj X)
      Y.unop (hI Y.unop) a
  let q : V := (Module.evalEquiv k V).symm ell
  refine ⟨q.op, ?_⟩
  apply (finiteDualLinearYonedaHomEquiv
    ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj X)
    Y.unop (hI Y.unop)).injective
  apply LinearMap.ext
  intro phi
  rw [finiteDualLinearYonedaHomEquiv_functor_map_apply]
  change (show Module.Dual k V from phi) q =
    ell (show Module.Dual k V from phi)
  exact LinearMap.congr_fun
    ((Module.evalEquiv k V).apply_symm_apply ell)
      (show Module.Dual k V from phi)

private def endRingEquivOfFullyFaithful
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] [F.Full] [F.Faithful] (X : Cᵒᵖ) :
    End X ≃+* End (F.obj X) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' _ _ := F.map_add
  map_mul' f g := F.map_comp g f

private def oppositeEndRingEquiv (X : C) :
    (End X)ᵐᵒᵖ ≃+* End (Opposite.op X) where
  toFun f := f.unop.op
  invFun f := MulOpposite.op f.unop
  left_inv := by intro f; cases f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; apply Quiver.Hom.unop_inj; rfl
  map_mul' := by intro f g; apply Quiver.Hom.unop_inj; rfl

private theorem isLocalRing_mulOpposite
    {R : Type v} [Ring R] [IsLocalRing R] :
    IsLocalRing Rᵐᵒᵖ := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := R) (a := a.unop) (b := 1 - a.unop)
      (add_sub_cancel a.unop 1) with h | h
  · exact Or.inl (by simpa using h.op)
  · exact Or.inr (by simpa using h.op)

/-- A finite dual corepresentable has local endomorphism ring whenever its
representing object does. -/
theorem finiteDimensionalDualLinearYoneda_end_isLocalRing
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    IsLocalRing (End
      ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj
        (Opposite.op X))) := by
  letI : IsLocalRing (End X) := hlocal X
  letI : IsLocalRing (End X)ᵐᵒᵖ := isLocalRing_mulOpposite
  letI : IsLocalRing (End (Opposite.op X)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (oppositeEndRingEquiv X)
  let F := finiteDimensionalDualLinearYonedaFunctor (k := k) hI
  change IsLocalRing (End (F.obj (Opposite.op X)))
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (endRingEquivOfFullyFaithful F (Opposite.op X))

/-- A finite dual corepresentable represented by an object with local
endomorphism ring is indecomposable. -/
theorem finiteDimensionalDualLinearYoneda_indecomposable
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    Indecomposable
      ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj
        (Opposite.op X)) := by
  letI : IsLocalRing (End
      ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj
        (Opposite.op X))) :=
    finiteDimensionalDualLinearYoneda_end_isLocalRing hI hlocal X
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _

/-- Every indecomposable injective finite module is a finite dual
corepresentable. -/
theorem indecomposable_injective_iso_finiteDimensionalDualLinearYoneda
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    [Injective M] (hMind : Indecomposable M) :
    ∃ X : C, Nonempty
      ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj
        (Opposite.op X) ≅ M) := by
  classical
  obtain ⟨P⟩ := finiteDualCorepresentableCopresentation_nonempty hI M
  let S := moduleSupport k M.obj.obj
  letI : Fintype S := P.supportFintype
  let I (X : S) :=
    finiteDimensionalDualLinearYoneda (k := k) X.1 (hI X.1)
  let B (X : S) :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
    ⨁ fun _ : Fin (P.d X) ↦ I X
  let E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
    ⨁ B
  let n := Fintype.card S
  let e : S ≃ Fin n := Fintype.equivFin S
  let Bfin (i : Fin n) := B (e.symm i)
  let Efin : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
    ⨁ Bfin
  let eOuter : E ≅ Efin :=
    biproduct.whiskerEquiv e (fun X ↦ eqToIso (by simp [Bfin]))
  letI : Mono P.f := P.mono_f
  let p : M ⟶ Efin := P.f ≫ eOuter.hom
  letI : Mono p := inferInstance
  let r : Efin ⟶ M := Injective.factorThru (𝟙 M) p
  have hpr : p ≫ r = 𝟙 M :=
    Injective.comp_factorThru (𝟙 M) p
  let cOuter (i : Fin n) : End M :=
    (p ≫ biproduct.π Bfin i) ≫ (biproduct.ι Bfin i ≫ r)
  have hsumOuter : ∑ i : Fin n, cOuter i = 𝟙 M := by
    change ∑ i : Fin n,
        (p ≫ biproduct.π Bfin i) ≫ (biproduct.ι Bfin i ≫ r) =
      𝟙 M
    calc
      ∑ i : Fin n,
          (p ≫ biproduct.π Bfin i) ≫ (biproduct.ι Bfin i ≫ r) =
        p ≫ (∑ i : Fin n,
          biproduct.π Bfin i ≫ biproduct.ι Bfin i) ≫ r := by
          simp only [Category.assoc, Preadditive.comp_sum,
            Preadditive.sum_comp]
      _ = p ≫ r := by
        have htotal :
            ∑ i : Fin n,
                biproduct.π Bfin i ≫ biproduct.ι Bfin i = 𝟙 Efin :=
          biproduct.total
        rw [htotal]
        simp only [Category.id_comp]
      _ = 𝟙 M := hpr
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hMind
  have hunitOuter : IsUnit (∑ i : Fin n, cOuter i) := by
    rw [hsumOuter]
    exact isUnit_one
  obtain ⟨i, _, hiunit⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := cOuter) hunitOuter
  let X : S := e.symm i
  let cInner (j : Fin (P.d X)) : End M :=
    (p ≫ biproduct.π Bfin i ≫
        biproduct.π (fun _ : Fin (P.d X) ↦ I X) j) ≫
      (biproduct.ι (fun _ : Fin (P.d X) ↦ I X) j ≫
        biproduct.ι Bfin i ≫ r)
  have hsumInner : ∑ j : Fin (P.d X), cInner j = cOuter i := by
    change ∑ j : Fin (P.d X),
        (p ≫ biproduct.π Bfin i ≫
            biproduct.π (fun _ : Fin (P.d X) ↦ I X) j) ≫
          (biproduct.ι (fun _ : Fin (P.d X) ↦ I X) j ≫
            biproduct.ι Bfin i ≫ r) =
      (p ≫ biproduct.π Bfin i) ≫ (biproduct.ι Bfin i ≫ r)
    calc
      ∑ j : Fin (P.d X),
          (p ≫ biproduct.π Bfin i ≫
              biproduct.π (fun _ : Fin (P.d X) ↦ I X) j) ≫
            (biproduct.ι (fun _ : Fin (P.d X) ↦ I X) j ≫
              biproduct.ι Bfin i ≫ r) =
        (p ≫ biproduct.π Bfin i) ≫
          (∑ j : Fin (P.d X),
            biproduct.π (fun _ : Fin (P.d X) ↦ I X) j ≫
              biproduct.ι (fun _ : Fin (P.d X) ↦ I X) j) ≫
          (biproduct.ι Bfin i ≫ r) := by
            simp only [Category.assoc, Preadditive.comp_sum,
              Preadditive.sum_comp]
      _ = (p ≫ biproduct.π Bfin i) ≫
          (biproduct.ι Bfin i ≫ r) := by
        have htotal :
            ∑ j : Fin (P.d X),
                biproduct.π (fun _ : Fin (P.d X) ↦ I X) j ≫
                  biproduct.ι (fun _ : Fin (P.d X) ↦ I X) j =
              𝟙 (B X) :=
          biproduct.total
        change
          (∑ j : Fin (P.d X),
              biproduct.π (fun _ : Fin (P.d X) ↦ I X) j ≫
                biproduct.ι (fun _ : Fin (P.d X) ↦ I X) j) =
            𝟙 (Bfin i) at htotal
        rw [htotal]
        simp only [Category.assoc, Category.id_comp]
  have hunitInner : IsUnit (∑ j : Fin (P.d X), cInner j) := by
    rw [hsumInner]
    exact hiunit
  obtain ⟨j, _, hj⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := cInner) hunitInner
  let a : M ⟶ I X :=
    p ≫ biproduct.π Bfin i ≫
      biproduct.π (fun _ : Fin (P.d X) ↦ I X) j
  let b : I X ⟶ M :=
    biproduct.ι (fun _ : Fin (P.d X) ↦ I X) j ≫
      biproduct.ι Bfin i ≫ r
  have habI : IsIso (a ≫ b) := by
    apply (isUnit_iff_isIso (a ≫ b)).1
    simpa only [cInner, a, b] using hj
  letI : IsIso (a ≫ b) := habI
  have haSplit : IsSplitMono a := by
    apply IsSplitMono.mk'
    exact
      { retraction := b ≫ inv (a ≫ b)
        id := by rw [← Category.assoc, IsIso.hom_inv_id] }
  letI : IsSplitMono a := haSplit
  have hIX : Indecomposable (I X) :=
    finiteDimensionalDualLinearYoneda_indecomposable hI hlocal X.1
  haveI : IsIso a :=
    MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
      hIX a hMind.1
  exact ⟨X.1, ⟨(asIso a).symm⟩⟩

/-- Literal finite dual-corepresentable coordinates on a finite injective
module. -/
structure FiniteDualCorepresentableCoordinates
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) where
  n : ℕ
  X : Fin n → C
  isoSource :
    (⨁ fun i ↦ (finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj
      (Opposite.op (X i))) ≅ M

/-- Every finite injective module has finite coordinates by dual
corepresentables when the representing objects have local endomorphism
rings. -/
theorem finiteDualCorepresentableCoordinates_nonempty_of_injective
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    [Injective M] :
    Nonempty (FiniteDualCorepresentableCoordinates hI M) := by
  classical
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition M
  have hinjective (j : Fin d.n) : Injective (d.summand j) := by
    let i : d.summand j ⟶ M :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv
    let r : M ⟶ d.summand j :=
      d.isoBiproduct.hom ≫ biproduct.π d.summand j
    exact Retract.injective
      { i := i
        r := r
        retract := by simp [i, r, Category.assoc] }
  have hdense (j : Fin d.n) :
      ∃ X : C, Nonempty
        ((finiteDimensionalDualLinearYonedaFunctor (k := k) hI).obj
          (Opposite.op X) ≅ d.summand j) := by
    letI : Injective (d.summand j) := hinjective j
    exact indecomposable_injective_iso_finiteDimensionalDualLinearYoneda
      hI hlocal (d.summand j) (d.indecomposable j)
  choose X e using hdense
  exact ⟨{
    n := d.n
    X := X
    isoSource :=
      biproduct.mapIso (fun j ↦ Classical.choice (e j)) ≪≫
        d.isoBiproduct.symm }⟩

/-- An injective finite module is projective as soon as each of its
indecomposable injective summands is projective.  This packages the finite
Krull--Schmidt reduction used in Auslander-category recovery. -/
theorem finiteDimensionalModule_projective_of_injective_of_indec_projective
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    [Injective M]
    (hprojective : ∀ N :
        FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
      Indecomposable N → Injective N →
        ∀ (i : N ⟶ M) (r : M ⟶ N), i ≫ r = 𝟙 N → Projective N) :
    Projective M := by
  classical
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition M
  have hinjective (j : Fin d.n) : Injective (d.summand j) := by
    let inc : d.summand j ⟶ M :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv
    let ret : M ⟶ d.summand j :=
      d.isoBiproduct.hom ≫ biproduct.π d.summand j
    exact Retract.injective
      { i := inc
        r := ret
        retract := by simp [inc, ret, Category.assoc] }
  letI hsummandProjective (j : Fin d.n) : Projective (d.summand j) := by
    let inc : d.summand j ⟶ M :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv
    let ret : M ⟶ d.summand j :=
      d.isoBiproduct.hom ≫ biproduct.π d.summand j
    exact hprojective (d.summand j) (d.indecomposable j) (hinjective j)
      inc ret (by simp [inc, ret, Category.assoc])
  have hsum : Projective (⨁ d.summand) := by
    constructor
    intro E N f e hepi
    letI : Epi e := hepi
    refine ⟨biproduct.desc (fun j ↦
      Projective.factorThru (biproduct.ι d.summand j ≫ f) e), ?_⟩
    apply biproduct.hom_ext'
    intro j
    simpa only [biproduct.ι_desc_assoc] using
      (Projective.factorThru_comp (biproduct.ι d.summand j ≫ f) e)
  exact Projective.of_iso d.isoBiproduct.symm hsum

end MagnitudeConjecture.CoveringHom
