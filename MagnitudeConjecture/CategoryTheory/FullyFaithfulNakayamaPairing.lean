import MagnitudeConjecture.CategoryTheory.OrbitPushdownCorepresentable

/-!
# Perfect composition pairings through fully faithful functors

A natural isomorphism from a covariant representable to a coefficient-dual
corepresentable is equivalent to a perfect composition pairing.  This file
records the part of that construction which is preserved by a fully faithful
linear functor.  It is used to pass a Nakayama pairing from a deck-orbit
category to its full image in a mesh category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v uD vD

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [CategoryTheory.Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]

/-- A fully faithful linear functor identifies every source Hom space with
the corresponding Hom space between its images. -/
noncomputable def fullyFaithfulMapLinearEquiv (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] (F.obj X ⟶ F.obj Y) :=
  LinearEquiv.ofBijective (F.mapLinearMap k)
    ⟨F.map_injective, F.map_surjective⟩

@[simp]
theorem fullyFaithfulMapLinearEquiv_apply
    {X Y : C} (f : X ⟶ Y) :
    fullyFaithfulMapLinearEquiv (k := k) F X Y f = F.map f :=
  rfl

/-- Evaluation at the target identity extracts the composition functional
from a representable/dual-corepresentable natural isomorphism. -/
def linearModuleIsoEpsilon
    (P J : C)
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J) :
    (P ⟶ J) →ₗ[k] k :=
  (LinearMap.applyₗ (R := k) (𝟙 J)).comp (e.hom.hom.app J).hom

/-- Naturality identifies every component of the module isomorphism with
composition followed by its extracted functional. -/
theorem linearModuleIsoEpsilon_comp
    (P J X : C)
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J)
    (f : P ⟶ X) (g : X ⟶ J) :
    linearModuleIsoEpsilon (k := k) P J e (f ≫ g) =
      (show Module.Dual k (X ⟶ J) from e.hom.hom.app X f) g := by
  have hnat := ConcreteCategory.congr_hom (e.hom.hom.naturality g) f
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hnat
  change e.hom.hom.app J (f ≫ g) =
    (CategoryTheory.Linear.leftComp k J g).dualMap
      (e.hom.hom.app X f) at hnat
  have hnatId := congrArg
    (fun phi : Module.Dual k (J ⟶ J) ↦ phi (𝟙 J)) hnat
  change linearModuleIsoEpsilon (k := k) P J e (f ≫ g) =
    (CategoryTheory.Linear.leftComp k J g).dualMap
      (show Module.Dual k (X ⟶ J) from e.hom.hom.app X f) (𝟙 J) at hnatId
  rw [LinearMap.dualMap_apply] at hnatId
  simpa using hnatId

/-- The composition functional transported to the image of a fully faithful
linear functor. -/
noncomputable def fullyFaithfulLinearModuleIsoEpsilon
    (P J : C)
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J) :
    (F.obj P ⟶ F.obj J) →ₗ[k] k :=
  (linearModuleIsoEpsilon (k := k) P J e).comp
    (fullyFaithfulMapLinearEquiv (k := k) F P J).symm.toLinearMap

/-- On mapped morphisms, the transported functional recovers the component
of the original natural isomorphism. -/
theorem fullyFaithfulLinearModuleIsoEpsilon_map_comp_map
    (P J X : C)
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J)
    (f : P ⟶ X) (g : X ⟶ J) :
    fullyFaithfulLinearModuleIsoEpsilon (k := k) F P J e
        (F.map f ≫ F.map g) =
      (show Module.Dual k (X ⟶ J) from e.hom.hom.app X f) g := by
  rw [← F.map_comp]
  change linearModuleIsoEpsilon (k := k) P J e
      ((fullyFaithfulMapLinearEquiv (k := k) F P J).symm
        (F.map (f ≫ g))) = _
  rw [← fullyFaithfulMapLinearEquiv_apply (k := k) F (f ≫ g)]
  rw [LinearEquiv.symm_apply_apply]
  exact linearModuleIsoEpsilon_comp (k := k) P J X e f g

/-- The perfect pairing induced at an object in the image of a fully faithful
linear functor. -/
noncomputable def fullyFaithfulLinearModuleIsoPairingEquiv
    (P J X : C)
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J) :
    (F.obj P ⟶ F.obj X) ≃ₗ[k]
      Module.Dual k (F.obj X ⟶ F.obj J) :=
  (fullyFaithfulMapLinearEquiv (k := k) F P X).symm.trans
    ((((IsLinearModule (C := C) k).ι.mapIso e).app X).toLinearEquiv.trans
      (fullyFaithfulMapLinearEquiv (k := k) F X J).dualMap.symm)

/-- The transported pairing equivalence is literally composition followed by
the transported functional. -/
theorem fullyFaithfulLinearModuleIsoPairingEquiv_apply_apply
    (P J X : C)
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J)
    (q : F.obj P ⟶ F.obj X) (r : F.obj X ⟶ F.obj J) :
    fullyFaithfulLinearModuleIsoPairingEquiv (k := k) F P J X e q r =
      fullyFaithfulLinearModuleIsoEpsilon (k := k) F P J e (q ≫ r) := by
  obtain ⟨f, rfl⟩ := F.map_surjective q
  obtain ⟨g, rfl⟩ := F.map_surjective r
  rw [fullyFaithfulLinearModuleIsoEpsilon_map_comp_map]
  dsimp only [fullyFaithfulLinearModuleIsoPairingEquiv,
    LinearEquiv.trans_apply]
  change
    (fullyFaithfulMapLinearEquiv (k := k) F X J).dualMap.symm
        (e.hom.hom.app X
          ((fullyFaithfulMapLinearEquiv (k := k) F P X).symm (F.map f)))
        (F.map g) = _
  have hf :
      (fullyFaithfulMapLinearEquiv (k := k) F P X).symm (F.map f) = f := by
    change (fullyFaithfulMapLinearEquiv (k := k) F P X).symm
      (fullyFaithfulMapLinearEquiv (k := k) F P X f) = f
    exact LinearEquiv.symm_apply_apply _ f
  rw [hf]
  change
    (fullyFaithfulMapLinearEquiv (k := k) F X J).dualMap.symm
        (e.hom.hom.app X f)
        (fullyFaithfulMapLinearEquiv (k := k) F X J g) = _
  rw [LinearEquiv.dualMap_symm, LinearEquiv.dualMap_apply,
    LinearEquiv.symm_apply_apply]

/-- The transported composition functional after replacing its two endpoint
objects by isomorphic objects in the target category. -/
noncomputable def fullyFaithfulLinearModuleIsoEpsilonCongr
    (P J : C) (P' J' : D)
    (iP : F.obj P ≅ P') (iJ : F.obj J ≅ J')
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J) :
    (P' ⟶ J') →ₗ[k] k :=
  (fullyFaithfulLinearModuleIsoEpsilon (k := k) F P J e).comp
    (CategoryTheory.Linear.homCongr k iP iJ).symm.toLinearMap

/-- The perfect pairing transported through a fully faithful functor and
through chosen isomorphisms of all three endpoint objects. -/
noncomputable def fullyFaithfulLinearModuleIsoPairingEquivCongr
    (P J X : C) (P' J' X' : D)
    (iP : F.obj P ≅ P') (iJ : F.obj J ≅ J') (iX : F.obj X ≅ X')
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J) :
    (P' ⟶ X') ≃ₗ[k] Module.Dual k (X' ⟶ J') :=
  (CategoryTheory.Linear.homCongr k iP iX).symm.trans
    ((fullyFaithfulLinearModuleIsoPairingEquiv (k := k) F P J X e).trans
      (CategoryTheory.Linear.homCongr k iX iJ).dualMap.symm)

/-- After all object transports, the perfect pairing remains evaluation of
one functional on composition. -/
theorem fullyFaithfulLinearModuleIsoPairingEquivCongr_apply_apply
    (P J X : C) (P' J' X' : D)
    (iP : F.obj P ≅ P') (iJ : F.obj J ≅ J') (iX : F.obj X ≅ X')
    (e : linearCoyonedaLinearModule (k := k) P ≅
      dualLinearYonedaLinearModule (k := k) J)
    (q : P' ⟶ X') (r : X' ⟶ J') :
    fullyFaithfulLinearModuleIsoPairingEquivCongr
        (k := k) F P J X P' J' X' iP iJ iX e q r =
      fullyFaithfulLinearModuleIsoEpsilonCongr
        (k := k) F P J P' J' iP iJ e (q ≫ r) := by
  dsimp only [fullyFaithfulLinearModuleIsoPairingEquivCongr,
    fullyFaithfulLinearModuleIsoEpsilonCongr, LinearEquiv.trans_apply,
    LinearMap.coe_comp, Function.comp_apply]
  change
    (CategoryTheory.Linear.homCongr k iX iJ).dualMap.symm
        (fullyFaithfulLinearModuleIsoPairingEquiv (k := k) F P J X e
          ((CategoryTheory.Linear.homCongr k iP iX).symm q)) r = _
  rw [LinearEquiv.dualMap_symm, LinearEquiv.dualMap_apply,
    fullyFaithfulLinearModuleIsoPairingEquiv_apply_apply]
  congr 1
  change _ = iP.hom ≫ (q ≫ r) ≫ iJ.inv
  rw [CategoryTheory.Linear.homCongr_symm_apply,
    CategoryTheory.Linear.homCongr_symm_apply]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end MagnitudeConjecture.CoveringHom
