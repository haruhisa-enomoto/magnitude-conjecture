import MagnitudeConjecture.Algebra.RightModuleProjectiveRadicalTop
import MagnitudeConjecture.Algebra.BiserialLeftIdealOpposite
import MagnitudeConjecture.Algebra.RightModuleContragredientSkeleton
import MagnitudeConjecture.Algebra.RightModuleRegularDecomposition
import MagnitudeConjecture.Algebra.RightModuleNakayamaHom
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableInjectiveBoundary

/-!
# Opposite primitive-projective presentations

Regular Hom-duality converts a complete primitive-projective presentation of a
finite-dimensional algebra into one for the opposite algebra.  On the selected
projective categories it is an anti-equivalence preserving the radical and its
square.  Hence it reverses ordinary-quiver arrows and converts the outgoing
degree bound for biserial presentations into the corresponding incoming bound.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
theorem rightIdealHomCoordinateEquiv_comp_apply
    {e f g : A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (a : rightIdealFGObj e ⟶ rightIdealFGObj f)
    (b : rightIdealFGObj f ⟶ rightIdealFGObj g) :
    ((rightIdealHomCoordinateEquiv (k := k) he (rightIdealFGObj g)
      (a ≫ b)).1.1) =
      (rightIdealHomCoordinateEquiv (k := k) hf (rightIdealFGObj g) b).1.1 *
        (rightIdealHomCoordinateEquiv (k := k) he (rightIdealFGObj f) a).1.1 := by
  change (b.hom.hom (a.hom.hom (rightIdealGenerator e))).1 =
    (b.hom.hom (rightIdealGenerator f)).1 *
      (a.hom.hom (rightIdealGenerator e)).1
  let x := a.hom.hom (rightIdealGenerator e)
  change (b.hom.hom x).1 =
    (b.hom.hom (rightIdealGenerator f)).1 * x.1
  obtain ⟨c, hc⟩ := x.2
  have hx : (MulOpposite.op c) • rightIdealGenerator f = x := by
    apply Subtype.ext
    exact hc
  have hfixed : (b.hom.hom (rightIdealGenerator f)).1 * f =
      (b.hom.hom (rightIdealGenerator f)).1 := by
    have hgen : (MulOpposite.op f) • rightIdealGenerator f =
        rightIdealGenerator f := by
      apply Subtype.ext
      exact hf.eq
    have hmap := b.hom.hom.map_smul
      (MulOpposite.op f) (rightIdealGenerator f)
    calc
      (b.hom.hom (rightIdealGenerator f)).1 * f =
          ((MulOpposite.op f) •
            b.hom.hom (rightIdealGenerator f)).1 := rfl
      _ = (b.hom.hom
          ((MulOpposite.op f) • rightIdealGenerator f)).1 :=
        congrArg Subtype.val hmap.symm
      _ = (b.hom.hom (rightIdealGenerator f)).1 :=
        congrArg (fun z ↦ (b.hom.hom z).1) hgen
  calc
    (b.hom.hom x).1 =
        (b.hom.hom ((MulOpposite.op c) • rightIdealGenerator f)).1 := by
      rw [hx]
    _ = ((MulOpposite.op c) •
        b.hom.hom (rightIdealGenerator f)).1 := by
      exact congrArg Subtype.val
        (b.hom.hom.map_smul (MulOpposite.op c) (rightIdealGenerator f))
    _ = (b.hom.hom (rightIdealGenerator f)).1 * c := rfl
    _ = (b.hom.hom (rightIdealGenerator f)).1 * (f * c) := by
      rw [← mul_assoc, hfixed]
    _ = (b.hom.hom (rightIdealGenerator f)).1 * x.1 := by
      change f * c = x.1 at hc
      rw [hc]

omit [IsNoetherianRing A] in
theorem leftIdealHom_apply_val
    {e f : A} (hf : IsIdempotentElem f)
    (h : leftIdealFGObj (k := k) f ⟶ leftIdealFGObj (k := k) e)
    (z : leftIdealFGObj (k := k) f) :
    (h.hom.hom z).1 = z.1 * (h.hom.hom (leftIdealGenerator f)).1 := by
  have hz : z.1 • leftIdealGenerator f = z := by
    apply Subtype.ext
    exact leftIdeal_fixed hf z
  calc
    (h.hom.hom z).1 =
        (h.hom.hom (z.1 • leftIdealGenerator f)).1 := by rw [hz]
    _ = (z.1 • h.hom.hom (leftIdealGenerator f)).1 := by
      rw [h.hom.hom.map_smul]
    _ = z.1 * (h.hom.hom (leftIdealGenerator f)).1 := rfl

/-- An isomorphism between primitive left ideals induces one between the
corresponding primitive right ideals. -/
def rightIdealIsoOfLeftIdealIso {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (i : leftIdealFGObj (k := k) e ≅ leftIdealFGObj (k := k) f) :
    rightIdealFGObj e ≅ rightIdealFGObj f where
  hom := (rightIdealHomCoordinateEquiv (k := k) he (rightIdealFGObj f)).symm
    (leftIdealHomRightCoordinateEquiv (k := k) he hf i.inv)
  inv := (rightIdealHomCoordinateEquiv (k := k) hf (rightIdealFGObj e)).symm
    (leftIdealHomRightCoordinateEquiv (k := k) hf he i.hom)
  hom_inv_id := by
    apply (rightIdealHomCoordinateEquiv (k := k) he
      (rightIdealFGObj e)).injective
    apply Subtype.ext
    apply Subtype.ext
    rw [rightIdealHomCoordinateEquiv_comp_apply (k := k) he hf]
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change (i.hom.hom (leftIdealGenerator e)).1 *
        (i.inv.hom.hom (leftIdealGenerator f)).1 = e
    have h := congrArg Subtype.val (i.hom_inv_id_apply (leftIdealGenerator e))
    change (i.inv.hom.hom (i.hom.hom (leftIdealGenerator e))).1 = e at h
    have hiapply := leftIdealHom_apply_val (k := k) hf i.inv
      (i.hom.hom (leftIdealGenerator e))
    exact hiapply.symm.trans h
  inv_hom_id := by
    apply (rightIdealHomCoordinateEquiv (k := k) hf
      (rightIdealFGObj f)).injective
    apply Subtype.ext
    apply Subtype.ext
    rw [rightIdealHomCoordinateEquiv_comp_apply (k := k) hf he]
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change (i.inv.hom.hom (leftIdealGenerator f)).1 *
        (i.hom.hom (leftIdealGenerator e)).1 = f
    have h := congrArg Subtype.val (i.inv_hom_id_apply (leftIdealGenerator f))
    change (i.hom.hom (i.inv.hom.hom (leftIdealGenerator f))).1 = f at h
    have hiapply := leftIdealHom_apply_val (k := k) he i.hom
      (i.inv.hom.hom (leftIdealGenerator f))
    exact hiapply.symm.trans h

/-- Evaluation at the generator identifies the regular Hom-dual of `eA`
with the corresponding left ideal `Ae`. -/
def regularHomDualRightIdealLinearEquiv {e : A}
    (he : IsIdempotentElem e) :
    regularHomDualCarrier (rightIdealFGObj e) ≃ₗ[A] leftIdeal e where
  toFun phi := by
    let gen : rightIdealFGObj e := rightIdealGenerator e
    refine ⟨phi gen, ⟨phi gen, ?_⟩⟩
    have hgen : (MulOpposite.op e) • gen = gen := by
      apply Subtype.ext
      exact he.eq
    calc
      phi gen * e = phi ((MulOpposite.op e) • gen) := by
        exact (phi.map_smul (MulOpposite.op e) gen).symm
      _ = phi gen := congrArg phi hgen
  invFun y :=
    { toFun := fun x ↦ y.1 * x.1
      map_add' := fun x z ↦ mul_add y.1 x.1 z.1
      map_smul' := by
        intro r x
        change y.1 * (x.1 * r.unop) = (y.1 * x.1) * r.unop
        exact (mul_assoc _ _ _).symm }
  left_inv phi := by
    apply LinearMap.ext
    intro x
    let gen : rightIdealFGObj e := rightIdealGenerator e
    obtain ⟨b, hb⟩ := x.2
    change e * b = x.1 at hb
    have hgen : (MulOpposite.op b) • gen = x := by
      apply Subtype.ext
      exact hb
    have hfixed : phi gen * e = phi gen := by
      have hgenFixed : (MulOpposite.op e) • gen = gen := by
        apply Subtype.ext
        exact he.eq
      calc
        phi gen * e = phi ((MulOpposite.op e) • gen) := by
          exact (phi.map_smul (MulOpposite.op e) gen).symm
        _ = phi gen := congrArg phi hgenFixed
    calc
      phi gen * x.1 = phi gen * (e * b) := by rw [hb]
      _ = phi gen * b := by
        rw [← mul_assoc, hfixed]
      _ = phi ((MulOpposite.op b) • gen) := by
        exact (phi.map_smul (MulOpposite.op b) gen).symm
      _ = phi x := by rw [hgen]
  right_inv y := by
    apply Subtype.ext
    exact leftIdeal_fixed he y
  map_add' phi psi := by
    apply Subtype.ext
    rfl
  map_smul' a phi := by
    apply Subtype.ext
    rfl

/-- Categorical form of the regular-Hom identification
`Hom_A(eA,A) ≅ Ae`. -/
def regularHomDualRightIdealIso {e : A} (he : IsIdempotentElem e) :
    regularHomDualFGObj (k := k) (rightIdealFGObj e) ≅
      leftIdealFGObj (k := k) e :=
  QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv A
    (regularHomDualRightIdealLinearEquiv he)

omit [IsNoetherianRing Aᵐᵒᵖ] [IsNoetherianRing A] in
@[simp]
theorem regularHomDualMap_comp
    {P Q T : FGModuleCat.{u} Aᵐᵒᵖ} (d : P ⟶ Q) (e : Q ⟶ T) :
    regularHomDualMap (k := k) (d ≫ e) =
      regularHomDualMap (k := k) e ≫ regularHomDualMap (k := k) d := by
  apply FGModuleCat.hom_ext
  rfl

omit [IsNoetherianRing Aᵐᵒᵖ] [IsNoetherianRing A] in
@[simp]
theorem regularHomDualMap_id (P : FGModuleCat.{u} Aᵐᵒᵖ) :
    regularHomDualMap (k := k) (𝟙 P) = 𝟙 _ := by
  apply FGModuleCat.hom_ext
  rfl

omit [IsNoetherianRing Aᵐᵒᵖ] [IsNoetherianRing A] in
@[simp]
theorem regularHomDualMap_add
    {P Q : FGModuleCat.{u} Aᵐᵒᵖ} (d e : P ⟶ Q) :
    regularHomDualMap (k := k) (d + e) =
      regularHomDualMap (k := k) d + regularHomDualMap (k := k) e := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro p
  change phi (d.hom.hom p + e.hom.hom p) =
    phi (d.hom.hom p) + phi (e.hom.hom p)
  exact map_add phi _ _

omit [IsNoetherianRing Aᵐᵒᵖ] [IsNoetherianRing A] in
@[simp]
theorem regularHomDualMap_smul
    {P Q : FGModuleCat.{u} Aᵐᵒᵖ} (c : k) (d : P ⟶ Q) :
    regularHomDualMap (k := k) (c • d) =
      c • regularHomDualMap (k := k) d := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro p
  change phi ((algebraMap k Aᵐᵒᵖ c) • d.hom.hom p) =
    (algebraMap k A c) * phi (d.hom.hom p)
  rw [phi.map_smul]
  change phi (d.hom.hom p) * (algebraMap k Aᵐᵒᵖ c).unop =
    (algebraMap k A c) * phi (d.hom.hom p)
  rw [MulOpposite.algebraMap_apply, MulOpposite.unop_op,
    Algebra.commutes]

/-- Regular Hom sends an isomorphism of right modules to the reversed
isomorphism of left modules. -/
def regularHomDualMapIso {P Q : FGModuleCat.{u} Aᵐᵒᵖ} (i : P ≅ Q) :
    regularHomDualFGObj (k := k) Q ≅ regularHomDualFGObj (k := k) P where
  hom := regularHomDualMap (k := k) i.hom
  inv := regularHomDualMap (k := k) i.inv
  hom_inv_id := by
    rw [← regularHomDualMap_comp, i.inv_hom_id, regularHomDualMap_id]
  inv_hom_id := by
    rw [← regularHomDualMap_comp, i.hom_inv_id, regularHomDualMap_id]

omit [IsNoetherianRing A] in
/-- Regular Hom-duality is faithful on finite projective right modules. -/
theorem regularHomDualMap_injective
    (P Q : FGModuleCat.{u} Aᵐᵒᵖ) [Projective Q] :
    Function.Injective (fun d : P ⟶ Q ↦
      regularHomDualMap (k := k) d) := by
  intro d e hde
  apply projectiveNakayamaMap_injective (k := k) P Q
  change (QuotientSubmoduleEquidistribution.Contragredient.dualFunctor
      k A).map (regularHomDualMap (k := k) d).op =
    (QuotientSubmoduleEquidistribution.Contragredient.dualFunctor
      k A).map (regularHomDualMap (k := k) e).op
  have hde' : regularHomDualMap (k := k) d =
      regularHomDualMap (k := k) e := hde
  rw [hde']

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

open CategoryTheory.Limits
open scoped BigOperators ModuleCat.Algebra

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable [IsNoetherianRing A] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

def oppositeIdempotent (p : S.ProjectiveLabel) : Aᵐᵒᵖ :=
  MulOpposite.op (P.idempotent p)

omit [IsNoetherianRing A] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ] in
theorem oppositeIdempotents_complete :
    CompleteOrthogonalIdempotents P.oppositeIdempotent where
  idem p := by
    apply MulOpposite.unop_injective
    exact (P.complete.idem p).eq
  ortho := by
    intro p q hpq
    apply MulOpposite.unop_injective
    change P.idempotent q * P.idempotent p = 0
    exact P.complete.ortho hpq.symm
  complete := by
    apply MulOpposite.unop_injective
    simpa [oppositeIdempotent] using P.complete.complete

omit [IsNoetherianRing A] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ] in
theorem oppositePrimitive (p : S.ProjectiveLabel) :
    RightModule.PrimitiveIdempotentData (P.oppositeIdempotent p) :=
  (P.primitive p).opposite

def oppositeProjectiveCoordinate (p : S.ProjectiveLabel) :
    S.contragredientSkeleton.ProjectiveLabel :=
  S.contragredientSkeleton.primitiveSourceProjectiveLabel
    (P.oppositePrimitive p)

def oppositeProjectiveCoordinateIso (p : S.ProjectiveLabel) :
    RightModule.rightIdealFGObj (P.oppositeIdempotent p) ≅
      S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate p).label :=
  S.contragredientSkeleton.primitiveSourceIso (P.oppositePrimitive p)

omit [IsNoetherianRing A] in
theorem oppositeProjectiveCoordinate_surjective :
    Function.Surjective P.oppositeProjectiveCoordinate := by
  classical
  let B := Aᵐᵒᵖ
  let T := S.contragredientSkeleton
  let σ := T.almostSplitSkeleton
  let R : Set (Fin T.n) :=
    Set.range (fun p ↦ (P.oppositeProjectiveCoordinate p).label)
  have hright : ∀ p : S.ProjectiveLabel,
      σ.InAdd R (RightModule.rightIdealFGObj (P.oppositeIdempotent p)) := by
    intro p
    apply (σ.inAdd_iff_of_iso (P.oppositeProjectiveCoordinateIso p)).2
    exact σ.inAdd_obj ⟨p, rfl⟩
  have hbiproduct : σ.InAdd R
      (⨁ fun p : S.ProjectiveLabel ↦
        RightModule.rightIdealFGObj (P.oppositeIdempotent p)) :=
    σ.inAdd_biproduct (FintypeCat.of S.ProjectiveLabel)
      (fun p ↦ RightModule.rightIdealFGObj (P.oppositeIdempotent p)) hright
  have hregular : σ.InAdd R (RightModule.rightRegularFGObj (B := B)) := by
    apply (σ.inAdd_iff_of_iso
      (RightModule.regularDecompositionIso P.oppositeIdempotent
        P.oppositeIdempotents_complete)).2
    exact hbiproduct
  intro q
  obtain ⟨n, qmap, hqmap⟩ :=
    RightModule.exists_fin_free_epimorphism (T.fgObj q.label)
  let Free : FGModuleCat.{u} Bᵐᵒᵖ :=
    FGModuleCat.of Bᵐᵒᵖ (Fin n → Bᵐᵒᵖ)
  letI : Epi qmap := hqmap
  obtain ⟨s, hs⟩ := q.projective.factors (𝟙 (T.fgObj q.label)) qmap
  let retract : CategoryTheory.Retract (T.fgObj q.label) Free :=
    { i := s
      r := qmap
      retract := by simpa using hs }
  let U := forget₂ (FGModuleCat.{u} Bᵐᵒᵖ) (ModuleCat.{u} Bᵐᵒᵖ)
  let regularUnderlyingIso : ModuleCat.of Bᵐᵒᵖ Bᵐᵒᵖ ≅
      (RightModule.rightRegularFGObj (B := B)).obj :=
    LinearEquiv.toModuleIso (RightModule.rightRegularLinearEquiv (A := B))
  letI : PreservesBiproduct
      (fun _ : Fin n ↦ RightModule.rightRegularFGObj (B := B)) U :=
    preservesBiproduct_of_preservesProduct U
  let freeIso : Free ≅
      ⨁ fun _ : Fin n ↦ RightModule.rightRegularFGObj (B := B) :=
    ObjectProperty.isoMk _ <|
      (ModuleCat.biproductIsoPi
        (fun _ : Fin n ↦ ModuleCat.of Bᵐᵒᵖ Bᵐᵒᵖ)).symm |>.trans <|
        (biproduct.mapIso fun _ : Fin n ↦ regularUnderlyingIso) |>.trans <|
          (U.mapBiproduct
            (fun _ : Fin n ↦ RightModule.rightRegularFGObj (B := B))).symm
  have hfreeBiproduct : σ.InAdd R
      (⨁ fun _ : Fin n ↦ RightModule.rightRegularFGObj (B := B)) :=
    σ.inAdd_biproduct (FintypeCat.of (Fin n))
      (fun _ ↦ RightModule.rightRegularFGObj (B := B))
      (fun _ ↦ hregular)
  have hfree : σ.InAdd R Free :=
    (σ.inAdd_iff_of_iso freeIso).2 hfreeBiproduct
  have hqR : q.label ∈ R := σ.index_mem_of_retract_inAdd retract hfree
  obtain ⟨p, hp⟩ := hqR
  refine ⟨p, ?_⟩
  cases q with
  | mk qlabel qprojective =>
      cases hcoord : P.oppositeProjectiveCoordinate p with
      | mk plabel pprojective =>
          change (P.oppositeProjectiveCoordinate p).label = qlabel at hp
          rw [hcoord] at hp
          have hlabel : plabel = qlabel := hp
          subst qlabel
          rfl

omit [IsNoetherianRing A] in
theorem oppositeProjectiveCoordinate_injective :
    Function.Injective P.oppositeProjectiveCoordinate := by
  intro p q hpq
  have hlabel : (P.oppositeProjectiveCoordinate p).label =
      (P.oppositeProjectiveCoordinate q).label :=
    congrArg ProjectiveLabel.label hpq
  let iOpp : RightModule.rightIdealFGObj (P.oppositeIdempotent p) ≅
      RightModule.rightIdealFGObj (P.oppositeIdempotent q) :=
    (P.oppositeProjectiveCoordinateIso p).trans <|
      (eqToIso (congrArg S.contragredientSkeleton.fgObj hlabel)).trans <|
        (P.oppositeProjectiveCoordinateIso q).symm
  let E : FGModuleCat.{u} (Aᵐᵒᵖ)ᵐᵒᵖ ≌ FGModuleCat.{u} A :=
    LeftModule.fgModuleEquivalenceOfAlgEquiv (AlgEquiv.opOp k A).symm
  let iLeft : RightModule.leftIdealFGObj (k := k) (P.idempotent p) ≅
      RightModule.leftIdealFGObj (k := k) (P.idempotent q) :=
    (RightModule.oppositeRightIdealLeftIdealIso
      (k := k) (P.idempotent p)).symm ≪≫
      E.functor.mapIso iOpp ≪≫
        RightModule.oppositeRightIdealLeftIdealIso
          (k := k) (P.idempotent q)
  let iRight : RightModule.rightIdealFGObj (P.idempotent p) ≅
      RightModule.rightIdealFGObj (P.idempotent q) :=
    RightModule.rightIdealIsoOfLeftIdealIso
      (P.primitive p).idempotent (P.primitive q).idempotent iLeft
  let iSkeleton : S.fgObj p.label ≅ S.fgObj q.label :=
    (P.primitiveProjectiveIso p).symm ≪≫ iRight ≪≫
      P.primitiveProjectiveIso q
  have hpqlabel : p.label = q.label := S.fgObj_skeletal ⟨iSkeleton⟩
  cases p with
  | mk plabel pprojective =>
      cases q with
      | mk qlabel qprojective =>
          simp only at hpqlabel ⊢
          subst qlabel
          rfl

def oppositeProjectiveEquiv :
    S.ProjectiveLabel ≃ S.contragredientSkeleton.ProjectiveLabel :=
  Equiv.ofBijective P.oppositeProjectiveCoordinate
    ⟨P.oppositeProjectiveCoordinate_injective,
      P.oppositeProjectiveCoordinate_surjective⟩

/-- The primitive projective presentation of the opposite algebra obtained by
opposing and then reindexing the original complete primitive family. -/
def oppositePresentation :
    S.contragredientSkeleton.PrimitiveProjectivePresentation where
  idempotent q :=
    P.oppositeIdempotent (P.oppositeProjectiveEquiv.symm q)
  complete := by
    exact (CompleteOrthogonalIdempotents.equiv
      P.oppositeProjectiveEquiv.symm).2 P.oppositeIdempotents_complete
  primitive q := P.oppositePrimitive (P.oppositeProjectiveEquiv.symm q)
  sourceLabel q := P.oppositeProjectiveEquiv.apply_symm_apply q

/-- Biseriality is symmetric under passage to the opposite primitive
projective presentation. -/
theorem oppositePresentation_isBiserial
    (hP : P.IsBiserial) : P.oppositePresentation.IsBiserial := by
  constructor
  · intro q
    exact (RightModule.leftIdealFGObj_isBiserialObject_iff_oppositeRightIdeal
      (k := k) (P.idempotent (P.oppositeProjectiveEquiv.symm q))).1
        (hP.2 (P.oppositeProjectiveEquiv.symm q))
  · intro q
    letI : IsNoetherianRing ((Aᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    exact (RightModule.leftIdealFGObj_isBiserialObject_iff_oppositeRightIdeal
      (k := k) (A := Aᵐᵒᵖ)
      (P.oppositePresentation.idempotent q)).2 <|
        (RightModule.rightIdealFGObj_isBiserialObject_mapAlgEquiv_iff
          (AlgEquiv.opOp k A) (P.idempotent
            (P.oppositeProjectiveEquiv.symm q))).2
              (hP.1 (P.oppositeProjectiveEquiv.symm q))

private abbrev oppositeRegularEquivalence :
    FGModuleCat.{u} (Aᵐᵒᵖ)ᵐᵒᵖ ≌ FGModuleCat.{u} A :=
  LeftModule.fgModuleEquivalenceOfAlgEquiv (AlgEquiv.opOp k A).symm

omit [IsNoetherianRing Aᵐᵒᵖ] [IsNoetherianRing A]
    [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ] in
@[simp]
theorem oppositeRegularEquivalence_preimage_apply
    {X Y : FGModuleCat.{u} (Aᵐᵒᵖ)ᵐᵒᵖ}
    (f : (oppositeRegularEquivalence (k := k) (A := A)).functor.obj X ⟶
      (oppositeRegularEquivalence (k := k) (A := A)).functor.obj Y)
    (x : X) :
    ((oppositeRegularEquivalence (k := k) (A := A)).functor.preimage f).hom.hom x =
      f.hom.hom x := by
  let E := oppositeRegularEquivalence (k := k) (A := A)
  change (E.functor.map (E.functor.preimage f)).hom.hom x = f.hom.hom x
  rw [E.functor.map_preimage]

/-- The opposite principal projective at `p`, after restriction along the
double-opposite equivalence, is the regular Hom-dual of the original
selected projective at `p`. -/
def oppositeProjectiveRegularHomIso (p : S.ProjectiveLabel) :
    (oppositeRegularEquivalence (k := k) (A := A)).functor.obj
        (RightModule.rightIdealFGObj (P.oppositeIdempotent p)) ≅
      RightModule.regularHomDualFGObj (k := k) (S.fgObj p.label) :=
  (RightModule.oppositeRightIdealLeftIdealIso
      (k := k) (P.idempotent p)).trans <|
    (RightModule.regularHomDualRightIdealIso
      (k := k) (P.primitive p).idempotent).symm |>.trans <|
        (RightModule.regularHomDualMapIso
          (k := k) (P.primitiveProjectiveIso p)).symm

/-- The morphism map of regular Hom-duality, realized between the selected
projectives on the two sides. -/
def oppositeProjectiveMap {p q : S.ProjectiveLabel}
    (f : S.fgObj q.label ⟶ S.fgObj p.label) :
    S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate p).label ⟶
      S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate q).label :=
    (P.oppositeProjectiveCoordinateIso p).inv ≫
      (oppositeRegularEquivalence (k := k) (A := A)).functor.preimage
        ((P.oppositeProjectiveRegularHomIso p).hom ≫
          RightModule.regularHomDualMap (k := k) f ≫
            (P.oppositeProjectiveRegularHomIso q).inv) ≫
      (P.oppositeProjectiveCoordinateIso q).hom

omit [IsNoetherianRing A] in
/-- In literal principal-projective coordinates, regular Hom-duality sends
an element of the opposite right ideal to right multiplication by the
original projective-map coordinate. -/
theorem oppositeProjectiveMap_literal_apply
    {p q : S.ProjectiveLabel}
    (f : S.fgObj q.label ⟶ S.fgObj p.label)
    (x : RightModule.rightIdeal (P.oppositeIdempotent p)) :
    (((P.oppositeProjectiveCoordinateIso p).hom ≫
        P.oppositeProjectiveMap f ≫
          (P.oppositeProjectiveCoordinateIso q).inv).hom.hom x).1 =
      MulOpposite.op
        (x.1.unop *
          (((P.primitiveProjectiveIso q).hom ≫ f ≫
            (P.primitiveProjectiveIso p).inv).hom.hom
              (RightModule.rightIdealGenerator (P.idempotent q))).1) := by
  simp [oppositeProjectiveMap, oppositeProjectiveRegularHomIso,
    regularHomDualMapIso, regularHomDualMap,
    RightModule.regularHomDualRightIdealIso,
    RightModule.regularHomDualRightIdealLinearEquiv,
    RightModule.oppositeRightIdealLeftIdealIso,
    RightModule.oppositeRightIdealLeftIdealLinearEquiv,
    RightModule.oppositeRightIdealToLeftIdeal,
    RightModule.leftIdealToOppositeRightIdeal,
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv,
    Category.assoc]
  rfl

omit [IsNoetherianRing A] in
@[simp]
theorem oppositeProjectiveMap_id (p : S.ProjectiveLabel) :
    P.oppositeProjectiveMap (𝟙 (S.fgObj p.label)) =
      𝟙 (S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate p).label) := by
  unfold oppositeProjectiveMap
  simp

omit [IsNoetherianRing A] in
@[simp]
theorem oppositeProjectiveMap_comp {p q r : S.ProjectiveLabel}
    (f : S.fgObj q.label ⟶ S.fgObj p.label)
    (g : S.fgObj r.label ⟶ S.fgObj q.label) :
    P.oppositeProjectiveMap (g ≫ f) =
      P.oppositeProjectiveMap f ≫ P.oppositeProjectiveMap g := by
  unfold oppositeProjectiveMap
  rw [RightModule.regularHomDualMap_comp]
  let E := oppositeRegularEquivalence (k := k) (A := A)
  have hpre : E.functor.preimage
      ((P.oppositeProjectiveRegularHomIso p).hom ≫
        (RightModule.regularHomDualMap (k := k) f ≫
          RightModule.regularHomDualMap (k := k) g) ≫
            (P.oppositeProjectiveRegularHomIso r).inv) =
      E.functor.preimage
          ((P.oppositeProjectiveRegularHomIso p).hom ≫
            RightModule.regularHomDualMap (k := k) f ≫
              (P.oppositeProjectiveRegularHomIso q).inv) ≫
        E.functor.preimage
          ((P.oppositeProjectiveRegularHomIso q).hom ≫
            RightModule.regularHomDualMap (k := k) g ≫
              (P.oppositeProjectiveRegularHomIso r).inv) := by
    apply E.functor.map_injective
    simp [Category.assoc]
  rw [hpre]
  simp [Category.assoc]
  rfl

/-- Recover the original projective morphism from its realized
regular-Hom dual. -/
def oppositeProjectiveMapPreimage {p q : S.ProjectiveLabel}
    (h : S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate p).label ⟶
      S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate q).label) :
    S.fgObj q.label ⟶ S.fgObj p.label := by
  letI : Projective (S.fgObj p.label) := p.projective
  let E := oppositeRegularEquivalence (k := k) (A := A)
  exact RightModule.regularHomDualMapPreimage
    (k := k) (S.fgObj q.label) (S.fgObj p.label)
      ((P.oppositeProjectiveRegularHomIso p).inv ≫
        E.functor.map
          ((P.oppositeProjectiveCoordinateIso p).hom ≫ h ≫
            (P.oppositeProjectiveCoordinateIso q).inv) ≫
        (P.oppositeProjectiveRegularHomIso q).hom)

omit [IsNoetherianRing A] in
@[simp]
theorem oppositeProjectiveMap_preimage {p q : S.ProjectiveLabel}
    (h : S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate p).label ⟶
      S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate q).label) :
    P.oppositeProjectiveMap (P.oppositeProjectiveMapPreimage h) = h := by
  unfold oppositeProjectiveMap oppositeProjectiveMapPreimage
  rw [RightModule.regularHomDualMap_preimage]
  simp [Category.assoc]

omit [IsNoetherianRing A] in
@[simp]
theorem oppositeProjectiveMapPreimage_map {p q : S.ProjectiveLabel}
    (f : S.fgObj q.label ⟶ S.fgObj p.label) :
    P.oppositeProjectiveMapPreimage (P.oppositeProjectiveMap f) = f := by
  letI : Projective (S.fgObj p.label) := p.projective
  apply RightModule.regularHomDualMap_injective
    (k := k) (S.fgObj q.label) (S.fgObj p.label)
  change RightModule.regularHomDualMap (k := k)
      (P.oppositeProjectiveMapPreimage (P.oppositeProjectiveMap f)) =
    RightModule.regularHomDualMap (k := k) f
  unfold oppositeProjectiveMapPreimage oppositeProjectiveMap
  dsimp only
  rw [RightModule.regularHomDualMap_preimage]
  simp [Category.assoc]

omit [IsNoetherianRing A] in
@[simp]
theorem oppositeProjectiveMap_add {p q : S.ProjectiveLabel}
    (f g : S.fgObj q.label ⟶ S.fgObj p.label) :
    P.oppositeProjectiveMap (f + g) =
      P.oppositeProjectiveMap f + P.oppositeProjectiveMap g := by
  unfold oppositeProjectiveMap
  rw [RightModule.regularHomDualMap_add]
  let E := oppositeRegularEquivalence (k := k) (A := A)
  have hpre : E.functor.preimage
      ((P.oppositeProjectiveRegularHomIso p).hom ≫
        (RightModule.regularHomDualMap (k := k) f +
          RightModule.regularHomDualMap (k := k) g) ≫
        (P.oppositeProjectiveRegularHomIso q).inv) =
      E.functor.preimage
          ((P.oppositeProjectiveRegularHomIso p).hom ≫
            RightModule.regularHomDualMap (k := k) f ≫
            (P.oppositeProjectiveRegularHomIso q).inv) +
        E.functor.preimage
          ((P.oppositeProjectiveRegularHomIso p).hom ≫
            RightModule.regularHomDualMap (k := k) g ≫
            (P.oppositeProjectiveRegularHomIso q).inv) := by
    apply E.functor.map_injective
    simp [Preadditive.comp_add, Preadditive.add_comp]
  rw [hpre]
  simp [Preadditive.comp_add, Preadditive.add_comp]
  rfl

omit [IsNoetherianRing A] in
@[simp]
theorem oppositeProjectiveMap_smul {p q : S.ProjectiveLabel}
    (c : k) (f : S.fgObj q.label ⟶ S.fgObj p.label) :
    P.oppositeProjectiveMap (c • f) =
      c • P.oppositeProjectiveMap f := by
  unfold oppositeProjectiveMap
  rw [RightModule.regularHomDualMap_smul]
  let E := oppositeRegularEquivalence (k := k) (A := A)
  have hpre : E.functor.preimage
      ((P.oppositeProjectiveRegularHomIso p).hom ≫
        (c • RightModule.regularHomDualMap (k := k) f) ≫
        (P.oppositeProjectiveRegularHomIso q).inv) =
      c • E.functor.preimage
        ((P.oppositeProjectiveRegularHomIso p).hom ≫
          RightModule.regularHomDualMap (k := k) f ≫
          (P.oppositeProjectiveRegularHomIso q).inv) := by
    apply E.functor.map_injective
    simp
  rw [hpre]
  simp
  rfl

/-- Regular Hom-duality is a linear equivalence on every selected
projective Hom space. -/
def oppositeProjectiveHomLinearEquiv (p q : S.ProjectiveLabel) :
    (S.fgObj q.label ⟶ S.fgObj p.label) ≃ₗ[k]
      (S.contragredientSkeleton.fgObj
          (P.oppositeProjectiveCoordinate p).label ⟶
        S.contragredientSkeleton.fgObj
          (P.oppositeProjectiveCoordinate q).label) where
  toFun := P.oppositeProjectiveMap
  invFun := P.oppositeProjectiveMapPreimage
  left_inv := P.oppositeProjectiveMapPreimage_map
  right_inv := P.oppositeProjectiveMap_preimage
  map_add' := P.oppositeProjectiveMap_add
  map_smul' := P.oppositeProjectiveMap_smul

/-- Regular Hom-duality on the selected projectives, realized in the
opposite algebra's selected projective category. -/
def oppositeProjectiveFunctor :
    S.ProjectiveCategoryᵒᵖ ⥤ S.contragredientSkeleton.ProjectiveCategory where
  obj p := P.oppositeProjectiveCoordinate
    (show S.ProjectiveLabel from p.unop)
  map f := (InducedCategory.homLinearEquiv (R := k)).symm
    (P.oppositeProjectiveMap (S.projectiveInclusion.map f.unop))
  map_id p := by
    apply InducedCategory.hom_ext
    simp
    change P.oppositeProjectiveMap
        (𝟙 (S.fgObj (show S.ProjectiveLabel from p.unop).label)) =
      𝟙 (S.contragredientSkeleton.fgObj
        (P.oppositeProjectiveCoordinate
          (show S.ProjectiveLabel from p.unop)).label)
    exact P.oppositeProjectiveMap_id _
  map_comp f g := by
    apply InducedCategory.hom_ext
    simp
    change P.oppositeProjectiveMap
        (S.projectiveInclusion.map g.unop ≫
          S.projectiveInclusion.map f.unop) =
      P.oppositeProjectiveMap (S.projectiveInclusion.map f.unop) ≫
        P.oppositeProjectiveMap (S.projectiveInclusion.map g.unop)
    exact P.oppositeProjectiveMap_comp _ _

noncomputable instance oppositeProjectiveFunctor_additive :
    P.oppositeProjectiveFunctor.Additive where
  map_add := by
    intro X Y f g
    apply InducedCategory.hom_ext
    simp [oppositeProjectiveFunctor]
    change P.oppositeProjectiveMap
        (S.projectiveInclusion.map f.unop +
          S.projectiveInclusion.map g.unop) =
      P.oppositeProjectiveMap (S.projectiveInclusion.map f.unop) +
        P.oppositeProjectiveMap (S.projectiveInclusion.map g.unop)
    exact P.oppositeProjectiveMap_add _ _

noncomputable instance oppositeProjectiveFunctor_linear :
    P.oppositeProjectiveFunctor.Linear k where
  map_smul := by
    intro X Y f c
    apply InducedCategory.hom_ext
    simp [oppositeProjectiveFunctor]
    change P.oppositeProjectiveMap
        (c • S.projectiveInclusion.map f.unop) =
      c • P.oppositeProjectiveMap (S.projectiveInclusion.map f.unop)
    exact P.oppositeProjectiveMap_smul _ _

/-- Regular Hom-duality is fully faithful on the selected projective
subcategory. -/
def oppositeProjectiveFunctorFullyFaithful :
    P.oppositeProjectiveFunctor.FullyFaithful where
  preimage {X Y} h := by
    let dAmbient : S.fgObj
          (show S.ProjectiveLabel from Y.unop).label ⟶
        S.fgObj (show S.ProjectiveLabel from X.unop).label :=
      P.oppositeProjectiveMapPreimage
        (S.contragredientSkeleton.projectiveInclusion.map h)
    let d : (show S.ProjectiveCategory from Y.unop) ⟶
        (show S.ProjectiveCategory from X.unop) :=
      InducedCategory.homMk dAmbient
    exact d.op
  map_preimage {X Y} h := by
    apply InducedCategory.hom_ext
    simp [oppositeProjectiveFunctor]
    change P.oppositeProjectiveMap
        (P.oppositeProjectiveMapPreimage
          (S.contragredientSkeleton.projectiveInclusion.map h)) = h.hom
    rw [P.oppositeProjectiveMap_preimage]
    rfl
  preimage_map {X Y} f := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    simp [oppositeProjectiveFunctor]
    change P.oppositeProjectiveMapPreimage
        (P.oppositeProjectiveMap (S.projectiveInclusion.map f.unop)) =
      S.projectiveInclusion.map f.unop
    exact P.oppositeProjectiveMapPreimage_map _

omit [IsNoetherianRing A] in
theorem oppositeProjectiveFunctor_obj_surjective :
    Function.Surjective P.oppositeProjectiveFunctor.obj := by
  intro q
  obtain ⟨p, hp⟩ := P.oppositeProjectiveCoordinate_surjective
    (show S.contragredientSkeleton.ProjectiveLabel from q)
  refine ⟨Opposite.op (S.ordinaryProjectiveObj p), ?_⟩
  exact hp

/-- Regular Hom-duality is an equivalence from the opposite selected
projective category to the selected projectives of the opposite algebra. -/
def oppositeProjectiveCategoryEquivalence :
    S.ProjectiveCategoryᵒᵖ ≌
      S.contragredientSkeleton.ProjectiveCategory := by
  let F := P.oppositeProjectiveFunctor
  let hFF := P.oppositeProjectiveFunctorFullyFaithful
  letI : F.IsEquivalence := Functor.IsEquivalence.mk
    hFF.faithful hFF.full
      (Functor.essSurj_of_surj P.oppositeProjectiveFunctor_obj_surjective)
  exact F.asEquivalence

/-- The Hom-space form of the selected-projective anti-equivalence. -/
def projectiveOppositeHomLinearEquiv (p q : S.ProjectiveLabel) :
    (S.ordinaryProjectiveObj q ⟶ S.ordinaryProjectiveObj p) ≃ₗ[k]
      (S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate p) ⟶
        S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate q)) where
  toFun f := InducedCategory.homMk (P.oppositeProjectiveMap f.hom)
  invFun h := InducedCategory.homMk (P.oppositeProjectiveMapPreimage h.hom)
  left_inv f := by
    apply InducedCategory.hom_ext
    exact P.oppositeProjectiveMapPreimage_map f.hom
  right_inv h := by
    apply InducedCategory.hom_ext
    exact P.oppositeProjectiveMap_preimage h.hom
  map_add' f g := by
    apply InducedCategory.hom_ext
    exact P.oppositeProjectiveMap_add f.hom g.hom
  map_smul' c f := by
    apply InducedCategory.hom_ext
    exact P.oppositeProjectiveMap_smul c f.hom

omit [IsNoetherianRing A] in
@[simp]
theorem projectiveOppositeHomLinearEquiv_apply
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj q ⟶ S.ordinaryProjectiveObj p) :
    P.projectiveOppositeHomLinearEquiv p q f =
      P.oppositeProjectiveFunctor.map f.op := by
  apply InducedCategory.hom_ext
  rfl

omit [IsNoetherianRing A] in
/-- The selected-projective anti-equivalence preserves and reflects the
categorical radical. -/
theorem projectiveOppositeHomLinearEquiv_mem_radical_iff
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj q ⟶ S.ordinaryProjectiveObj p) :
    P.projectiveOppositeHomLinearEquiv p q f ∈
        S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal.hom
          (S.contragredientSkeleton.ordinaryProjectiveObj
            (P.oppositeProjectiveCoordinate p))
          (S.contragredientSkeleton.ordinaryProjectiveObj
            (P.oppositeProjectiveCoordinate q)) ↔
      f ∈ S.projectiveNilpotentRadicalData.ideal.hom
        (S.ordinaryProjectiveObj q) (S.ordinaryProjectiveObj p) := by
  rw [S.projectiveNilpotentRadicalData.mem_ideal_iff,
    S.contragredientSkeleton.projectiveNilpotentRadicalData.mem_ideal_iff,
    P.projectiveOppositeHomLinearEquiv_apply]
  let F := P.oppositeProjectiveFunctor
  let hFF := P.oppositeProjectiveFunctorFullyFaithful
  exact (MagnitudeConjecture.isRadicalMorphism_iff_map_of_fullyFaithful
    F hFF f.op).symm.trans
      (MagnitudeConjecture.CoveringHom.isRadicalMorphism_op_iff f)

omit [IsNoetherianRing A] in
/-- The selected-projective anti-equivalence sends the square of the
projective radical into the opposite projective radical square. -/
theorem projectiveOppositeHomLinearEquiv_mem_radicalSquare_of_mem
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj q ⟶ S.ordinaryProjectiveObj p)
    (hf : f ∈ (S.projectiveNilpotentRadicalData.ideal.pow 2).hom
      (S.ordinaryProjectiveObj q) (S.ordinaryProjectiveObj p)) :
    P.projectiveOppositeHomLinearEquiv p q f ∈
      (S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal.pow 2).hom
        (S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate p))
        (S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate q)) := by
  let I := S.projectiveNilpotentRadicalData.ideal
  let J := S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal
  have hf' : f ∈ (I ⋆ᵢ I).hom
      (S.ordinaryProjectiveObj q) (S.ordinaryProjectiveObj p) := by
    simpa [I] using hf
  clear hf
  rw [show
    S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal.pow 2 =
      S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal ⋆ᵢ
        S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal by simp]
  change P.projectiveOppositeHomLinearEquiv p q f ∈
    (J ⋆ᵢ J).hom _ _
  induction hf' using AddSubgroup.closure_induction with
  | mem f hfgen =>
      obtain ⟨r, a, b, ha, hb, rfl⟩ := hfgen
      have ha' :=
        (P.projectiveOppositeHomLinearEquiv_mem_radical_iff a).2 ha
      have hb' :=
        (P.projectiveOppositeHomLinearEquiv_mem_radical_iff b).2 hb
      have hcomp : P.projectiveOppositeHomLinearEquiv p q (a ≫ b) =
          P.projectiveOppositeHomLinearEquiv p r b ≫
            P.projectiveOppositeHomLinearEquiv r q a := by
        simp only [P.projectiveOppositeHomLinearEquiv_apply]
        exact P.oppositeProjectiveFunctor.map_comp b.op a.op
      rw [hcomp]
      exact QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.comp_mem_mul
        hb' ha'
  | zero =>
      rw [map_zero]
      exact ((J ⋆ᵢ J).hom _ _).zero_mem
  | add f g _ _ hf hg =>
      rw [map_add]
      exact ((J ⋆ᵢ J).hom _ _).add_mem hf hg
  | neg f _ hf =>
      rw [map_neg]
      exact ((J ⋆ᵢ J).hom _ _).neg_mem hf

omit [IsNoetherianRing A] in
/-- Reflection of the radical square under the selected-projective
anti-equivalence. -/
theorem projectiveOppositeHomLinearEquiv_symm_mem_radicalSquare_of_mem
    {p q : S.ProjectiveLabel}
    (h : S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate p) ⟶
        S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate q))
    (hh : h ∈
      (S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal.pow 2).hom
        (S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate p))
        (S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate q))) :
    (P.projectiveOppositeHomLinearEquiv p q).symm h ∈
      (S.projectiveNilpotentRadicalData.ideal.pow 2).hom
        (S.ordinaryProjectiveObj q) (S.ordinaryProjectiveObj p) := by
  let I := S.projectiveNilpotentRadicalData.ideal
  let J := S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal
  have hh' : h ∈ (J ⋆ᵢ J).hom
      (S.contragredientSkeleton.ordinaryProjectiveObj
        (P.oppositeProjectiveCoordinate p))
      (S.contragredientSkeleton.ordinaryProjectiveObj
        (P.oppositeProjectiveCoordinate q)) := by
    simpa [J] using hh
  clear hh
  rw [show S.projectiveNilpotentRadicalData.ideal.pow 2 =
    S.projectiveNilpotentRadicalData.ideal ⋆ᵢ
      S.projectiveNilpotentRadicalData.ideal by simp]
  change (P.projectiveOppositeHomLinearEquiv p q).symm h ∈
    (I ⋆ᵢ I).hom _ _
  induction hh' using AddSubgroup.closure_induction with
  | mem h hgen =>
      obtain ⟨z, a, b, ha, hb, rfl⟩ := hgen
      obtain ⟨r, hr⟩ := P.oppositeProjectiveCoordinate_surjective
        (show S.contragredientSkeleton.ProjectiveLabel from z)
      let eZ : S.contragredientSkeleton.ordinaryProjectiveObj
          (P.oppositeProjectiveCoordinate r) ≅ z := eqToIso hr
      let a' := a ≫ eZ.inv
      let b' := eZ.hom ≫ b
      have ha' : a' ∈ J.hom
          (S.contragredientSkeleton.ordinaryProjectiveObj
            (P.oppositeProjectiveCoordinate p))
          (S.contragredientSkeleton.ordinaryProjectiveObj
            (P.oppositeProjectiveCoordinate r)) :=
        J.postcomp eZ.inv ha
      have hb' : b' ∈ J.hom
          (S.contragredientSkeleton.ordinaryProjectiveObj
            (P.oppositeProjectiveCoordinate r))
          (S.contragredientSkeleton.ordinaryProjectiveObj
            (P.oppositeProjectiveCoordinate q)) :=
        J.precomp eZ.hom hb
      let a₀ := (P.projectiveOppositeHomLinearEquiv p r).symm a'
      let b₀ := (P.projectiveOppositeHomLinearEquiv r q).symm b'
      have ha₀ : a₀ ∈ I.hom
          (S.ordinaryProjectiveObj r) (S.ordinaryProjectiveObj p) := by
        apply (P.projectiveOppositeHomLinearEquiv_mem_radical_iff a₀).1
        simpa [a₀] using ha'
      have hb₀ : b₀ ∈ I.hom
          (S.ordinaryProjectiveObj q) (S.ordinaryProjectiveObj r) := by
        apply (P.projectiveOppositeHomLinearEquiv_mem_radical_iff b₀).1
        simpa [b₀] using hb'
      have hmap : P.projectiveOppositeHomLinearEquiv p q (b₀ ≫ a₀) =
          a' ≫ b' := by
        calc
          P.projectiveOppositeHomLinearEquiv p q (b₀ ≫ a₀) =
              P.projectiveOppositeHomLinearEquiv p r a₀ ≫
                P.projectiveOppositeHomLinearEquiv r q b₀ := by
            simp only [P.projectiveOppositeHomLinearEquiv_apply]
            exact P.oppositeProjectiveFunctor.map_comp a₀.op b₀.op
          _ = a' ≫ b' := by simp [a₀, b₀]
      have hab : a' ≫ b' = a ≫ b := by
        simp [a', b', eZ, Category.assoc]
      have hinv : (P.projectiveOppositeHomLinearEquiv p q).symm (a ≫ b) =
          b₀ ≫ a₀ := by
        apply (P.projectiveOppositeHomLinearEquiv p q).injective
        rw [LinearEquiv.apply_symm_apply]
        rw [← hab]
        exact hmap.symm
      rw [hinv]
      exact QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.comp_mem_mul
        hb₀ ha₀
  | zero =>
      rw [map_zero]
      exact ((I ⋆ᵢ I).hom _ _).zero_mem
  | add f g _ _ hf hg =>
      rw [map_add]
      exact ((I ⋆ᵢ I).hom _ _).add_mem hf hg
  | neg f _ hf =>
      rw [map_neg]
      exact ((I ⋆ᵢ I).hom _ _).neg_mem hf

/-- Restriction of the selected-projective anti-equivalence to radical Hom
spaces. -/
def projectiveRadicalOppositeLinearEquiv (p q : S.ProjectiveLabel) :
    S.projectiveRadicalSubmodule p q ≃ₗ[k]
      S.contragredientSkeleton.projectiveRadicalSubmodule
        (P.oppositeProjectiveCoordinate q)
        (P.oppositeProjectiveCoordinate p) where
  toFun f := ⟨P.projectiveOppositeHomLinearEquiv p q f.1,
    (P.projectiveOppositeHomLinearEquiv_mem_radical_iff f.1).2 f.2⟩
  invFun h := ⟨(P.projectiveOppositeHomLinearEquiv p q).symm h.1, by
    apply (P.projectiveOppositeHomLinearEquiv_mem_radical_iff
      ((P.projectiveOppositeHomLinearEquiv p q).symm h.1)).1
    rw [(P.projectiveOppositeHomLinearEquiv p q).apply_symm_apply]
    exact h.2⟩
  left_inv f := by
    apply Subtype.ext
    change (P.projectiveOppositeHomLinearEquiv p q).symm
        (P.projectiveOppositeHomLinearEquiv p q f.1) = f.1
    exact (P.projectiveOppositeHomLinearEquiv p q).symm_apply_apply f.1
  right_inv h := by
    apply Subtype.ext
    change P.projectiveOppositeHomLinearEquiv p q
        ((P.projectiveOppositeHomLinearEquiv p q).symm h.1) = h.1
    exact (P.projectiveOppositeHomLinearEquiv p q).apply_symm_apply h.1
  map_add' f g := by
    apply Subtype.ext
    exact (P.projectiveOppositeHomLinearEquiv p q).map_add f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact (P.projectiveOppositeHomLinearEquiv p q).map_smul c f.1

omit [IsNoetherianRing A] in
/-- The radical anti-equivalence carries the square-inside-radical
submodule onto the corresponding opposite submodule. -/
theorem projectiveRadicalOppositeLinearEquiv_mem_square_iff
    (p q : S.ProjectiveLabel)
    (f : S.projectiveRadicalSubmodule p q) :
    P.projectiveRadicalOppositeLinearEquiv p q f ∈
        S.contragredientSkeleton.projectiveRadicalSquareInRadicalSubmodule
          (P.oppositeProjectiveCoordinate q)
          (P.oppositeProjectiveCoordinate p) ↔
      f ∈ S.projectiveRadicalSquareInRadicalSubmodule p q := by
  constructor
  · intro hf
    change (P.projectiveOppositeHomLinearEquiv p q f.1) ∈
      (S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal.pow 2).hom
        _ _ at hf
    change f.1 ∈ (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _
    have hsymm :=
      P.projectiveOppositeHomLinearEquiv_symm_mem_radicalSquare_of_mem
        (P.projectiveOppositeHomLinearEquiv p q f.1) hf
    change (P.projectiveOppositeHomLinearEquiv p q).symm
        (P.projectiveOppositeHomLinearEquiv p q f.1) ∈
      (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _ at hsymm
    rw [(P.projectiveOppositeHomLinearEquiv p q).symm_apply_apply] at hsymm
    exact hsymm
  · intro hf
    change f.1 ∈ (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _ at hf
    change (P.projectiveOppositeHomLinearEquiv p q f.1) ∈
      (S.contragredientSkeleton.projectiveNilpotentRadicalData.ideal.pow 2).hom
        _ _
    exact P.projectiveOppositeHomLinearEquiv_mem_radicalSquare_of_mem f.1 hf

/-- Regular Hom-duality descends from radical morphisms to irreducible
projective morphisms. -/
def projectiveIrreducibleOppositeLinearEquiv (p q : S.ProjectiveLabel) :
    S.projectiveIrreducibleHomSpace p q ≃ₗ[k]
      S.contragredientSkeleton.projectiveIrreducibleHomSpace
        (P.oppositeProjectiveCoordinate q)
        (P.oppositeProjectiveCoordinate p) :=
  Submodule.Quotient.equiv
    (S.projectiveRadicalSquareInRadicalSubmodule p q)
    (S.contragredientSkeleton.projectiveRadicalSquareInRadicalSubmodule
      (P.oppositeProjectiveCoordinate q)
      (P.oppositeProjectiveCoordinate p))
    (P.projectiveRadicalOppositeLinearEquiv p q) (by
      apply le_antisymm
      · rintro _ ⟨f, hf, rfl⟩
        exact (P.projectiveRadicalOppositeLinearEquiv_mem_square_iff p q f).2 hf
      · intro h hh
        refine ⟨(P.projectiveRadicalOppositeLinearEquiv p q).symm h, ?_, ?_⟩
        · apply (P.projectiveRadicalOppositeLinearEquiv_mem_square_iff p q
            ((P.projectiveRadicalOppositeLinearEquiv p q).symm h)).1
          simpa using hh
        · exact (P.projectiveRadicalOppositeLinearEquiv p q).apply_symm_apply h)

omit [IsNoetherianRing A] in
/-- Opposite regular Hom-duality preserves the dimensions of irreducible
projective-morphism spaces, with source and target reversed. -/
theorem finrank_projectiveIrreducibleHomSpace_eq_opposite
    (p q : S.ProjectiveLabel) :
    Module.finrank k (S.projectiveIrreducibleHomSpace p q) =
      Module.finrank k
        (S.contragredientSkeleton.projectiveIrreducibleHomSpace
          (P.oppositeProjectiveCoordinate q)
          (P.oppositeProjectiveCoordinate p)) :=
  (P.projectiveIrreducibleOppositeLinearEquiv p q).finrank_eq

omit [IsNoetherianRing A] in
/-- The incoming ordinary-quiver degree over the original algebra is the
outgoing degree at the corresponding projective over the opposite algebra. -/
theorem ordinaryCostar_card_eq_oppositeStar_card
    (x : S.ProjectiveLabel) :
    Nat.card (Quiver.Costar x) =
      Nat.card (Quiver.Star (P.oppositeProjectiveCoordinate x)) := by
  rw [S.ordinaryCostar_card_eq_sum_finrank,
    S.contragredientSkeleton.ordinaryStar_card_eq_sum_finrank]
  calc
    (∑ y : S.ProjectiveLabel,
        Module.finrank k (S.projectiveIrreducibleHomSpace y x)) =
        ∑ y : S.ProjectiveLabel,
          Module.finrank k
            (S.contragredientSkeleton.projectiveIrreducibleHomSpace
              (P.oppositeProjectiveCoordinate x)
              (P.oppositeProjectiveCoordinate y)) := by
          apply Finset.sum_congr rfl
          intro y _
          exact P.finrank_projectiveIrreducibleHomSpace_eq_opposite y x
    _ = ∑ z : S.contragredientSkeleton.ProjectiveLabel,
          Module.finrank k
            (S.contragredientSkeleton.projectiveIrreducibleHomSpace
              (P.oppositeProjectiveCoordinate x) z) :=
      by
        convert P.oppositeProjectiveEquiv.sum_comp
            (fun z : S.contragredientSkeleton.ProjectiveLabel ↦
              Module.finrank k
                (S.contragredientSkeleton.projectiveIrreducibleHomSpace
                  (P.oppositeProjectiveCoordinate x) z)) using 1
        all_goals simp [oppositeProjectiveEquiv]
        apply Finset.sum_congr
        · ext y
          simp
        · intro y _
          rfl

/-- Biseriality bounds the incoming as well as the outgoing ordinary-quiver
degree at every selected projective. -/
theorem ordinaryCostar_card_le_two_of_isBiserial
    [IsAlgClosed k] (hP : P.IsBiserial) (x : S.ProjectiveLabel) :
    Nat.card (Quiver.Costar x) ≤ 2 := by
  rw [P.ordinaryCostar_card_eq_oppositeStar_card x]
  exact S.contragredientSkeleton
    |>.ordinaryStar_card_le_two_of_primitiveProjectivePresentation_isBiserial
      P.oppositePresentation (P.oppositePresentation_isBiserial hP)
        (P.oppositeProjectiveCoordinate x)

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
