import MagnitudeConjecture.CategoryTheory.RightFreydCokernel
import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# Kernel duality on epimorphic right-Freyd presentations

For an epimorphism `g : B ⟶ C` in an abelian category, its kernel inclusion
`ker(g) ⟶ B` becomes an epimorphism in the opposite category.  A square of
epimorphisms induces a square of the opposite kernel inclusions in the
reverse direction.  Right homotopies are carried to right homotopies, so the
construction descends to right Freyd categories.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Preadditive.RightFreyd

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Right-Freyd objects represented by epimorphisms. -/
def IsEpiArrow : ObjectProperty (Preadditive.RightFreyd C) :=
  fun X ↦ Epi X.as.hom

/-- The full subcategory of the right Freyd category on epimorphic
presentations. -/
abbrev EpiCategory := (IsEpiArrow C).FullSubcategory

variable {C}

/-- The map between kernels induced by a square of arrows. -/
def kernelMap {a b : Arrow C} (s : b ⟶ a) :
    kernel b.hom ⟶ kernel a.hom :=
  kernel.lift a.hom (kernel.ι b.hom ≫ s.left) (by
    rw [Category.assoc, s.w, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
theorem kernelMap_comp_ι {a b : Arrow C} (s : b ⟶ a) :
    kernelMap s ≫ kernel.ι a.hom = kernel.ι b.hom ≫ s.left :=
  kernel.lift_ι _ _ _

@[simp]
theorem kernelMap_id (a : Arrow C) :
    kernelMap (𝟙 a) = 𝟙 (kernel a.hom) := by
  apply (cancel_mono (kernel.ι a.hom)).1
  simp

@[simp]
theorem kernelMap_comp {a b c : Arrow C} (s : c ⟶ b) (t : b ⟶ a) :
    kernelMap (s ≫ t) = kernelMap s ≫ kernelMap t := by
  apply (cancel_mono (kernel.ι a.hom)).1
  simp

/-- A square `b ⟶ a` gives a reversed square between the opposite kernel
inclusions. -/
def kernelOpMapRepresentative {a b : Arrow C} (s : b ⟶ a) :
    Arrow.mk (kernel.ι a.hom).op ⟶ Arrow.mk (kernel.ι b.hom).op :=
  Arrow.homMk s.left.op (kernelMap s).op (by
    apply Quiver.Hom.unop_inj
    change kernel.ι b.hom ≫ s.left = kernelMap s ≫ kernel.ι a.hom
    exact (kernelMap_comp_ι s).symm)

@[simp]
theorem kernelOpMapRepresentative_id (a : Arrow C) :
    kernelOpMapRepresentative (𝟙 a) =
      𝟙 (Arrow.mk (kernel.ι a.hom).op) := by
  ext <;> simp [kernelOpMapRepresentative]

@[simp]
theorem kernelOpMapRepresentative_comp
    {a b c : Arrow C} (s : c ⟶ b) (t : b ⟶ a) :
    kernelOpMapRepresentative (s ≫ t) =
      kernelOpMapRepresentative t ≫ kernelOpMapRepresentative s := by
  ext <;> simp [kernelOpMapRepresentative]

/-- Right-homotopic squares induce right-homotopic reversed kernel
squares. -/
def kernelOpRightHomotopy {a b : Arrow C} (s t : b ⟶ a)
    (H : Arrow.RightHomotopy s t) :
    Arrow.RightHomotopy
      (kernelOpMapRepresentative s) (kernelOpMapRepresentative t) := by
  let d : b.left ⟶ kernel a.hom :=
    kernel.lift a.hom
      (s.left - t.left - b.hom ≫ H.hom) (by
        rw [Preadditive.sub_comp, Preadditive.sub_comp,
          s.w, t.w, Category.assoc, ← Preadditive.comp_sub, H.comm,
          sub_self])
  refine
    { hom := d.op
      comm := ?_ }
  apply Quiver.Hom.unop_inj
  simp only [kernelOpMapRepresentative, Arrow.homMk_right, unop_sub,
    Quiver.Hom.unop_op, unop_comp]
  change kernelMap s - kernelMap t = kernel.ι b.hom ≫ d
  apply (cancel_mono (kernel.ι a.hom)).1
  rw [Preadditive.sub_comp, kernelMap_comp_ι, kernelMap_comp_ι,
    Category.assoc]
  simp only [d, kernel.lift_ι]
  simp only [Preadditive.comp_sub, Category.assoc, kernel.condition,
    zero_comp, sub_zero]
  rw [← Category.assoc, kernel.condition, zero_comp, sub_zero]

/-- Taking the opposite kernel inclusion descends to a contravariant functor
between the epimorphic parts of the two right Freyd categories. -/
def kernelOp : (EpiCategory C)ᵒᵖ ⥤ EpiCategory Cᵒᵖ where
  obj X := by
    let a := X.unop.obj.as
    exact ⟨(Preadditive.RightFreyd.quotient Cᵒᵖ).obj
      (Arrow.mk (kernel.ι a.hom).op), by
        change Epi (kernel.ι a.hom).op
        infer_instance⟩
  map {X Y} f := by
    let q := Preadditive.RightFreyd.quotient C
    let s : Y.unop.obj.as ⟶ X.unop.obj.as := q.preimage f.unop.hom
    exact ObjectProperty.homMk
      ((Preadditive.RightFreyd.quotient Cᵒᵖ).map
        (kernelOpMapRepresentative s))
  map_id X := by
    apply ObjectProperty.hom_ext
    let q := Preadditive.RightFreyd.quotient C
    let qop := Preadditive.RightFreyd.quotient Cᵒᵖ
    let s : X.unop.obj.as ⟶ X.unop.obj.as :=
      q.preimage (𝟙 X).unop.hom
    change qop.map (kernelOpMapRepresentative s) = 𝟙 _
    have hq : q.map s = q.map (𝟙 X.unop.obj.as) := by
      have hpre := q.map_preimage (𝟙 X).unop.hom
      change q.map s = 𝟙 X.unop.obj at hpre
      rw [q.map_id]
      exact hpre
    apply Preadditive.RightFreyd.eq_of_rightHomotopy
    have hs : Arrow.RightHomotopy s (𝟙 X.unop.obj.as) :=
      Preadditive.RightFreyd.homotopyOfEq _ _ hq
    exact (kernelOpRightHomotopy s (𝟙 X.unop.obj.as) hs).trans
      (Arrow.RightHomotopy.ofEq (kernelOpMapRepresentative_id _))
  map_comp {X Y Z} f g := by
    apply ObjectProperty.hom_ext
    let q := Preadditive.RightFreyd.quotient C
    let qop := Preadditive.RightFreyd.quotient Cᵒᵖ
    let sf : Y.unop.obj.as ⟶ X.unop.obj.as := q.preimage f.unop.hom
    let sg : Z.unop.obj.as ⟶ Y.unop.obj.as := q.preimage g.unop.hom
    let sfg : Z.unop.obj.as ⟶ X.unop.obj.as :=
      q.preimage (f ≫ g).unop.hom
    change qop.map (kernelOpMapRepresentative sfg) =
      qop.map (kernelOpMapRepresentative sf) ≫
        qop.map (kernelOpMapRepresentative sg)
    rw [← qop.map_comp, ← kernelOpMapRepresentative_comp]
    apply Preadditive.RightFreyd.eq_of_rightHomotopy
    have hpre := q.map_preimage (f ≫ g).unop.hom
    change q.map sfg = g.unop.hom ≫ f.unop.hom at hpre
    have hsf := q.map_preimage f.unop.hom
    have hsg := q.map_preimage g.unop.hom
    change q.map sf = f.unop.hom at hsf
    change q.map sg = g.unop.hom at hsg
    have hs : Arrow.RightHomotopy sfg (sg ≫ sf) :=
      Preadditive.RightFreyd.homotopyOfEq _ _ (by
        rw [q.map_comp, hpre, hsg, hsf]
        rfl)
    exact kernelOpRightHomotopy sfg (sg ≫ sf) hs

/-- For epimorphic presentations, a right homotopy between the reversed
kernel squares comes from a right homotopy between the original squares. -/
def rightHomotopyOfKernelOpRightHomotopy
    {a b : Arrow C} [Epi b.hom] (s t : b ⟶ a)
    (H : Arrow.RightHomotopy
      (kernelOpMapRepresentative s) (kernelOpMapRepresentative t)) :
    Arrow.RightHomotopy s t := by
  let d : b.left ⟶ kernel a.hom := H.hom.unop
  have hkernelMap : kernelMap s - kernelMap t = kernel.ι b.hom ≫ d := by
    have h := congrArg Quiver.Hom.unop H.comm
    change kernelMap s - kernelMap t = kernel.ι b.hom ≫ d at h
    exact h
  let z : b.left ⟶ a.left := s.left - t.left - d ≫ kernel.ι a.hom
  have hz : kernel.ι b.hom ≫ z = 0 := by
    calc
      kernel.ι b.hom ≫ z =
          kernel.ι b.hom ≫ (s.left - t.left) -
            kernel.ι b.hom ≫ (d ≫ kernel.ι a.hom) := by
        simp only [z, Preadditive.comp_sub]
      _ = (kernel.ι b.hom ≫ s.left - kernel.ι b.hom ≫ t.left) -
            (kernel.ι b.hom ≫ d) ≫ kernel.ι a.hom := by
        rw [Preadditive.comp_sub, Category.assoc]
      _ = ((kernelMap s - kernelMap t) ≫ kernel.ι a.hom) -
            (kernel.ι b.hom ≫ d) ≫ kernel.ι a.hom := by
        rw [Preadditive.sub_comp, kernelMap_comp_ι, kernelMap_comp_ι]
      _ = 0 := by rw [hkernelMap, sub_self]
  let h : b.right ⟶ a.left := Abelian.epiDesc b.hom z hz
  refine
    { hom := h
      comm := ?_ }
  apply (cancel_epi b.hom).1
  rw [Preadditive.comp_sub, ← s.w, ← t.w, ← Category.assoc]
  simp only [h, Abelian.comp_epiDesc]
  dsimp only [z]
  rw [Preadditive.sub_comp, Preadditive.sub_comp, Category.assoc,
    kernel.condition, comp_zero, sub_zero]

/-- Kernel reversal is faithful on epimorphic right-Freyd presentations. -/
noncomputable instance kernelOp_faithful : (kernelOp (C := C)).Faithful where
  map_injective {X Y} f g hfg := by
    let q := Preadditive.RightFreyd.quotient C
    let qop := Preadditive.RightFreyd.quotient Cᵒᵖ
    let a := X.unop.obj.as
    let b := Y.unop.obj.as
    let sf : b ⟶ a := q.preimage f.unop.hom
    let sg : b ⟶ a := q.preimage g.unop.hom
    letI : Epi b.hom := Y.unop.property
    have hqop : qop.map (kernelOpMapRepresentative sf) =
        qop.map (kernelOpMapRepresentative sg) := by
      have h := congrArg (fun z ↦ z.hom) hfg
      change qop.map (kernelOpMapRepresentative sf) =
        qop.map (kernelOpMapRepresentative sg) at h
      exact h
    let H : Arrow.RightHomotopy
        (kernelOpMapRepresentative sf) (kernelOpMapRepresentative sg) :=
      Preadditive.RightFreyd.homotopyOfEq _ _ hqop
    have hs : q.map sf = q.map sg :=
      Preadditive.RightFreyd.eq_of_rightHomotopy _ _
        (rightHomotopyOfKernelOpRightHomotopy sf sg H)
    have hsf := q.map_preimage f.unop.hom
    have hsg := q.map_preimage g.unop.hom
    change q.map sf = f.unop.hom at hsf
    change q.map sg = g.unop.hom at hsg
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact hsf.symm.trans (hs.trans hsg)

/-- Kernel reversal is full on epimorphic right-Freyd presentations. -/
noncomputable instance kernelOp_full : (kernelOp (C := C)).Full where
  map_surjective {X Y} m := by
    let q := Preadditive.RightFreyd.quotient C
    let qop := Preadditive.RightFreyd.quotient Cᵒᵖ
    let a := X.unop.obj.as
    let b := Y.unop.obj.as
    letI : Epi b.hom := Y.unop.property
    let r : Arrow.mk (kernel.ι a.hom).op ⟶
        Arrow.mk (kernel.ι b.hom).op := qop.preimage m.hom
    let u : b.left ⟶ a.left := r.left.unop
    let v : kernel b.hom ⟶ kernel a.hom := r.right.unop
    have huv : kernel.ι b.hom ≫ u = v ≫ kernel.ι a.hom := by
      have h := congrArg Quiver.Hom.unop r.w
      change kernel.ι b.hom ≫ u = v ≫ kernel.ι a.hom at h
      exact h
    have hzero : kernel.ι b.hom ≫ (u ≫ a.hom) = 0 := by
      rw [← Category.assoc, huv, Category.assoc, kernel.condition,
        comp_zero]
    let w : b.right ⟶ a.right :=
      Abelian.epiDesc b.hom (u ≫ a.hom) hzero
    let s : b ⟶ a := Arrow.homMk u w (by
      exact (Abelian.comp_epiDesc b.hom (u ≫ a.hom) hzero).symm)
    let f : X ⟶ Y :=
      (ObjectProperty.homMk (q.map s) : Y.unop ⟶ X.unop).op
    refine ⟨f, ?_⟩
    apply ObjectProperty.hom_ext
    let sf : b ⟶ a := q.preimage f.unop.hom
    have hsource : q.map sf = q.map s := by
      have hpre := q.map_preimage f.unop.hom
      change q.map sf = q.map s at hpre
      exact hpre
    let Hsource : Arrow.RightHomotopy sf s :=
      Preadditive.RightFreyd.homotopyOfEq _ _ hsource
    have hkernel : kernelMap s = v := by
      apply (cancel_mono (kernel.ι a.hom)).1
      rw [kernelMap_comp_ι]
      exact huv
    have hrepresentative : kernelOpMapRepresentative s = r := by
      ext
      · apply Quiver.Hom.unop_inj
        rfl
      · apply Quiver.Hom.unop_inj
        exact hkernel
    change qop.map (kernelOpMapRepresentative sf) = m.hom
    have hfirst : qop.map (kernelOpMapRepresentative sf) =
        qop.map (kernelOpMapRepresentative s) :=
      Preadditive.RightFreyd.eq_of_rightHomotopy _ _
        (kernelOpRightHomotopy sf s Hsource)
    have hr := qop.map_preimage m.hom
    change qop.map r = m.hom at hr
    rw [hfirst, hrepresentative, hr]

/-- Every epimorphic presentation in the opposite category is, up to
isomorphism, the opposite kernel presentation of an epimorphism. -/
noncomputable instance kernelOp_essSurj : (kernelOp (C := C)).EssSurj where
  mem_essImage X := by
    let q := Preadditive.RightFreyd.quotient C
    let qop := Preadditive.RightFreyd.quotient Cᵒᵖ
    let a := X.obj.as
    letI : Epi a.hom := X.property
    let i : a.right.unop ⟶ a.left.unop := a.hom.unop
    letI : Mono i := by
      dsimp only [i]
      infer_instance
    let g : a.left.unop ⟶ cokernel i := cokernel.π i
    let b : Arrow C := Arrow.mk g
    letI : Epi g := by
      dsimp only [g]
      infer_instance
    letI : Epi b.hom := by
      change Epi g
      infer_instance
    let B : EpiCategory C :=
      ⟨q.obj b, show Epi b.hom from inferInstance⟩
    let hKernel : IsLimit
        (KernelFork.ofι i (cokernel.condition i)) :=
      Abelian.monoIsKernelOfCokernel
        (CokernelCofork.ofπ (cokernel.π i) (cokernel.condition i))
        (cokernelIsCokernel i)
    let eK : kernel g ≅ a.right.unop :=
      IsLimit.conePointUniqueUpToIso (kernelIsKernel g) hKernel
    let eLeft : Opposite.op a.left.unop ≅ a.left :=
      eqToIso (Opposite.op_unop a.left)
    let eRight : Opposite.op (kernel g) ≅ a.right :=
      eK.symm.op ≪≫ eqToIso (Opposite.op_unop a.right)
    have heK : eK.inv ≫ kernel.ι g = i := by
      have h := IsLimit.conePointUniqueUpToIso_inv_comp
        (kernelIsKernel g) hKernel WalkingParallelPair.zero
      change eK.inv ≫ kernel.ι g = i at h
      exact h
    let eArrow : Arrow.mk (kernel.ι g).op ≅ a :=
      Arrow.isoMk eLeft eRight (by
        apply Quiver.Hom.unop_inj
        change a.hom.unop ≫ eLeft.hom.unop =
          eRight.hom.unop ≫ kernel.ι g
        simpa [eLeft, eRight, i] using heK.symm)
    refine ⟨Opposite.op B, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ (qop.mapIso eArrow)

noncomputable instance kernelOp_isEquivalence :
    (kernelOp (C := C)).IsEquivalence := {}

/-- The anti-equivalence between epimorphic presentations and opposite
kernel presentations. -/
def kernelOpEquivalence : (EpiCategory C)ᵒᵖ ≌ EpiCategory Cᵒᵖ :=
  (kernelOp (C := C)).asEquivalence

end CategoryTheory.Preadditive.RightFreyd
