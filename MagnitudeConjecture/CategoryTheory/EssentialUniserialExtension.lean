import MagnitudeConjecture.CategoryTheory.InjectiveEnvelope
import MagnitudeConjecture.CategoryTheory.UniserialObject
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Uniserial essential extensions

A simple essential subobject is contained in every nonzero subobject.  Hence,
if the quotient by that subobject is uniserial, the whole object is
uniserial.  This is the categorical induction step for an ascending socle
series.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem compSquare_isPullback
    {R H G : C} (r : R ⟶ H) [Mono r] (l : H ⟶ G) [Mono l] :
    IsPullback r (𝟙 R) l (r ≫ l) :=
  IsPullback.of_vert_isIso_mono ⟨by
    simp only [Category.id_comp]⟩

/-- The inclusion of the first quotient in the quotient by a composite
monomorphism. -/
noncomputable def cokernelInclusionOfComp
    {R H G : C} (r : R ⟶ H) [Mono r] (l : H ⟶ G) [Mono l] :
    cokernel r ⟶ cokernel (r ≫ l) :=
  cokernel.map r (r ≫ l) (𝟙 R) l (compSquare_isPullback r l).w

instance cokernelInclusionOfComp_mono
    {R H G : C} (r : R ⟶ H) [Mono r] (l : H ⟶ G) [Mono l] :
    Mono (cokernelInclusionOfComp r l) :=
  Abelian.mono_cokernel_map_of_isPullback (compSquare_isPullback r l)

@[reassoc]
theorem cokernel_π_comp_cokernelInclusionOfComp
    {R H G : C} (r : R ⟶ H) [Mono r] (l : H ⟶ G) [Mono l] :
    cokernel.π r ≫ cokernelInclusionOfComp r l =
      l ≫ cokernel.π (r ≫ l) := by
  exact cokernel.π_desc _ _ _

/-- Collapsing the two successive quotients by `R ⊆ H` gives the direct
quotient by `H`. -/
noncomputable def cokernelTowerDesc
    {R H G : C} (r : R ⟶ H) [Mono r] (l : H ⟶ G) [Mono l] :
    cokernel (cokernelInclusionOfComp r l) ⟶ cokernel l := by
  let q : cokernel (r ≫ l) ⟶ cokernel l :=
    cokernel.desc (r ≫ l) (cokernel.π l) (by simp)
  apply cokernel.desc (cokernelInclusionOfComp r l) q
  apply (cancel_epi (cokernel.π r)).1
  calc
    cokernel.π r ≫ (cokernelInclusionOfComp r l ≫ q) =
        (cokernel.π r ≫ cokernelInclusionOfComp r l) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = (l ≫ cokernel.π (r ≫ l)) ≫ q := by
      rw [cokernel_π_comp_cokernelInclusionOfComp]
    _ = l ≫ (cokernel.π (r ≫ l) ≫ q) := Category.assoc _ _ _
    _ = l ≫ cokernel.π l := by
      dsimp only [q]
      rw [cokernel.π_desc]
    _ = 0 := cokernel.condition l
    _ = cokernel.π r ≫ 0 := by rw [comp_zero]

@[reassoc]
theorem cokernel_π_comp_cokernel_π_comp_cokernelTowerDesc
    {R H G : C} (r : R ⟶ H) [Mono r] (l : H ⟶ G) [Mono l] :
    cokernel.π (r ≫ l) ≫
        cokernel.π (cokernelInclusionOfComp r l) ≫
          cokernelTowerDesc r l =
      cokernel.π l := by
  dsimp only [cokernelTowerDesc]
  simp

/-- Equality after the two successive quotients by `R ⊆ H` descends to
equality after the direct quotient by `H`. -/
theorem comp_cokernel_π_eq_of_comp_cokernelTower_eq
    {R H G P : C} (r : R ⟶ H) [Mono r] (l : H ⟶ G) [Mono l]
    (f g : P ⟶ G)
    (h : (f ≫ cokernel.π (r ≫ l)) ≫
          cokernel.π (cokernelInclusionOfComp r l) =
        (g ≫ cokernel.π (r ≫ l)) ≫
          cokernel.π (cokernelInclusionOfComp r l)) :
    f ≫ cokernel.π l = g ≫ cokernel.π l := by
  have hw := congrArg
    (fun z ↦ z ≫ cokernelTowerDesc r l) h
  simpa only [Category.assoc,
    cokernel_π_comp_cokernel_π_comp_cokernelTowerDesc] using hw

/-- The quotient map commutes with the canonical transport between cokernels
of equal morphisms. -/
@[reassoc]
theorem cokernel_π_comp_eqToIso_of_eq
    {X Y : C} {f g : X ⟶ Y} (h : f = g) :
    cokernel.π f ≫
        (eqToIso (congrArg (fun q : X ⟶ Y ↦ cokernel q) h)).hom =
      cokernel.π g := by
  subst g
  simp

namespace IsUniserialObject

/-- A subobject is a waist when it is comparable with every subobject of the
ambient object.  Successive terms of an ascending uniserial socle series have
this stronger ambient property. -/
def IsWaistSubobject {X : C} (P : Subobject X) : Prop :=
  ∀ Q : Subobject X, P ≤ Q ∨ Q ≤ P

/-- Essentiality is unchanged by composing the target with an isomorphism. -/
theorem isEssentialMono_of_comp_iso
    {X Y Z : C} (f : X ⟶ Y) (e : Y ≅ Z)
    (h : IsEssentialMono (f ≫ e.hom)) : IsEssentialMono f := by
  constructor
  · letI : Mono (f ≫ e.hom) := h.1
    exact mono_of_mono f e.hom
  · intro W q hfq
    let q' : Z ⟶ W := e.inv ≫ q
    have hcomp : Mono ((f ≫ e.hom) ≫ q') := by
      rw [Category.assoc]
      dsimp only [q']
      simpa only [← Category.assoc, e.hom_inv_id_assoc] using hfq
    have hq' : Mono q' := h.2 q' hcomp
    constructor
    intro V a b hab
    apply (cancel_mono e.hom).1
    apply (cancel_mono q').1
    dsimp only [q']
    simp only [Category.assoc, e.hom_inv_id_assoc, hab]

/-- A simple object is uniserial. -/
theorem of_simple (X : C) [Simple X] : IsUniserialObject X := by
  constructor
  intro P Q
  rcases IsSimpleOrder.eq_bot_or_eq_top P with hP | hP
  · left
    simpa only [hP] using (bot_le : (⊥ : Subobject X) ≤ Q)
  · right
    simpa only [hP] using (le_top : Q ≤ (⊤ : Subobject X))

/-- A nonzero subobject of an essential extension of a simple object contains
that simple subobject. -/
theorem simple_le_nonzero_subobject_of_essential
    {L X : C} [Simple L] (l : L ⟶ X) [Mono l]
    (hl : IsEssentialMono l)
    (P : Subobject X) (hP : P ≠ ⊥) :
    Subobject.mk l ≤ P := by
  have hlP : l ≫ cokernel.π P.arrow = 0 := by
    by_contra hne
    letI : Mono (l ≫ cokernel.π P.arrow) :=
      mono_of_nonzero_from_simple hne
    letI : Mono (cokernel.π P.arrow) :=
      hl.2 (cokernel.π P.arrow) inferInstance
    have hParrow : P.arrow = 0 := by
      apply (cancel_mono (cokernel.π P.arrow)).1
      rw [cokernel.condition, zero_comp]
    apply hP
    rw [← P.mk_arrow, Subobject.mk_eq_bot_iff_zero]
    exact hParrow
  let a : L ⟶ (P : C) := Abelian.monoLift P.arrow l hlP
  simpa only [P.mk_arrow] using
    (Subobject.mk_le_mk_of_comm a
      (Abelian.monoLift_comp P.arrow l hlP))

/-- A simple essential subobject is a waist in its ambient object. -/
theorem isWaistSubobject_of_simple_essential
    {L X : C} [Simple L] (l : L ⟶ X) [Mono l]
    (hl : IsEssentialMono l) :
    IsWaistSubobject (Subobject.mk l) := by
  intro P
  by_cases hP : P = ⊥
  · exact Or.inr (by simpa only [hP] using
      (bot_le : (⊥ : Subobject X) ≤ Subobject.mk l))
  · exact Or.inl (simple_le_nonzero_subobject_of_essential l hl P hP)

/-- A waist remains a waist after adjoining a simple layer which is essential
in the quotient by the old waist.  This is the abstract propagation step for
an ascending uniserial socle series. -/
theorem isWaistSubobject_of_essentialSimpleTop
    {R H X : C} (r : R ⟶ H) [Mono r] (m : H ⟶ X) [Mono m]
    (hR : IsWaistSubobject (Subobject.mk (r ≫ m)))
    [Simple (cokernel r)]
    (ht : IsEssentialMono (cokernelInclusionOfComp r m)) :
    IsWaistSubobject (Subobject.mk m) := by
  intro P
  by_cases hPH : P ≤ Subobject.mk m
  · exact Or.inr hPH
  have hnle : Subobject.mk (r ≫ m) ≤ Subobject.mk m :=
    Subobject.mk_le_mk_of_comm r rfl
  have hRP : Subobject.mk (r ≫ m) ≤ P :=
    (hR P).resolve_right (fun hPR ↦ hPH (hPR.trans hnle))
  have hRP' : Subobject.mk (r ≫ m) ≤ Subobject.mk P.arrow := by
    simpa only [P.mk_arrow] using hRP
  let a : R ⟶ (P : C) := Subobject.ofMkLEMk (r ≫ m) P.arrow hRP'
  have ha : a ≫ P.arrow = r ≫ m := Subobject.ofMkLEMk_comp hRP'
  have sq : IsPullback a (𝟙 R) P.arrow (r ≫ m) :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [ha, Category.id_comp]⟩
  let pbar : cokernel a ⟶ cokernel (r ≫ m) :=
    cokernel.map a (r ≫ m) (𝟙 R) P.arrow sq.w
  letI : Mono pbar := Abelian.mono_cokernel_map_of_isPullback sq
  have hpbar : cokernel.π a ≫ pbar =
      P.arrow ≫ cokernel.π (r ≫ m) := cokernel.π_desc _ _ _
  have hpbarne : pbar ≠ 0 := by
    intro hpbarzero
    apply hPH
    have hPπn : P.arrow ≫ cokernel.π (r ≫ m) = 0 := by
      rw [← hpbar, hpbarzero, comp_zero]
    have hPπm : P.arrow ≫ cokernel.π m = 0 := by
      rw [← cokernel_π_comp_cokernel_π_comp_cokernelTowerDesc r m,
        ← Category.assoc, hPπn, zero_comp]
    let b : (P : C) ⟶ H := Abelian.monoLift m P.arrow hPπm
    simpa only [P.mk_arrow] using
      (Subobject.mk_le_mk_of_comm b
        (Abelian.monoLift_comp m P.arrow hPπm))
  let t := cokernelInclusionOfComp r m
  have htP : Subobject.mk t ≤ Subobject.mk pbar :=
    simple_le_nonzero_subobject_of_essential t ht (Subobject.mk pbar)
      (fun hbot ↦ hpbarne (Subobject.mk_eq_bot_iff_zero.mp hbot))
  let k : cokernel r ⟶ cokernel a :=
    Subobject.ofMkLEMk t pbar htP
  have hk : k ≫ pbar = t := Subobject.ofMkLEMk_comp htP
  have hnPπ : (r ≫ m) ≫ cokernel.π P.arrow = 0 := by
    rw [← ha, Category.assoc, cokernel.condition, comp_zero]
  let w : cokernel (r ≫ m) ⟶ cokernel P.arrow :=
    cokernel.desc (r ≫ m) (cokernel.π P.arrow) hnPπ
  have hpbarw : pbar ≫ w = 0 := by
    apply (cancel_epi (cokernel.π a)).1
    calc
      cokernel.π a ≫ (pbar ≫ w) =
          (P.arrow ≫ cokernel.π (r ≫ m)) ≫ w := by
        rw [← Category.assoc, hpbar]
      _ = P.arrow ≫ cokernel.π P.arrow := by
        dsimp only [w]
        rw [Category.assoc, cokernel.π_desc]
      _ = 0 := cokernel.condition P.arrow
      _ = cokernel.π a ≫ 0 := by rw [comp_zero]
  have hmPπ : m ≫ cokernel.π P.arrow = 0 := by
    calc
      m ≫ cokernel.π P.arrow = m ≫
          (cokernel.π (r ≫ m) ≫ w) := by
        dsimp only [w]
        rw [cokernel.π_desc]
      _ = (cokernel.π r ≫ t) ≫ w := by
        rw [← Category.assoc,
          cokernel_π_comp_cokernelInclusionOfComp]
      _ = (cokernel.π r ≫ (k ≫ pbar)) ≫ w := by rw [hk]
      _ = (cokernel.π r ≫ k) ≫ (pbar ≫ w) := by
        simp only [Category.assoc]
      _ = 0 := by rw [hpbarw, comp_zero]
  let b : H ⟶ (P : C) := Abelian.monoLift P.arrow m hmPπ
  exact Or.inl (by
    simpa only [P.mk_arrow] using
      (Subobject.mk_le_mk_of_comm b
        (Abelian.monoLift_comp P.arrow m hmPπ)))

/-- Restricting an ambient waist to an intermediate subobject preserves the
waist property. -/
theorem isWaistSubobject_restrict
    {L H X : C} (a : L ⟶ H) [Mono a] (m : H ⟶ X) [Mono m]
    (hL : IsWaistSubobject (Subobject.mk (a ≫ m))) :
    IsWaistSubobject (Subobject.mk a) := by
  intro P
  rcases hL (Subobject.mk (P.arrow ≫ m)) with h | h
  · have h' : Subobject.mk (a ≫ m) ≤
        Subobject.mk (P.arrow ≫ m) := h
    let b : L ⟶ (P : C) :=
      Subobject.ofMkLEMk (a ≫ m) (P.arrow ≫ m) h'
    have hb : b ≫ (P.arrow ≫ m) = a ≫ m :=
      Subobject.ofMkLEMk_comp h'
    have hb' : b ≫ P.arrow = a := by
      apply (cancel_mono m).1
      simpa only [Category.assoc] using hb
    exact Or.inl (by
      simpa only [P.mk_arrow] using
        (Subobject.mk_le_mk_of_comm b hb'))
  · have h' : Subobject.mk (P.arrow ≫ m) ≤
        Subobject.mk (a ≫ m) := h
    let b : (P : C) ⟶ L :=
      Subobject.ofMkLEMk (P.arrow ≫ m) (a ≫ m) h'
    have hb : b ≫ (a ≫ m) = P.arrow ≫ m :=
      Subobject.ofMkLEMk_comp h'
    have hb' : b ≫ a = P.arrow := by
      apply (cancel_mono m).1
      simpa only [Category.assoc] using hb
    exact Or.inr (by
      simpa only [P.mk_arrow] using
        (Subobject.mk_le_mk_of_comm b hb'))

/-- A simple essential subobject remains essential in every intermediate
subobject through which its inclusion factors. -/
theorem essential_restrict_of_simple
    {L H X : C} [Simple L]
    (l : L ⟶ X) [Mono l] (hl : IsEssentialMono l)
    (a : L ⟶ H) [Mono a] (m : H ⟶ X) [Mono m]
    (ham : a ≫ m = l) :
    IsEssentialMono a := by
  constructor
  · infer_instance
  · intro Z q haq
    letI : Mono (a ≫ q) := haq
    apply Abelian.mono_of_kernel_ι_eq_zero
    by_contra hk
    let r : kernel q ⟶ X := kernel.ι q ≫ m
    have hr : r ≠ 0 := by
      intro hrzero
      apply hk
      apply (cancel_mono m).1
      simpa only [r, zero_comp] using hrzero
    letI : Mono r := inferInstance
    have hP : Subobject.mk r ≠ ⊥ := fun hbot ↦
      hr (Subobject.mk_eq_bot_iff_zero.mp hbot)
    have hle : Subobject.mk l ≤ Subobject.mk r :=
      simple_le_nonzero_subobject_of_essential l hl (Subobject.mk r) hP
    let b : L ⟶ kernel q := Subobject.ofMkLEMk l r hle
    have hbr : b ≫ r = l := Subobject.ofMkLEMk_comp hle
    have hba : b ≫ kernel.ι q = a := by
      apply (cancel_mono m).1
      simpa only [r, Category.assoc, ham] using hbr
    apply CategoryTheory.id_nonzero L
    apply (cancel_mono (a ≫ q)).1
    rw [Category.id_comp, zero_comp, ← hba, Category.assoc,
      kernel.condition, comp_zero]

/-- A simple essential subobject with uniserial cokernel has uniserial
ambient object. -/
theorem of_essential_simple_cokernel
    {L X : C} [Simple L] (l : L ⟶ X) (hl : IsEssentialMono l)
    (hQ : IsUniserialObject (cokernel l)) :
    IsUniserialObject X := by
  letI : Mono l := hl.1
  constructor
  intro P Q
  by_cases hP : P = ⊥
  · left
    simpa only [hP] using (bot_le : (⊥ : Subobject X) ≤ Q)
  by_cases hQzero : Q = ⊥
  · right
    simpa only [hQzero] using (bot_le : (⊥ : Subobject X) ≤ P)
  have hLP : Subobject.mk l ≤ P :=
    simple_le_nonzero_subobject_of_essential l hl P hP
  have hLQ : Subobject.mk l ≤ Q :=
    simple_le_nonzero_subobject_of_essential l hl Q hQzero
  have hLP' : Subobject.mk l ≤ Subobject.mk P.arrow := by
    simpa only [P.mk_arrow] using hLP
  have hLQ' : Subobject.mk l ≤ Subobject.mk Q.arrow := by
    simpa only [Q.mk_arrow] using hLQ
  let lP : L ⟶ (P : C) := Subobject.ofMkLEMk l P.arrow hLP'
  let lQ : L ⟶ (Q : C) := Subobject.ofMkLEMk l Q.arrow hLQ'
  have hlP : lP ≫ P.arrow = l := Subobject.ofMkLEMk_comp hLP'
  have hlQ : lQ ≫ Q.arrow = l := Subobject.ofMkLEMk_comp hLQ'
  have sqP : IsPullback lP (𝟙 L) P.arrow l :=
    IsPullback.of_vert_isIso_mono ⟨by simp only [hlP, Category.id_comp]⟩
  have sqQ : IsPullback lQ (𝟙 L) Q.arrow l :=
    IsPullback.of_vert_isIso_mono ⟨by simp only [hlQ, Category.id_comp]⟩
  let pbar : cokernel lP ⟶ cokernel l :=
    cokernel.map lP l (𝟙 L) P.arrow sqP.w
  let qbar : cokernel lQ ⟶ cokernel l :=
    cokernel.map lQ l (𝟙 L) Q.arrow sqQ.w
  letI : Mono pbar := Abelian.mono_cokernel_map_of_isPullback sqP
  letI : Mono qbar := Abelian.mono_cokernel_map_of_isPullback sqQ
  let Pbar : Subobject (cokernel l) := Subobject.mk pbar
  let Qbar : Subobject (cokernel l) := Subobject.mk qbar
  have hpbar : cokernel.π lP ≫ pbar = P.arrow ≫ cokernel.π l := by
    exact cokernel.π_desc _ _ _
  have hqbar : cokernel.π lQ ≫ qbar = Q.arrow ≫ cokernel.π l := by
    exact cokernel.π_desc _ _ _
  have lift_le {P₁ P₂ : Subobject X}
      {m₁ : L ⟶ (P₁ : C)} {m₂ : L ⟶ (P₂ : C)}
      {b₁ : cokernel m₁ ⟶ cokernel l}
      {b₂ : cokernel m₂ ⟶ cokernel l}
      [Mono b₁] [Mono b₂]
      (hm₂ : m₂ ≫ P₂.arrow = l)
      (hb₁ : cokernel.π m₁ ≫ b₁ = P₁.arrow ≫ cokernel.π l)
      (hb₂ : cokernel.π m₂ ≫ b₂ = P₂.arrow ≫ cokernel.π l)
      (hbar : Subobject.mk b₁ ≤ Subobject.mk b₂) : P₁ ≤ P₂ := by
    let k : cokernel m₁ ⟶ cokernel m₂ :=
      Subobject.ofMkLEMk b₁ b₂ hbar
    have hk : k ≫ b₂ = b₁ := Subobject.ofMkLEMk_comp hbar
    have hl₂π : l ≫ cokernel.π P₂.arrow = 0 := by
      rw [← hm₂, Category.assoc, cokernel.condition, comp_zero]
    let w : cokernel l ⟶ cokernel P₂.arrow :=
      cokernel.desc l (cokernel.π P₂.arrow) hl₂π
    have hb₂w : b₂ ≫ w = 0 := by
      apply (cancel_epi (cokernel.π m₂)).1
      calc
        cokernel.π m₂ ≫ (b₂ ≫ w) =
            (cokernel.π m₂ ≫ b₂) ≫ w :=
          (Category.assoc _ _ _).symm
        _ = (P₂.arrow ≫ cokernel.π l) ≫ w := by rw [hb₂]
        _ = P₂.arrow ≫ cokernel.π P₂.arrow := by
          dsimp only [w]
          rw [Category.assoc, cokernel.π_desc]
        _ = 0 := cokernel.condition P₂.arrow
        _ = cokernel.π m₂ ≫ 0 := by rw [comp_zero]
    have hpπ : P₁.arrow ≫ cokernel.π P₂.arrow = 0 := by
      calc
        P₁.arrow ≫ cokernel.π P₂.arrow =
            P₁.arrow ≫ (cokernel.π l ≫ w) := by
          dsimp only [w]
          rw [cokernel.π_desc]
        _ = (P₁.arrow ≫ cokernel.π l) ≫ w :=
          (Category.assoc _ _ _).symm
        _ = (cokernel.π m₁ ≫ b₁) ≫ w := by rw [hb₁]
        _ = (cokernel.π m₁ ≫ (k ≫ b₂)) ≫ w := by rw [hk]
        _ = (cokernel.π m₁ ≫ k) ≫ (b₂ ≫ w) := by
          simp only [Category.assoc]
        _ = 0 := by rw [hb₂w, comp_zero]
    let a : (P₁ : C) ⟶ (P₂ : C) :=
      Abelian.monoLift P₂.arrow P₁.arrow hpπ
    simpa only [P₁.mk_arrow, P₂.mk_arrow] using
      (Subobject.mk_le_mk_of_comm a
        (Abelian.monoLift_comp P₂.arrow P₁.arrow hpπ))
  rcases hQ.total Pbar Qbar with hbar | hbar
  · exact Or.inl (lift_le hlQ hpbar hqbar hbar)
  · exact Or.inr (lift_le hlP hqbar hpbar hbar)

/-- A waist subobject with simple cokernel is the unique maximal subobject and
hence contains every proper subobject. -/
theorem isRadicalSubobject_of_waist_simple_cokernel
    {L X : C} (l : L ⟶ X) [Mono l] [Simple (cokernel l)]
    (hl : IsWaistSubobject (Subobject.mk l)) :
    IsRadicalSubobject (Subobject.mk l) := by
  intro P hPtop
  by_cases hPL : P ≤ Subobject.mk l
  · exact hPL
  have hLP : Subobject.mk l ≤ P :=
    (hl P).resolve_right hPL
  have hLP' : Subobject.mk l ≤ Subobject.mk P.arrow := by
    simpa only [P.mk_arrow] using hLP
  let a : L ⟶ (P : C) := Subobject.ofMkLEMk l P.arrow hLP'
  have ha : a ≫ P.arrow = l := Subobject.ofMkLEMk_comp hLP'
  have sq : IsPullback a (𝟙 L) P.arrow l :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [ha, Category.id_comp]⟩
  let b : cokernel a ⟶ cokernel l :=
    cokernel.map a l (𝟙 L) P.arrow sq.w
  letI : Mono b := Abelian.mono_cokernel_map_of_isPullback sq
  have hb : cokernel.π a ≫ b = P.arrow ≫ cokernel.π l :=
    cokernel.π_desc _ _ _
  have hbne : b ≠ 0 := by
    intro hbzero
    have hπa : cokernel.π a = 0 := by
      apply (cancel_mono b).1
      rw [hbzero, comp_zero, zero_comp]
    letI : Epi a := Abelian.epi_of_cokernel_π_eq_zero a hπa
    letI : IsIso a := isIso_of_mono_of_epi a
    apply hPL
    rw [← P.mk_arrow]
    exact Subobject.mk_le_mk_of_comm (inv a) (by
      calc
        inv a ≫ l = inv a ≫ (a ≫ P.arrow) := by rw [ha]
        _ = P.arrow := by simp)
  letI : IsIso b := (Simple.mono_isIso_iff_nonzero b).2 hbne
  have hlPπ : l ≫ cokernel.π P.arrow = 0 := by
    rw [← ha, Category.assoc, cokernel.condition, comp_zero]
  let w : cokernel l ⟶ cokernel P.arrow :=
    cokernel.desc l (cokernel.π P.arrow) hlPπ
  have hbw : b ≫ w = 0 := by
    apply (cancel_epi (cokernel.π a)).1
    calc
      cokernel.π a ≫ (b ≫ w) =
          (P.arrow ≫ cokernel.π l) ≫ w := by
        rw [← Category.assoc, hb]
      _ = P.arrow ≫ cokernel.π P.arrow := by
        dsimp only [w]
        rw [Category.assoc, cokernel.π_desc]
      _ = 0 := cokernel.condition P.arrow
      _ = cokernel.π a ≫ 0 := by rw [comp_zero]
  have hw : w = 0 := by
    apply (cancel_epi b).1
    simpa only [comp_zero] using hbw
  have hπP : cokernel.π P.arrow = 0 := by
    rw [← show cokernel.π l ≫ w = cokernel.π P.arrow from
      cokernel.π_desc l (cokernel.π P.arrow) hlPπ]
    rw [hw, comp_zero]
  letI : Epi P.arrow := Abelian.epi_of_cokernel_π_eq_zero P.arrow hπP
  letI : IsIso P.arrow := isIso_of_mono_of_epi P.arrow
  exfalso
  apply hPtop
  simpa only [P.mk_arrow] using
    (Subobject.isIso_iff_mk_eq_top P.arrow).mp
      (inferInstance : IsIso P.arrow)

/-- In a uniserial object, a subobject with simple cokernel is the unique
maximal subobject and hence contains every proper subobject. -/
theorem isRadicalSubobject_of_uniserial_simple_cokernel
    {L X : C} (hX : IsUniserialObject X)
    (l : L ⟶ X) [Mono l] [Simple (cokernel l)] :
    IsRadicalSubobject (Subobject.mk l) :=
  isRadicalSubobject_of_waist_simple_cokernel l
    (fun P ↦ hX.total (Subobject.mk l) P)

/-- Extending a uniserial object across a waist inclusion with simple
cokernel again gives a uniserial object. -/
theorem of_waist_simple_cokernel
    {L X : C} (hL : IsUniserialObject L)
    (l : L ⟶ X) [Mono l] [Simple (cokernel l)]
    (hl : IsWaistSubobject (Subobject.mk l)) :
    IsUniserialObject X := by
  apply of_radicalSubobject (Subobject.mk l)
    (isRadicalSubobject_of_waist_simple_cokernel l hl)
  exact hL.congr (Subobject.underlyingIso l).symm

/-- A simple essential subobject with simple quotient contains every proper
subobject of its ambient object. -/
theorem isRadicalSubobject_of_essential_simple_cokernel
    {L X : C} [Simple L] (l : L ⟶ X) [Mono l]
    (hl : IsEssentialMono l) [Simple (cokernel l)] :
    IsRadicalSubobject (Subobject.mk l) := by
  intro P hPtop
  by_cases hPbot : P = ⊥
  · simpa only [hPbot] using (bot_le : (⊥ : Subobject X) ≤ Subobject.mk l)
  by_cases hPL : P ≤ Subobject.mk l
  · exact hPL
  have hLP : Subobject.mk l ≤ P :=
    simple_le_nonzero_subobject_of_essential l hl P hPbot
  have hLP' : Subobject.mk l ≤ Subobject.mk P.arrow := by
    simpa only [P.mk_arrow] using hLP
  let a : L ⟶ (P : C) := Subobject.ofMkLEMk l P.arrow hLP'
  have ha : a ≫ P.arrow = l := Subobject.ofMkLEMk_comp hLP'
  have sq : IsPullback a (𝟙 L) P.arrow l :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [ha, Category.id_comp]⟩
  let b : cokernel a ⟶ cokernel l :=
    cokernel.map a l (𝟙 L) P.arrow sq.w
  letI : Mono b := Abelian.mono_cokernel_map_of_isPullback sq
  have hb : cokernel.π a ≫ b = P.arrow ≫ cokernel.π l :=
    cokernel.π_desc _ _ _
  have hbne : b ≠ 0 := by
    intro hbzero
    have hπa : cokernel.π a = 0 := by
      apply (cancel_mono b).1
      rw [hbzero, comp_zero, zero_comp]
    letI : Epi a := Abelian.epi_of_cokernel_π_eq_zero a hπa
    letI : IsIso a := isIso_of_mono_of_epi a
    apply hPL
    rw [← P.mk_arrow]
    exact Subobject.mk_le_mk_of_comm (inv a) (by
      calc
        inv a ≫ l = inv a ≫ (a ≫ P.arrow) := by rw [ha]
        _ = P.arrow := by simp)
  letI : IsIso b := (Simple.mono_isIso_iff_nonzero b).2 hbne
  have hlPπ : l ≫ cokernel.π P.arrow = 0 := by
    rw [← ha, Category.assoc, cokernel.condition, comp_zero]
  let w : cokernel l ⟶ cokernel P.arrow :=
    cokernel.desc l (cokernel.π P.arrow) hlPπ
  have hbw : b ≫ w = 0 := by
    apply (cancel_epi (cokernel.π a)).1
    calc
      cokernel.π a ≫ (b ≫ w) =
          (P.arrow ≫ cokernel.π l) ≫ w := by
        rw [← Category.assoc, hb]
      _ = P.arrow ≫ cokernel.π P.arrow := by
        dsimp only [w]
        rw [Category.assoc, cokernel.π_desc]
      _ = 0 := cokernel.condition P.arrow
      _ = cokernel.π a ≫ 0 := by rw [comp_zero]
  have hw : w = 0 := by
    apply (cancel_epi b).1
    simpa only [comp_zero] using hbw
  have hπP : cokernel.π P.arrow = 0 := by
    rw [← show cokernel.π l ≫ w = cokernel.π P.arrow from
      cokernel.π_desc l (cokernel.π P.arrow) hlPπ]
    rw [hw, comp_zero]
  letI : Epi P.arrow := Abelian.epi_of_cokernel_π_eq_zero P.arrow hπP
  letI : IsIso P.arrow := isIso_of_mono_of_epi P.arrow
  exfalso
  apply hPtop
  simpa only [P.mk_arrow] using
    (Subobject.isIso_iff_mk_eq_top P.arrow).mp
      (inferInstance : IsIso P.arrow)

end IsUniserialObject

namespace CoveringHom

universe uC uK

variable {k : Type uK} [Field k]
variable {D : Type uC} [Category.{uK} D] [Preadditive D]
  [CategoryTheory.Linear k D]

/-- A proper quotient of a finite module has strictly smaller total
pointwise dimension. -/
theorem moduleTotalDimension_lt_of_epi_not_isIso
    (M N : FiniteDimensionalModuleCategory.{uC, uK, uK, uK} (C := D) k)
    (p : M ⟶ N) [Epi p] (hp : ¬ IsIso p) :
    moduleTotalDimension N < moduleTotalDimension M := by
  classical
  let J := (IsFiniteDimensionalModule (C := D) k).ι
  let I := (IsLinearModule (C := D) k).ι
  letI : J.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
      (IsFiniteDimensionalModule (C := D) k)
  letI : I.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
      (IsLinearModule (C := D) k)
  haveI : Epi (I.map (J.map p)) := I.map_epi (J.map p)
  haveI hpApp (X : D) : Epi ((I.map (J.map p)).app X) := inferInstance
  have hle (X : D) :
      Module.finrank k (N.obj.obj.obj X) ≤
        Module.finrank k (M.obj.obj.obj X) := by
    exact LinearMap.finrank_le_finrank_of_surjective
      ((ModuleCat.epi_iff_surjective _).mp (hpApp X))
  have hbad : ∃ X : D, ¬ IsIso ((I.map (J.map p)).app X) := by
    by_contra h
    push Not at h
    letI hpAppIso (X : D) : IsIso ((I.map (J.map p)).app X) := h X
    haveI : IsIso (I.map (J.map p)) := NatIso.isIso_of_isIso_app _
    haveI : IsIso (J.map p) := isIso_of_reflects_iso (J.map p) I
    haveI : IsIso p := isIso_of_reflects_iso p J
    exact hp inferInstance
  obtain ⟨X, hX⟩ := hbad
  have hlt : Module.finrank k (N.obj.obj.obj X) <
      Module.finrank k (M.obj.obj.obj X) := by
    refine (hle X).lt_of_ne ?_
    intro heq
    apply hX
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have hsurj : Function.Surjective ((I.map (J.map p)).app X) :=
      (ModuleCat.epi_iff_surjective _).mp (hpApp X)
    exact ⟨
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm).2 hsurj,
      hsurj⟩
  let f : D → ℕ := fun Y ↦ Module.finrank k (N.obj.obj.obj Y)
  let g : D → ℕ := fun Y ↦ Module.finrank k (M.obj.obj.obj Y)
  have hf := moduleFinrank_hasFiniteSupport N
  have hg := moduleFinrank_hasFiniteSupport M
  let s := (hf.union hg).toFinset
  rw [moduleTotalDimension, moduleTotalDimension,
    finsum_eq_finsetSum_of_support_subset f
      (s := s) (by
        intro Y hY
        change Y ∈ (hf.union hg).toFinset
        rw [Set.Finite.mem_toFinset, Set.mem_union]
        exact Or.inl hY),
    finsum_eq_finsetSum_of_support_subset g
      (s := s) (by
        intro Y hY
        change Y ∈ (hf.union hg).toFinset
        rw [Set.Finite.mem_toFinset, Set.mem_union]
        exact Or.inr hY)]
  apply Finset.sum_lt_sum
  · intro Y hY
    exact hle Y
  · refine ⟨X, ?_, hlt⟩
    change X ∈ (hf.union hg).toFinset
    rw [Set.Finite.mem_toFinset, Set.mem_union]
    right
    change Module.finrank k (M.obj.obj.obj X) ≠ 0
    omega

/-- Finite ascending-socle induction.  If every nonzero object in a class has
a simple essential subobject whose cokernel remains in the class, then every
object in the class is uniserial. -/
theorem finiteDimensionalModule_isUniserial_of_essentialSimpleCokernelSuccessors
    (Good : FiniteDimensionalModuleCategory.{uC, uK, uK, uK} (C := D) k → Prop)
    (hsuccessor : ∀
      (F : FiniteDimensionalModuleCategory.{uC, uK, uK, uK} (C := D) k),
      Good F → ¬ IsZero F →
      ∃ (L : FiniteDimensionalModuleCategory.{uC, uK, uK, uK} (C := D) k)
        (l : L ⟶ F),
        Simple L ∧ Mono l ∧ IsEssentialMono l ∧ Good (cokernel l))
    (F : FiniteDimensionalModuleCategory.{uC, uK, uK, uK} (C := D) k)
    (hF : Good F) : IsUniserialObject F := by
  let main : ∀ n : ℕ,
      ∀ (G : FiniteDimensionalModuleCategory.{uC, uK, uK, uK} (C := D) k),
      moduleTotalDimension G = n → Good G → IsUniserialObject G := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro G hdim hG
        by_cases hzero : IsZero G
        · exact IsUniserialObject.of_isZero hzero
        · obtain ⟨L, l, hL, hl, hessential, hnextGood⟩ :=
            hsuccessor G hG hzero
          letI : Simple L := hL
          letI : Mono l := hl
          have hlne : l ≠ 0 := by
            intro hlzero
            apply CategoryTheory.id_nonzero L
            apply (cancel_mono l).1
            rw [Category.id_comp, hlzero, zero_comp]
          have hπnot : ¬ IsIso (cokernel.π l) := by
            intro hπ
            letI : IsIso (cokernel.π l) := hπ
            apply hlne
            apply (cancel_mono (cokernel.π l)).1
            rw [cokernel.condition, zero_comp]
          have hlt : moduleTotalDimension (cokernel l) < n := by
            rw [← hdim]
            exact moduleTotalDimension_lt_of_epi_not_isIso
              G (cokernel l) (cokernel.π l) hπnot
          have hnext : IsUniserialObject (cokernel l) :=
            ih (moduleTotalDimension (cokernel l)) hlt
              (cokernel l) rfl hnextGood
          exact IsUniserialObject.of_essential_simple_cokernel
            l hessential hnext
  exact main (moduleTotalDimension F) F rfl hF

end CoveringHom

end MagnitudeConjecture
