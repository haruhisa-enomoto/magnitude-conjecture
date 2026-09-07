import MagnitudeConjecture.CategoryTheory.AdditiveAuslanderEquivalence

/-!
# Fullness of a representable functor from finite additive presentations

This file isolates the elementary categorical core of a minimal-realization
argument.  If every object has a two-term presentation by objects in `add(G)`,
the displayed map is surjective on maps out of `G`, and the second arrow has
the weak-cokernel factorization property, then a faithful `Hom(G,-)` is full.

The theorem separates the routine Yoneda lifting from the genuinely
homological task of constructing these presentations in a strict tau-category.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace MagnitudeConjecture.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- A two-term presentation of `X` by objects in `add(G)`, with exactly the
two exactness properties detected by `Hom(G,-)`. -/
structure FiniteAddGeneratorPresentation (G X : C) where
  P₁ : C
  P₀ : C
  P₀_mem : finiteAddClosure G P₀
  d : P₁ ⟶ P₀
  p : P₀ ⟶ X
  zero : d ≫ p = 0
  lifts_from_generator : ∀ h : G ⟶ X,
    ∃ l : G ⟶ P₀, l ≫ p = h
  weakCokernel : ∀ {Y : C} (q : P₀ ⟶ Y), d ≫ q = 0 →
    ∃ f : X ⟶ Y, p ≫ f = q

/-- An object already in `add(G)` has the tautological presentation. -/
def FiniteAddGeneratorPresentation.ofFiniteAddClosure
    {G X : C} (hX : finiteAddClosure G X) :
    FiniteAddGeneratorPresentation G X where
  P₁ := X
  P₀ := X
  P₀_mem := hX
  d := 0
  p := 𝟙 X
  zero := zero_comp
  lifts_from_generator h := ⟨h, Category.comp_id h⟩
  weakCokernel q _ := ⟨q, Category.id_comp q⟩

/-- Transport a finite additive presentation across an isomorphism of target
objects. -/
def FiniteAddGeneratorPresentation.ofIso
    {G X Y : C} (P : FiniteAddGeneratorPresentation G X)
    (e : X ≅ Y) : FiniteAddGeneratorPresentation G Y where
  P₁ := P.P₁
  P₀ := P.P₀
  P₀_mem := P.P₀_mem
  d := P.d
  p := P.p ≫ e.hom
  zero := by rw [← Category.assoc, P.zero, zero_comp]
  lifts_from_generator h := by
    obtain ⟨l, hl⟩ := P.lifts_from_generator (h ≫ e.inv)
    refine ⟨l, ?_⟩
    rw [← Category.assoc, hl, Category.assoc,
      e.inv_hom_id, Category.comp_id]
  weakCokernel q hq := by
    obtain ⟨f, hf⟩ := P.weakCokernel q hq
    refine ⟨e.inv ≫ f, ?_⟩
    calc
      (P.p ≫ e.hom) ≫ e.inv ≫ f =
          P.p ≫ (e.hom ≫ e.inv) ≫ f := by
        simp only [Category.assoc]
      _ = P.p ≫ f := by
        rw [e.hom_inv_id, Category.id_comp]
      _ = q := hf

/-- Replace the generator of a finite additive presentation by an isomorphic
one. -/
def FiniteAddGeneratorPresentation.replaceGenerator
    {G H X : C} (P : FiniteAddGeneratorPresentation G X)
    (e : G ≅ H) : FiniteAddGeneratorPresentation H X where
  P₁ := P.P₁
  P₀ := P.P₀
  P₀_mem := (finiteAddClosure_iff_of_iso e).1 P.P₀_mem
  d := P.d
  p := P.p
  zero := P.zero
  lifts_from_generator h := by
    obtain ⟨l, hl⟩ := P.lifts_from_generator (e.hom ≫ h)
    refine ⟨e.inv ≫ l, ?_⟩
    rw [Category.assoc, hl, ← Category.assoc, e.inv_hom_id,
      Category.id_comp]
  weakCokernel := P.weakCokernel

/-- Generator lifting extends from `G` to every object of `add(G)`. -/
theorem FiniteAddGeneratorPresentation.lifts_from_finiteAddClosure
    {G X A : C} (P : FiniteAddGeneratorPresentation G X)
    (hA : finiteAddClosure G A) (h : A ⟶ X) :
    ∃ l : A ⟶ P.P₀, l ≫ P.p = h := by
  classical
  let R := hA.some
  let F : Fin R.n → C := fun _ ↦ G
  choose l hl using fun i : Fin R.n ↦
    P.lifts_from_generator
      (biproduct.ι F i ≫ R.retract.r ≫ h)
  let q : (⨁ F) ⟶ P.P₀ := biproduct.desc l
  refine ⟨R.retract.i ≫ q, ?_⟩
  have hq : q ≫ P.p = R.retract.r ≫ h := by
    apply biproduct.hom_ext'
    intro i
    simp only [q, biproduct.ι_desc_assoc, hl]
  rw [Category.assoc, hq, ← Category.assoc,
    R.retract.retract, Category.id_comp]

/-- Under faithfulness of `Hom(G,-)`, the displayed cover in any finite
additive generator presentation is an epimorphism. -/
theorem FiniteAddGeneratorPresentation.epi_p
    {G X : C} (P : FiniteAddGeneratorPresentation G X)
    (hfaithful : (preadditiveCoyonedaObj G).Faithful) :
    Epi P.p := by
  apply Preadditive.epi_of_cancel_zero P.p
  intro Y q hq
  apply hfaithful.map_injective
  apply ModuleCat.hom_ext
  ext h
  obtain ⟨l, hl⟩ := P.lifts_from_generator h
  change h ≫ q = h ≫ (0 : X ⟶ Y)
  rw [← hl, Category.assoc, hq, comp_zero]
  simp

/-- Binary biproducts of finite additive generator presentations. -/
def FiniteAddGeneratorPresentation.biprod
    [HasBinaryBiproducts C]
    {G X Y : C} (P : FiniteAddGeneratorPresentation G X)
    (Q : FiniteAddGeneratorPresentation G Y) :
    FiniteAddGeneratorPresentation G (X ⊞ Y) where
  P₁ := P.P₁ ⊞ Q.P₁
  P₀ := P.P₀ ⊞ Q.P₀
  P₀_mem := finiteAddClosure_biprod P.P₀_mem Q.P₀_mem
  d := biprod.map P.d Q.d
  p := biprod.map P.p Q.p
  zero := by
    apply biprod.hom_ext
    · simp [P.zero]
    · simp [Q.zero]
  lifts_from_generator h := by
    obtain ⟨l, hl⟩ := P.lifts_from_generator (h ≫ biprod.fst)
    obtain ⟨r, hr⟩ := Q.lifts_from_generator (h ≫ biprod.snd)
    refine ⟨biprod.lift l r, ?_⟩
    apply biprod.hom_ext
    · simp [hl]
    · simp [hr]
  weakCokernel q hq := by
    have hqP : P.d ≫ biprod.inl ≫ q = 0 := by
      rw [← biprod.inl_map_assoc, hq, comp_zero]
    have hqQ : Q.d ≫ biprod.inr ≫ q = 0 := by
      rw [← biprod.inr_map_assoc, hq, comp_zero]
    obtain ⟨f, hf⟩ := P.weakCokernel (biprod.inl ≫ q) (by
      simpa only [Category.assoc] using hqP)
    obtain ⟨g, hg⟩ := Q.weakCokernel (biprod.inr ≫ q) (by
      simpa only [Category.assoc] using hqQ)
    refine ⟨biprod.desc f g, ?_⟩
    apply biprod.hom_ext'
    · simp [hf]
    · simp [hg]

/-- Split a nonempty finite biproduct into its first summand and its tail. -/
private def finiteBiproductSuccIso
    [HasBinaryBiproducts C] {m : ℕ} (F : Fin (m + 1) → C) :
    (⨁ F) ≅ (F 0 ⊞ (⨁ fun i : Fin m ↦ F i.succ)) := by
  let T : Fin m → C := fun i ↦ F i.succ
  let q : (⨁ F) ⟶ (⨁ T) :=
    biproduct.lift fun i : Fin m ↦ biproduct.π F i.succ
  let r : (⨁ T) ⟶ (⨁ F) :=
    biproduct.desc fun i : Fin m ↦ biproduct.ι F i.succ
  have hhead_q : biproduct.ι F 0 ≫ q = 0 := by
    apply biproduct.hom_ext
    intro i
    rw [Category.assoc, biproduct.lift_π, zero_comp]
    exact biproduct.ι_π_ne F (Fin.succ_ne_zero i).symm
  have htail_q (i : Fin m) :
      biproduct.ι F i.succ ≫ q = biproduct.ι T i := by
    apply biproduct.hom_ext
    intro j
    by_cases h : i = j
    · subst h
      simp [q, T, Category.assoc]
    · rw [Category.assoc, biproduct.lift_π,
        biproduct.ι_π_ne F (fun hs ↦ h (Fin.succ_inj.mp hs)),
        biproduct.ι_π_ne T h]
  have hr_head : r ≫ biproduct.π F 0 = 0 := by
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc, biproduct.ι_desc, comp_zero]
    exact biproduct.ι_π_ne F (Fin.succ_ne_zero i)
  have hr_tail (i : Fin m) :
      r ≫ biproduct.π F i.succ = biproduct.π T i := by
    apply biproduct.hom_ext'
    intro j
    by_cases h : j = i
    · subst h
      simp [r, T]
    · rw [← Category.assoc, biproduct.ι_desc,
        biproduct.ι_π_ne F (fun hs ↦ h (Fin.succ_inj.mp hs)),
        biproduct.ι_π_ne T h]
  have hrq : r ≫ q = 𝟙 (⨁ T) := by
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc, biproduct.ι_desc, htail_q,
      Category.comp_id]
  have hhead_qr : biproduct.ι F 0 ≫ q ≫ r = 0 := by
    rw [← Category.assoc, hhead_q, zero_comp]
  have htail_qr (i : Fin m) :
      biproduct.ι F i.succ ≫ q ≫ r = biproduct.ι F i.succ := by
    rw [← Category.assoc, htail_q, biproduct.ι_desc]
  exact
    { hom := biprod.lift (biproduct.π F 0) q
      inv := biprod.desc (biproduct.ι F 0) r
      hom_inv_id := by
        apply biproduct.hom_ext'
        intro j
        refine Fin.cases ?_ (fun i ↦ ?_) j
        · simpa using hhead_qr
        · simpa using htail_qr i
      inv_hom_id := by
        apply biprod.hom_ext'
        · apply biprod.hom_ext
          · simp
          · simpa [Category.assoc] using hhead_q
        · apply biprod.hom_ext
          · simpa [Category.assoc] using hr_head
          · simpa [Category.assoc] using hrq }

/-- A finite biproduct of objects carrying finite additive generator
presentations again carries such a presentation. -/
theorem finiteAddGeneratorPresentation_finBiproduct
    [HasBinaryBiproducts C]
    {G : C} {n : ℕ} (F : Fin n → C)
    (P : ∀ i, FiniteAddGeneratorPresentation G (F i)) :
    Nonempty (FiniteAddGeneratorPresentation G (⨁ F)) := by
  induction n with
  | zero =>
      apply Nonempty.intro
      apply FiniteAddGeneratorPresentation.ofFiniteAddClosure
      exact ⟨{
        n := 0
        retract := Retract.ofIso
          (biproduct.mapIso (fun i : Fin 0 ↦ Fin.elim0 i)) }⟩
  | succ m ih =>
      let T : Fin m → C := fun i ↦ F i.succ
      obtain ⟨PT⟩ := ih T (fun i ↦ P i.succ)
      exact ⟨((P 0).biprod PT).ofIso
        (finiteBiproductSuccIso F).symm⟩

/-- Splice presentations through a weak-cokernel pair.  This is the formal
horseshoe step used by the right-tau-mesh induction. -/
def FiniteAddGeneratorPresentation.splice
    [HasBinaryBiproducts C]
    {G L M X : C}
    (PL : FiniteAddGeneratorPresentation G L)
    (PM : FiniteAddGeneratorPresentation G M)
    (f : L ⟶ M) (g : M ⟶ X)
    (hzero : f ≫ g = 0)
    (hlift : ∀ h : G ⟶ X, ∃ k : G ⟶ M, k ≫ g = h)
    (hweak : ∀ {Y : C} (q : M ⟶ Y), f ≫ q = 0 →
      ∃ s : X ⟶ Y, g ≫ s = q)
    (hfaithful : (preadditiveCoyonedaObj G).Faithful) :
    FiniteAddGeneratorPresentation G X := by
  let haExists := PM.lifts_from_finiteAddClosure
    PL.P₀_mem (PL.p ≫ f)
  let a := Classical.choose haExists
  have ha : a ≫ PM.p = PL.p ≫ f :=
    Classical.choose_spec haExists
  letI : Epi PL.p := PL.epi_p hfaithful
  exact
    { P₁ := PM.P₁ ⊞ PL.P₀
      P₀ := PM.P₀
      P₀_mem := PM.P₀_mem
      d := biprod.desc PM.d a
      p := PM.p ≫ g
      zero := by
        apply biprod.hom_ext'
        · simp only [biprod.inl_desc_assoc, comp_zero]
          rw [← Category.assoc, PM.zero, zero_comp]
        · simp only [biprod.inr_desc_assoc, comp_zero]
          rw [← Category.assoc, ha, Category.assoc,
            hzero, comp_zero]
      lifts_from_generator := by
        intro h
        obtain ⟨k, hk⟩ := hlift h
        obtain ⟨l, hl⟩ := PM.lifts_from_generator k
        refine ⟨l, ?_⟩
        rw [← Category.assoc, hl, hk]
      weakCokernel := by
        intro Y q hq
        have hdq : PM.d ≫ q = 0 := by
          rw [← biprod.inl_desc_assoc, hq, comp_zero]
        obtain ⟨r, hr⟩ := PM.weakCokernel q hdq
        have haq : a ≫ q = 0 := by
          rw [← biprod.inr_desc_assoc, hq, comp_zero]
        have hfr : f ≫ r = 0 := by
          apply (cancel_epi PL.p).1
          calc
            PL.p ≫ f ≫ r = (PL.p ≫ f) ≫ r := by
              rw [Category.assoc]
            _ = (a ≫ PM.p) ≫ r := by rw [ha]
            _ = a ≫ (PM.p ≫ r) := Category.assoc _ _ _
            _ = a ≫ q := by rw [hr]
            _ = 0 := haq
            _ = PL.p ≫ 0 := by simp
        obtain ⟨s, hs⟩ := hweak r hfr
        refine ⟨s, ?_⟩
        rw [Category.assoc, hs, hr] }

/-- A faithful representable functor is full once every object has a finite
`add(G)` presentation of the displayed exact form. -/
theorem preadditiveCoyonedaObj_full_of_finiteAddGeneratorPresentations
    (G : C) (hfaithful : (preadditiveCoyonedaObj G).Faithful)
    (hpresent : ∀ X : C,
      Nonempty (FiniteAddGeneratorPresentation G X)) :
    (preadditiveCoyonedaObj G).Full where
  map_surjective {X Y} α := by
    let F := preadditiveCoyonedaObj G
    let P := (hpresent X).some
    let αp : F.obj P.P₀ ⟶ F.obj Y := F.map P.p ≫ α
    obtain ⟨q, hq⟩ :=
      exists_hom_of_moduleHom_of_finiteAddSource
        G P.P₀_mem.some αp
    have hdq : P.d ≫ q = 0 := by
      apply hfaithful.map_injective
      rw [F.map_comp, hq, F.map_zero]
      dsimp only [αp]
      rw [← Category.assoc, ← F.map_comp, P.zero, F.map_zero,
        zero_comp]
    obtain ⟨f, hf⟩ := P.weakCokernel q hdq
    refine ⟨f, ?_⟩
    apply ModuleCat.hom_ext
    ext h
    change h ≫ f = α.hom h
    obtain ⟨l, hl⟩ := P.lifts_from_generator h
    have happ := congrArg (fun r ↦ r.hom l) hq
    change l ≫ q = α.hom (l ≫ P.p) at happ
    calc
      h ≫ f = (l ≫ P.p) ≫ f := by rw [hl]
      _ = l ≫ q := by rw [Category.assoc, hf]
      _ = α.hom (l ≫ P.p) := happ
      _ = α.hom h := by rw [hl]

end MagnitudeConjecture.CategoryTheory
