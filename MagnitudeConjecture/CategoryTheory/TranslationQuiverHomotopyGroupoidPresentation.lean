import MagnitudeConjecture.CategoryTheory.TranslationQuiverHomotopyGroupoid

/-!
# Presentation of the mesh-homotopy groupoid

The augmented quiver generates its mesh-homotopy groupoid subject exactly to
the polarized mesh relations.  A labelling into any target groupoid descends
when it respects those relations, and the descended functor is unique.

This is the generator-and-relation interface used to construct the
Bongartz--Gabriel graph comparison.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe u w v z

variable {Q : Type u} [Quiver.{w} Q]

namespace HomotopyGroupoid

-- The three vertex types below are transparent synonyms of the same type.
set_option backward.isDefEq.respectTransparency false

variable (T : RightMeshData Q)
variable {C : Type v} [Groupoid.{z} C]

/-- An augmented arrow regarded as a positive arrow of the symmetrified
augmented quiver. -/
private def positiveArrow {x y : AugmentedVertex T} (a : x ⟶ y) :
    @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y :=
  Sum.inl a

/-- An augmented arrow regarded as a negative arrow of the symmetrified
augmented quiver. -/
private def negativeArrow {x y : AugmentedVertex T} (a : x ⟶ y) :
    @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) y x :=
  Sum.inr a

/-- The augmented quiver includes into its mesh-homotopy groupoid. -/
def of : AugmentedVertex T ⥤q HomotopyGroupoid T where
  obj x := show HomotopyGroupoid T from x
  map a := Quotient.mk _ (positiveArrow T a).toPath

/-- The ordinary quiver includes into the augmented quiver. -/
def old : Q ⥤q AugmentedVertex T where
  obj x := show AugmentedVertex T from x
  map a := AugmentedArrow.old a

/-- An ordinary path evaluated in the mesh-homotopy groupoid. -/
def ofOldPath {x y : Q} (p : Quiver.Path x y) :
    (show HomotopyGroupoid T from x) ⟶
      (show HomotopyGroupoid T from y) :=
  (Paths.lift (old T ⋙q of T)).map p

@[simp]
theorem ofOldPath_nil (x : Q) :
    ofOldPath T (Quiver.Path.nil : Quiver.Path x x) = 𝟙 _ :=
  rfl

@[simp]
theorem ofOldPath_cons
    {x y z : Q} (p : Quiver.Path x y) (a : y ⟶ z) :
    ofOldPath T (p.cons a) =
      ofOldPath T p ≫ (of T).map (AugmentedArrow.old a) := by
  exact Paths.lift_cons (old T ⋙q of T) p a

@[simp]
theorem ofOldPath_toPath {x y : Q} (a : x ⟶ y) :
    ofOldPath T a.toPath = (of T).map (AugmentedArrow.old a) := by
  exact Paths.lift_toPath (old T ⋙q of T) a

@[simp]
theorem ofOldPath_comp
    {x y z : Q} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    ofOldPath T (p.comp q) = ofOldPath T p ≫ ofOldPath T q := by
  exact (Paths.lift (old T ⋙q of T)).map_comp p q

/-- Transporting the target of an augmented arrow becomes composition with
the corresponding equality morphism in the mesh-homotopy groupoid. -/
theorem of_cast_target
    {x y z : AugmentedVertex T} (a : x ⟶ y) (h : y = z) :
    (of T).map (a.cast rfl h) =
      (of T).map a ≫
        eqToHom (congrArg
          (fun t : AugmentedVertex T ↦
            show HomotopyGroupoid T from t) h) := by
  subst z
  simp

/-- The target-transport formula specialized to an ordinary augmented
arrow. -/
theorem of_old_cast_target
    {x y z : Q} (a : x ⟶ y) (h : y = z) :
    (of T).map (AugmentedArrow.old (a.cast rfl h)) =
      (of T).map (AugmentedArrow.old a) ≫
        eqToHom (congrArg
          (fun t : Q ↦ show HomotopyGroupoid T from t) h) := by
  subst z
  simp

@[simp]
theorem of_mesh_eq_old_comp_old
    (s : {s : Q // s ∉ T.projective}) (a : T.MeshArrow s) :
    (of T).map (AugmentedArrow.mesh s) =
      (of T).map (AugmentedArrow.old a.2) ≫
        (of T).map
          (AugmentedArrow.old ((T.arrowEquiv s a.1) a.2)) := by
  change Quotient.mk _ (meshArrowPath T s) =
    Quotient.mk _ ((oldArrowPath T a.2).comp
      (oldArrowPath T ((T.arrowEquiv s a.1) a.2)))
  apply Quotient.sound
  change Homotopic T s.1 (meshArrowPath T s)
    ((oldArrowPath T a.2).comp
      (oldArrowPath T ((T.arrowEquiv s a.1) a.2)))
  simpa only [Quiver.Path.nil_comp] using
    Homotopic.mesh s Quiver.Path.nil a

/-- A labelling of the augmented quiver respects mesh homotopy when every
formal mesh arrow has the same image as every polarized length-two route
through that mesh. -/
def MeshCompatible
    (phi : AugmentedVertex T ⥤q C) : Prop :=
  ∀ (s : {s : Q // s ∉ T.projective}) (a : T.MeshArrow s),
    phi.map (AugmentedArrow.mesh s) =
      phi.map (AugmentedArrow.old a.2) ≫
        phi.map (AugmentedArrow.old ((T.arrowEquiv s a.1) a.2))

/-- Evaluate a symmetrified augmented walk in a target groupoid. -/
def evalWalk
    (phi : AugmentedVertex T ⥤q C)
    {x y : Quiver.Symmetrify (AugmentedVertex T)}
    (p : @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    phi.obj (show AugmentedVertex T from x) ⟶
      phi.obj (show AugmentedVertex T from y) :=
  (Paths.lift (Quiver.Symmetrify.lift phi)).map p

@[simp]
theorem evalWalk_nil
    (phi : AugmentedVertex T ⥤q C)
    (x : Quiver.Symmetrify (AugmentedVertex T)) :
    evalWalk T phi (Quiver.Path.nil :
      @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
        (Quiver.symmetrifyQuiver (AugmentedVertex T)) x x) = 𝟙 _ :=
  rfl

@[simp]
theorem evalWalk_comp
    (phi : AugmentedVertex T ⥤q C)
    {x y z : Quiver.Symmetrify (AugmentedVertex T)}
    (p : @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y)
    (q : @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) y z) :
    evalWalk T phi (p.comp q) =
      evalWalk T phi p ≫ evalWalk T phi q := by
  exact (Paths.lift (Quiver.Symmetrify.lift phi)).map_comp p q

@[simp]
theorem evalWalk_toPath
    (phi : AugmentedVertex T ⥤q C)
    {x y : Quiver.Symmetrify (AugmentedVertex T)}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    evalWalk T phi e.toPath = (Quiver.Symmetrify.lift phi).map e := by
  exact Paths.lift_toPath (Quiver.Symmetrify.lift phi) e

@[simp]
theorem evalWalk_reverse
    (phi : AugmentedVertex T ⥤q C)
    {x y : Q} (p : Walk T x y) :
    evalWalk T phi p.reverse =
      Groupoid.inv (evalWalk T phi p) := by
  induction p with
  | nil =>
      rw [evalWalk_nil, Groupoid.inv_eq_inv]
      simp
  | cons p e ih =>
      simp only [Quiver.Path.reverse]
      rw [evalWalk_comp, evalWalk_toPath,
        Quiver.Symmetrify.lift_reverse, Groupoid.reverse_eq_inv,
        ih]
      change _ = Groupoid.inv
        (evalWalk T phi p ≫ (Quiver.Symmetrify.lift phi).map e)
      rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
        Groupoid.inv_eq_inv, IsIso.inv_comp]

@[simp]
theorem evalWalk_meshArrowPath
    (phi : AugmentedVertex T ⥤q C)
    (s : {s : Q // s ∉ T.projective}) :
    evalWalk T phi (meshArrowPath T s) =
      phi.map (AugmentedArrow.mesh s) := by
  rw [meshArrowPath, evalWalk_toPath]
  rfl

@[simp]
theorem evalWalk_oldArrowPath
    (phi : AugmentedVertex T ⥤q C)
    {x y : Q} (a : x ⟶ y) :
    evalWalk T phi (oldArrowPath T a) =
      phi.map (AugmentedArrow.old a) := by
  rw [oldArrowPath, evalWalk_toPath]
  rfl

private theorem evalWalk_eq_of_homotopic
    (phi : AugmentedVertex T ⥤q C)
    (hphi : MeshCompatible T phi)
    {x y : Q} {p q : Walk T x y}
    (h : Homotopic T x p q) :
    evalWalk T phi p = evalWalk T phi q := by
  induction h with
  | refl p => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp h r ih =>
      simpa only [evalWalk_comp] using
        congrArg (fun f ↦ f ≫ evalWalk T phi r) ih
  | cancel p e =>
      rw [evalWalk_comp, evalWalk_comp, evalWalk_toPath,
        evalWalk_toPath, Quiver.Symmetrify.lift_reverse,
        Groupoid.reverse_eq_inv,
        Groupoid.inv_eq_inv,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  | mesh s p a =>
      rw [evalWalk_comp, evalWalk_comp, evalWalk_comp]
      rw [Category.assoc]
      rw [evalWalk_meshArrowPath, evalWalk_oldArrowPath,
        evalWalk_oldArrowPath, hphi s a]

/-- A mesh-compatible labelling of the augmented quiver descends uniquely on
morphisms to a functor from the mesh-homotopy groupoid. -/
def lift
    (phi : AugmentedVertex T ⥤q C)
    (hphi : MeshCompatible T phi) :
    HomotopyGroupoid T ⥤ C where
  obj x := phi.obj (show AugmentedVertex T from x)
  map := Quotient.lift
    (fun p ↦ evalWalk T phi p)
    (fun _ _ h ↦ evalWalk_eq_of_homotopic T phi hphi h)
  map_id x := by
    change evalWalk T phi Quiver.Path.nil = 𝟙 _
    rw [evalWalk_nil]
  map_comp f g := by
    induction f, g using Quotient.inductionOn₂ with
    | _ p q =>
        change evalWalk T phi (p.comp q) =
          evalWalk T phi p ≫ evalWalk T phi q
        exact evalWalk_comp T phi p q

@[simp]
theorem lift_map_of
    (phi : AugmentedVertex T ⥤q C)
    (hphi : MeshCompatible T phi)
    {x y : AugmentedVertex T} (a : x ⟶ y) :
    (lift T phi hphi).map ((of T).map a) = phi.map a := by
  change evalWalk T phi (positiveArrow T a).toPath = phi.map a
  rw [evalWalk_toPath]
  rfl

/-- The descended functor extends the original augmented-quiver labelling. -/
theorem lift_spec
    (phi : AugmentedVertex T ⥤q C)
    (hphi : MeshCompatible T phi) :
    of T ⋙q (lift T phi hphi).toPrefunctor = phi := by
  fapply Prefunctor.ext
  · intro x
    rfl
  · intro x y a
    exact lift_map_of T phi hphi a

/-- A functor out of the mesh-homotopy groupoid automatically gives a
mesh-compatible labelling of the augmented quiver. -/
theorem of_comp_meshCompatible
    (F : HomotopyGroupoid T ⥤ C) :
    MeshCompatible T (of T ⋙q F.toPrefunctor) := by
  intro s a
  change F.map ((of T).map (AugmentedArrow.mesh s)) =
    F.map ((of T).map (AugmentedArrow.old a.2)) ≫
      F.map ((of T).map
        (AugmentedArrow.old ((T.arrowEquiv s a.1) a.2)))
  rw [← F.map_comp, of_mesh_eq_old_comp_old]

/-- Evaluating a walk with the labelling induced by an existing functor gives
that functor's value on the corresponding homotopy class. -/
private theorem evalWalk_of_comp
    (F : HomotopyGroupoid T ⥤ C)
    {x y : Quiver.Symmetrify (AugmentedVertex T)}
    (p : @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    evalWalk T (of T ⋙q F.toPrefunctor) p =
      F.map (Quotient.mk _ p) := by
  induction p with
  | nil =>
      change 𝟙 (F.obj (show HomotopyGroupoid T from x)) = F.map (𝟙 _)
      exact (F.map_id _).symm
  | cons p e ih =>
      change evalWalk T (of T ⋙q F.toPrefunctor) p ≫
          (Quiver.Symmetrify.lift (of T ⋙q F.toPrefunctor)).map e =
        F.map (Quotient.mk _ (p.cons e))
      rw [ih]
      rw [show F.map (Quotient.mk _ (p.cons e)) =
          F.map (Quotient.mk _ p) ≫ F.map (Quotient.mk _ e.toPath) by
        rw [← F.map_comp]
        rfl]
      cases e with
      | inl a => rfl
      | inr a =>
          congr 1
          change Groupoid.inv (F.map ((of T).map a)) =
            F.map (Quotient.mk _ (negativeArrow T a).toPath)
          rw [Groupoid.inv_eq_inv, ← F.map_inv]
          apply F.congr_map
          rw [← Groupoid.inv_eq_inv]
          change Quotient.mk _
              (reverseWalk T (positiveArrow T a).toPath) =
            Quotient.mk _ (negativeArrow T a).toPath
          rw [reverseWalk_toPath]
          rfl

/-- Descending the labelling induced by an existing functor recovers that
functor. -/
theorem lift_of_comp
    (F : HomotopyGroupoid T ⥤ C) :
    lift T (of T ⋙q F.toPrefunctor)
      (of_comp_meshCompatible T F) = F := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  dsimp
  induction f using Quotient.inductionOn with
  | _ p =>
      rw [Category.id_comp, Category.comp_id]
      change evalWalk T (of T ⋙q F.toPrefunctor) p =
        F.map (Quotient.mk _ p)
      exact evalWalk_of_comp T F p

/-- The mesh-compatible extension is unique. -/
theorem lift_unique
    (phi : AugmentedVertex T ⥤q C)
    (hphi : MeshCompatible T phi)
    (F : HomotopyGroupoid T ⥤ C)
    (hF : of T ⋙q F.toPrefunctor = phi) :
    F = lift T phi hphi := by
  subst phi
  exact (lift_of_comp T F).symm

/-- Naturality across a groupoid arrow implies naturality across its inverse. -/
private theorem naturality_inv_of_naturality
    (F G : HomotopyGroupoid T ⥤ C)
    (app : ∀ X, F.obj X ⟶ G.obj X)
    {X Y : HomotopyGroupoid T} (f : X ⟶ Y)
    (h : F.map f ≫ app Y = app X ≫ G.map f) :
    F.map (Groupoid.inv f) ≫ app X =
      app Y ≫ G.map (Groupoid.inv f) := by
  rw [Groupoid.inv_eq_inv, F.map_inv, G.map_inv]
  rw [← cancel_epi (F.map f)]
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Generator-wise naturality extends along a represented augmented walk. -/
private theorem naturality_quotient_of_generator
    (F G : HomotopyGroupoid T ⥤ C)
    (app : ∀ X, F.obj X ⟶ G.obj X)
    (naturalityOf : ∀ {X Y : AugmentedVertex T} (a : X ⟶ Y),
      F.map ((of T).map a) ≫ app Y =
        app X ≫ G.map ((of T).map a))
    {X Y : Q} (p : Walk T X Y) :
    F.map (Quotient.mk _ p) ≫ app Y =
      app X ≫ G.map (Quotient.mk _ p) := by
  induction p with
  | nil =>
      rw [show Quotient.mk _ Quiver.Path.nil =
          𝟙 (show HomotopyGroupoid T from X) by rfl,
        F.map_id, G.map_id, Category.id_comp, Category.comp_id]
  | @cons Z W p e ih =>
      let ep : Walk T (show Q from Z) (show Q from W) :=
        @Quiver.Hom.toPath
          (Quiver.Symmetrify (AugmentedVertex T))
          (Quiver.symmetrifyQuiver (AugmentedVertex T)) Z W e
      let pe : Walk T X (show Q from W) :=
        @Quiver.Path.cons
          (Quiver.Symmetrify (AugmentedVertex T))
          (Quiver.symmetrifyQuiver (AugmentedVertex T)) X Z W p e
      let fe :
          (show HomotopyGroupoid T from Z) ⟶
            (show HomotopyGroupoid T from W) :=
        Quotient.mk
          (homotopySetoid T (show Q from Z) (show Q from W)) ep
      have he :
          F.map fe ≫ app W = app Z ≫ G.map fe := by
        cases e with
        | inl a =>
            change F.map ((of T).map a) ≫ app ((of T).obj W) =
              app ((of T).obj Z) ≫ G.map ((of T).map a)
            exact naturalityOf a
        | inr a =>
            change F.map (Groupoid.inv ((of T).map a)) ≫
                app ((of T).obj W) =
              app ((of T).obj Z) ≫
                G.map (Groupoid.inv ((of T).map a))
            exact naturality_inv_of_naturality T F G app
              ((of T).map a) (naturalityOf a)
      rw [show Quotient.mk
            (homotopySetoid T X (show Q from W)) pe =
          Quotient.mk (homotopySetoid T X (show Q from Z)) p ≫ fe by rfl,
        F.map_comp, G.map_comp, Category.assoc, he,
        ← Category.assoc, ih, Category.assoc]

/-- A family of components natural on the augmented generators extends to a
natural transformation on the presented mesh-homotopy groupoid. -/
def natTransOfGenerator
    (F G : HomotopyGroupoid T ⥤ C)
    (app : ∀ X, F.obj X ⟶ G.obj X)
    (naturalityOf : ∀ {X Y : AugmentedVertex T} (a : X ⟶ Y),
      F.map ((of T).map a) ≫ app Y =
        app X ≫ G.map ((of T).map a)) :
    F ⟶ G where
  app := app
  naturality := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ p => exact naturality_quotient_of_generator T F G app naturalityOf p

end HomotopyGroupoid

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
