import MagnitudeConjecture.CategoryTheory.TranslationQuiverHomotopyGroupoidCover

/-!
# Lifting augmented walks through stable mesh covers

The path-star equivalence of a stable polarized mesh cover is exposed as an
explicit unique-lift operation, with projection, endpoint, and degree
formulas suitable for descent through augmented-walk homotopy.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData.Cover

universe v₁ v₂ w₁ w₂

open MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

variable {Q₁ : Type v₁} [Quiver.{w₁} Q₁]
variable {Q₂ : Type v₂} [Quiver.{w₂} Q₂]
variable {T₁ : RightMeshData Q₁} {T₂ : RightMeshData Q₂}

variable (C : Cover T₁ T₂)
variable (hstable₁ : T₁.projective = ∅) (hstable₂ : T₂.projective = ∅)
variable (hbijective₁ : Function.Bijective (T₁.stableTau hstable₁))
variable (hbijective₂ : Function.Bijective (T₂.stableTau hstable₂))

private theorem prefunctor_ext_of_map_heq
    {U : Type*} {V : Type*} [Quiver U] [Quiver V]
    {F G : Prefunctor U V}
    (hobj : ∀ x, F.obj x = G.obj x)
    (hmap : ∀ (x y : U) (a : x ⟶ y), F.map a ≍ G.map a) :
    F = G := by
  rcases F with ⟨Fobj, Fmap⟩
  rcases G with ⟨Gobj, Gmap⟩
  have hobj' : Fobj = Gobj := funext hobj
  subst Gobj
  congr
  funext x y a
  exact eq_of_heq (hmap x y a)

private theorem prefunctor_map_cast_heq
    {U : Type*} {V : Type*} [Quiver U] [Quiver V]
    (F : Prefunctor U V) {x y x' y' : U}
    (hx : x = x') (hy : y = y') (a : x ⟶ y) :
    F.map (Quiver.Hom.cast hx hy a) ≍ F.map a := by
  cases hx
  cases hy
  rfl

/-- Taking a homotopy quotient commutes heterogeneously with transport of a
walk's target endpoint. -/
private theorem quotient_mk_cast_target_heq
    {Q : Type*} [Quiver Q] (T : RightMeshData Q)
    {x y y' : Q} (p : Walk T x y) (h : y = y') :
    (Quotient.mk (homotopySetoid T x y) p) ≍
      Quotient.mk (homotopySetoid T x y')
        (@Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
          (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _
          rfl h p) := by
  subst y'
  rfl

/-- Lift a target augmented path star from a chosen source vertex. -/
def liftPathStar (x : Q₁) :
    Quiver.PathStar
        (show Quiver.Symmetrify (AugmentedVertex T₂) from
          C.toPrefunctor.obj x) →
      Quiver.PathStar
        (show Quiver.Symmetrify (AugmentedVertex T₁) from x) :=
  (C.symmetrifiedAugmentedPathStarEquiv hstable₁ hstable₂
    hbijective₁ hbijective₂ x).symm

/-- Lift one target symmetric augmented arrow from a chosen source vertex. -/
def liftArrowStar (x : Q₁) :
    Quiver.Star
        (show Quiver.Symmetrify (AugmentedVertex T₂) from
          C.toPrefunctor.obj x) →
      Quiver.Star
        (show Quiver.Symmetrify (AugmentedVertex T₁) from x) :=
  (Equiv.ofBijective
    (C.augmentedPrefunctor.symmetrify.star x)
    ((C.symmetrifiedAugmentedPrefunctor_isCovering hstable₁ hstable₂
      hbijective₁ hbijective₂).star_bijective
        (show Quiver.Symmetrify (AugmentedVertex T₁) from x))).symm

/-- The lifted arrow projects back to its target arrow star. -/
@[simp]
theorem star_map_liftArrowStar (x : Q₁)
    (A : Quiver.Star
      (show Quiver.Symmetrify (AugmentedVertex T₂) from
        C.toPrefunctor.obj x)) :
    C.augmentedPrefunctor.symmetrify.star x
        (C.liftArrowStar hstable₁ hstable₂
          hbijective₁ hbijective₂ x A) = A :=
  (Equiv.ofBijective
    (C.augmentedPrefunctor.symmetrify.star x)
    ((C.symmetrifiedAugmentedPrefunctor_isCovering hstable₁ hstable₂
      hbijective₁ hbijective₂).star_bijective
        (show Quiver.Symmetrify (AugmentedVertex T₁) from x))).apply_symm_apply A

/-- Lift one target symmetric augmented arrow, retaining its endpoint. -/
def liftArrow (x : Q₁) {y : Q₂}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂))
      (C.toPrefunctor.obj x) y) :
    Σ z : Q₁,
      @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₁))
        (Quiver.symmetrifyQuiver (AugmentedVertex T₁)) x z :=
  C.liftArrowStar hstable₁ hstable₂ hbijective₁ hbijective₂
    x ⟨y, e⟩

/-- The endpoint of a lifted arrow projects to its target endpoint. -/
theorem liftArrow_endpoint (x : Q₁) {y : Q₂}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂))
      (C.toPrefunctor.obj x) y) :
    C.toPrefunctor.obj
        (C.liftArrow hstable₁ hstable₂ hbijective₁ hbijective₂
          x e).1 = y := by
  exact congrArg Sigma.fst
    (C.star_map_liftArrowStar hstable₁ hstable₂
      hbijective₁ hbijective₂ x ⟨y, e⟩)

/-- The mapped lifted arrow with its target endpoint restored. -/
def mappedLiftArrow (x : Q₁) {y : Q₂}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂))
      (C.toPrefunctor.obj x) y) :
    @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂))
      (C.toPrefunctor.obj x) y :=
  @Quiver.Hom.cast (Quiver.Symmetrify (AugmentedVertex T₂))
    (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
    (C.liftArrow_endpoint hstable₁ hstable₂
      hbijective₁ hbijective₂ x e)
    (C.augmentedPrefunctor.symmetrify.map
      (C.liftArrow hstable₁ hstable₂ hbijective₁ hbijective₂
        x e).2)

/-- Mapping the lifted arrow and restoring its endpoint recovers the target
arrow. -/
@[simp]
theorem mappedLiftArrow_eq (x : Q₁) {y : Q₂}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂))
      (C.toPrefunctor.obj x) y) :
    C.mappedLiftArrow hstable₁ hstable₂
      hbijective₁ hbijective₂ x e = e := by
  have h := C.star_map_liftArrowStar hstable₁ hstable₂
    hbijective₁ hbijective₂ x ⟨y, e⟩
  let hy := congrArg Sigma.fst h
  have he := (Sigma.ext_iff.mp h).2
  unfold mappedLiftArrow
  rw [show C.liftArrow_endpoint hstable₁ hstable₂
      hbijective₁ hbijective₂ x e = hy from
    Subsingleton.elim _ _]
  exact (@Quiver.Hom.cast_eq_iff_heq
    (Quiver.Symmetrify (AugmentedVertex T₂))
    (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl hy _ _).2 he

/-- Lift one ordinary target arrow through the underlying quiver covering. -/
def liftOrdinaryArrow (x : Q₁) {y : Q₂}
    (a : C.toPrefunctor.obj x ⟶ y) :
    Σ z : Q₁, x ⟶ z :=
  (Equiv.ofBijective (C.toPrefunctor.star x)
    (C.isCovering.star_bijective x)).symm ⟨y, a⟩

/-- The lifted ordinary arrow projects back to its target arrow star. -/
@[simp]
theorem star_map_liftOrdinaryArrow (x : Q₁) {y : Q₂}
    (a : C.toPrefunctor.obj x ⟶ y) :
    C.toPrefunctor.star x (C.liftOrdinaryArrow x a) = ⟨y, a⟩ :=
  (Equiv.ofBijective (C.toPrefunctor.star x)
    (C.isCovering.star_bijective x)).apply_symm_apply ⟨y, a⟩

/-- The endpoint of an ordinary lifted arrow projects to the target
endpoint. -/
theorem liftOrdinaryArrow_endpoint (x : Q₁) {y : Q₂}
    (a : C.toPrefunctor.obj x ⟶ y) :
    C.toPrefunctor.obj (C.liftOrdinaryArrow x a).1 = y :=
  congrArg Sigma.fst (C.star_map_liftOrdinaryArrow x a)

/-- Mapping an ordinary lifted arrow and restoring its endpoint recovers the
target arrow. -/
@[simp]
theorem liftOrdinaryArrow_map_cast (x : Q₁) {y : Q₂}
    (a : C.toPrefunctor.obj x ⟶ y) :
    (C.toPrefunctor.map (C.liftOrdinaryArrow x a).2).cast rfl
        (C.liftOrdinaryArrow_endpoint x a) = a := by
  have h := C.star_map_liftOrdinaryArrow x a
  let hy := congrArg Sigma.fst h
  have ha := (Sigma.ext_iff.mp h).2
  rw [show C.liftOrdinaryArrow_endpoint x a = hy from
    Subsingleton.elim _ _]
  exact (Quiver.Hom.cast_eq_iff_heq rfl hy _ _).2 ha

private theorem cancelPath_eq_of_cast
    {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {x y y' : V} (a : x ⟶ y) (b : x ⟶ y') (h : y = y')
    (hab : a.cast rfl h = b) :
    a.toPath.comp (Quiver.reverse a).toPath =
      b.toPath.comp (Quiver.reverse b).toPath := by
  subst y'
  subst b
  rfl

/-- The lift projects back to the target path star literally. -/
@[simp]
theorem pathStar_map_liftPathStar (x : Q₁)
    (P : Quiver.PathStar
      (show Quiver.Symmetrify (AugmentedVertex T₂) from
        C.toPrefunctor.obj x)) :
    C.augmentedPrefunctor.symmetrify.pathStar x
        (C.liftPathStar hstable₁ hstable₂ hbijective₁ hbijective₂
          x P) = P :=
  (C.symmetrifiedAugmentedPathStarEquiv hstable₁ hstable₂
    hbijective₁ hbijective₂ x).apply_symm_apply P

/-- Lifting the image of a source path star returns that source path star. -/
@[simp]
theorem liftPathStar_pathStar_map (x : Q₁)
    (P : Quiver.PathStar
      (show Quiver.Symmetrify (AugmentedVertex T₁) from x)) :
    C.liftPathStar hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (C.augmentedPrefunctor.symmetrify.pathStar x P) = P :=
  (C.symmetrifiedAugmentedPathStarEquiv hstable₁ hstable₂
    hbijective₁ hbijective₂ x).symm_apply_apply P

private theorem path_comp_cast_target
    {V : Type*} [Quiver V] {a b c c' : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) (h : c = c') :
    (p.comp q).cast rfl h = p.comp (q.cast rfl h) := by
  subst c'
  rfl

private theorem path_comp_cast_middle
    {V : Type*} [Quiver V] {a b b' c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b' c) (h : b = b') :
    (p.cast rfl h).comp q = p.comp (q.cast h.symm rfl) := by
  subst b'
  rfl

private theorem cancelPath_cast_start
    {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {x x' y : V} (e : x ⟶ y) (h : x = x') :
    (e.toPath.comp (Quiver.reverse e).toPath).cast h rfl =
      ((e.cast h rfl).toPath.comp
        (Quiver.reverse (e.cast h rfl)).toPath).cast rfl h.symm := by
  subst x'
  rfl

private theorem positiveArrow_cast_toPath_inverse_target
    {Q : Type*} [Quiver Q] (T : RightMeshData Q)
    {x y y' : Q} (a : AugmentedArrow T x y') (h : y = y') :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _ rfl h
      (@Quiver.Hom.toPath (Quiver.Symmetrify (AugmentedVertex T))
        (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _
        (Sum.inl (@Quiver.Hom.cast (AugmentedVertex T)
          (augmentedQuiver T) _ _ _ _ rfl h.symm a))) =
      @Quiver.Hom.toPath (Quiver.Symmetrify (AugmentedVertex T))
        (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ (Sum.inl a) := by
  subst y'
  rfl

private theorem oldPairPath_cast_target
    {Q : Type*} [Quiver Q] (T : RightMeshData Q)
    {x y z z' : Q} (a : x ⟶ y) (b : y ⟶ z)
    (c : y ⟶ z') (h : z = z') (hb : b.cast rfl h = c) :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _ rfl h
      ((oldArrowPath T a).comp (oldArrowPath T b)) =
      (oldArrowPath T a).comp (oldArrowPath T c) := by
  subst z'
  subst c
  rfl

private theorem oldArrowPath_cast_target
    {Q : Type*} [Quiver Q] (T : RightMeshData Q)
    {x y y' : Q} (a : x ⟶ y) (b : x ⟶ y')
    (h : y = y') (hab : a.cast rfl h = b) :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _ rfl h
      (oldArrowPath T a) = oldArrowPath T b := by
  subst y'
  subst b
  rfl

private theorem oldArrowPath_cast_start
    {Q : Type*} [Quiver Q] (T : RightMeshData Q)
    {x x' y : Q} (a : x ⟶ y) (h : x = x') :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _ h rfl
      (oldArrowPath T a) = oldArrowPath T (a.cast h rfl) := by
  subst x'
  rfl

private theorem meshArrowPath_cast_start_eq
    {Q : Type*} [Quiver Q] (T : RightMeshData Q)
    (s s' : {s : Q // s ∉ T.projective}) (h : s = s') :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _ rfl
      (congrArg T.tau h) (meshArrowPath T s) =
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _
      (congrArg Subtype.val h).symm rfl (meshArrowPath T s') := by
  subst s'
  rfl

private theorem oldMeshRoute_cast_start_eq
    {Q : Type*} [Quiver Q] (T : RightMeshData Q)
    (s s' : {s : Q // s ∉ T.projective}) (h : s = s')
    (a : T.MeshArrow s') :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _ rfl
      (congrArg T.tau h)
      ((oldArrowPath T (h.symm ▸ a).2).comp
        (oldArrowPath T
          ((T.arrowEquiv s (h.symm ▸ a).1) (h.symm ▸ a).2))) =
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ _ _ _
      (congrArg Subtype.val h).symm rfl
      ((oldArrowPath T a.2).comp
        (oldArrowPath T ((T.arrowEquiv s' a.1) a.2))) := by
  subst s'
  rfl

/-- Lift one target augmented walk from a chosen source vertex, retaining its
lifted endpoint. -/
def liftWalk (x : Q₁) {y : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) :
    Σ z : Q₁, Walk T₁ x z :=
  C.liftPathStar hstable₁ hstable₂ hbijective₁ hbijective₂
    x ⟨y, p⟩

/-- A source walk is recovered by lifting its mapped walk. -/
@[simp]
theorem liftWalk_mapPath {x z : Q₁} (p : Walk T₁ x z) :
    C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (C.augmentedPrefunctor.symmetrify.mapPath p) =
      ⟨z, p⟩ :=
  C.liftPathStar_pathStar_map hstable₁ hstable₂
    hbijective₁ hbijective₂ x ⟨z, p⟩

/-- The endpoint of a lifted walk projects to its target endpoint. -/
theorem liftWalk_endpoint (x : Q₁) {y : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) :
    C.toPrefunctor.obj
        (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂
          x p).1 = y := by
  exact congrArg Sigma.fst
    (C.pathStar_map_liftPathStar hstable₁ hstable₂
      hbijective₁ hbijective₂ x ⟨y, p⟩)

/-- The mapped lift, with its target endpoint restored to the endpoint of the
original target walk. -/
def mappedLiftWalk (x : Q₁) {y : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) :
    Walk T₂ (C.toPrefunctor.obj x) y :=
  @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
    (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
    (C.liftWalk_endpoint hstable₁ hstable₂
      hbijective₁ hbijective₂ x p)
    (C.augmentedPrefunctor.symmetrify.mapPath
      (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂
        x p).2)

/-- Transport only the initial endpoint of a target augmented walk. -/
def castWalkStart (_C : Cover T₁ T₂) {x y x' : Q₂}
    (p : Walk T₂ x y) (h : x = x') :
    Walk T₂ x' y :=
  @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
    (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ h rfl p

/-- The mapped lifted walk agrees with the target walk after restoring the
dependent endpoint along `liftWalk_endpoint`. -/
theorem liftWalk_mapPath_cast (x : Q₁) {y : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) :
    C.mappedLiftWalk hstable₁ hstable₂ hbijective₁ hbijective₂
      x p = p := by
  have h := C.pathStar_map_liftPathStar hstable₁ hstable₂
    hbijective₁ hbijective₂ x ⟨y, p⟩
  let hy := congrArg Sigma.fst h
  have hp := (Sigma.ext_iff.mp h).2
  unfold mappedLiftWalk
  rw [show C.liftWalk_endpoint hstable₁ hstable₂
      hbijective₁ hbijective₂ x p = hy from
    Subsingleton.elim _ _]
  exact (Quiver.Path.cast_eq_iff_heq rfl hy _ _).2 hp

/-- Transporting only the target endpoint of a target walk does not change
its lifted source path star. -/
theorem liftWalk_cast_target (x : Q₁) {y y' : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) (h : y = y') :
    C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (@Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _
          rfl h p) =
      C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x p := by
  unfold liftWalk
  apply congrArg
  apply Sigma.ext h.symm
  exact (@Quiver.Path.cast_heq
    (Quiver.Symmetrify (AugmentedVertex T₂))
    (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl h p)

/-- Mapping the one-edge ordinary lift and restoring its endpoint gives the
original target ordinary-arrow walk. -/
theorem mapPath_liftOrdinaryArrow_cast (x : Q₁) {y : Q₂}
    (a : C.toPrefunctor.obj x ⟶ y) :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
      (C.liftOrdinaryArrow_endpoint x a)
      (C.augmentedPrefunctor.symmetrify.mapPath
        (oldArrowPath T₁ (C.liftOrdinaryArrow x a).2)) =
      oldArrowPath T₂ a := by
  change
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
      (C.liftOrdinaryArrow_endpoint x a)
      (oldArrowPath T₂
        (C.toPrefunctor.map (C.liftOrdinaryArrow x a).2)) =
      oldArrowPath T₂ a
  exact oldArrowPath_cast_target T₂ _ _
    (C.liftOrdinaryArrow_endpoint x a)
    (C.liftOrdinaryArrow_map_cast x a)

/-- The lift of a one-edge ordinary target walk is the one-edge ordinary
lift through the underlying quiver cover. -/
theorem liftWalk_oldArrowPath (x : Q₁) {y : Q₂}
    (a : C.toPrefunctor.obj x ⟶ y) :
    C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (oldArrowPath T₂ a) =
      ⟨(C.liftOrdinaryArrow x a).1,
        oldArrowPath T₁ (C.liftOrdinaryArrow x a).2⟩ := by
  calc
    _ = C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (@Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
          (C.liftOrdinaryArrow_endpoint x a)
          (C.augmentedPrefunctor.symmetrify.mapPath
            (oldArrowPath T₁ (C.liftOrdinaryArrow x a).2))) :=
      congrArg (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x)
        (C.mapPath_liftOrdinaryArrow_cast x a).symm
    _ = C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (C.augmentedPrefunctor.symmetrify.mapPath
          (oldArrowPath T₁ (C.liftOrdinaryArrow x a).2)) :=
      C.liftWalk_cast_target hstable₁ hstable₂
        hbijective₁ hbijective₂ x _
          (C.liftOrdinaryArrow_endpoint x a)
    _ = _ := C.liftWalk_mapPath hstable₁ hstable₂
      hbijective₁ hbijective₂ _

/-- Lifting a mapped source prefix followed by a target suffix concatenates
the source prefix with the lift of that suffix. -/
theorem liftWalk_mapPath_comp (x z : Q₁) (p : Walk T₁ x z)
    {y : Q₂} (q : Walk T₂ (C.toPrefunctor.obj z) y) :
    C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
        ((C.augmentedPrefunctor.symmetrify.mapPath p).comp q) =
      ⟨(C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂
          z q).1,
        p.comp
          (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂
            z q).2⟩ := by
  apply (C.symmetrifiedAugmentedPrefunctor_pathStar_bijective
    hstable₁ hstable₂ hbijective₁ hbijective₂ x).1
  change C.augmentedPrefunctor.symmetrify.pathStar x
      (C.liftPathStar hstable₁ hstable₂ hbijective₁ hbijective₂ x
        ⟨y, (C.augmentedPrefunctor.symmetrify.mapPath p).comp q⟩) = _
  rw [C.pathStar_map_liftPathStar hstable₁ hstable₂
    hbijective₁ hbijective₂]
  symm
  apply Sigma.ext
  · exact C.liftWalk_endpoint hstable₁ hstable₂
      hbijective₁ hbijective₂ z q
  · change HEq
      (C.augmentedPrefunctor.symmetrify.mapPath
        (p.comp (C.liftWalk hstable₁ hstable₂
          hbijective₁ hbijective₂ z q).2))
      ((C.augmentedPrefunctor.symmetrify.mapPath p).comp q)
    rw [Prefunctor.mapPath_comp]
    exact (@Quiver.Path.cast_eq_iff_heq
      (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
      (C.liftWalk_endpoint hstable₁ hstable₂
        hbijective₁ hbijective₂ z q)
      ((C.augmentedPrefunctor.symmetrify.mapPath p).comp
        (C.augmentedPrefunctor.symmetrify.mapPath
          (C.liftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ z q).2))
      ((C.augmentedPrefunctor.symmetrify.mapPath p).comp q)).1 (by
        rw [path_comp_cast_target]
        change (C.augmentedPrefunctor.symmetrify.mapPath p).comp
            (C.mappedLiftWalk hstable₁ hstable₂
              hbijective₁ hbijective₂ z q) = _
        rw [C.liftWalk_mapPath_cast hstable₁ hstable₂
          hbijective₁ hbijective₂ z q])

/-- Lifting an arbitrary composite first lifts its prefix and then lifts the
suffix from the resulting endpoint. -/
theorem liftWalk_comp (x : Q₁) {y z : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) (q : Walk T₂ y z) :
    let P := C.liftWalk hstable₁ hstable₂
      hbijective₁ hbijective₂ x p
    let q' := C.castWalkStart q
      (C.liftWalk_endpoint hstable₁ hstable₂
        hbijective₁ hbijective₂ x p).symm
    let Q := C.liftWalk hstable₁ hstable₂
      hbijective₁ hbijective₂ P.1 q'
    C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (p.comp q) =
      ⟨Q.1, P.2.comp Q.2⟩ := by
  dsimp only
  apply (C.symmetrifiedAugmentedPrefunctor_pathStar_bijective
    hstable₁ hstable₂ hbijective₁ hbijective₂ x).1
  change C.augmentedPrefunctor.symmetrify.pathStar x
      (C.liftPathStar hstable₁ hstable₂ hbijective₁ hbijective₂ x
        ⟨z, p.comp q⟩) = _
  rw [C.pathStar_map_liftPathStar hstable₁ hstable₂
    hbijective₁ hbijective₂]
  symm
  apply Sigma.ext
  · exact C.liftWalk_endpoint hstable₁ hstable₂
      hbijective₁ hbijective₂ _ _
  · change HEq
      (C.augmentedPrefunctor.symmetrify.mapPath
        ((C.liftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ x p).2.comp
          (C.liftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂
            (C.liftWalk hstable₁ hstable₂
              hbijective₁ hbijective₂ x p).1
            (C.castWalkStart q
              (C.liftWalk_endpoint hstable₁ hstable₂
                hbijective₁ hbijective₂ x p).symm)).2))
      (p.comp q)
    rw [Prefunctor.mapPath_comp]
    exact (@Quiver.Path.cast_eq_iff_heq
      (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
      (C.liftWalk_endpoint hstable₁ hstable₂
        hbijective₁ hbijective₂ _ _)
      ((C.augmentedPrefunctor.symmetrify.mapPath
          (C.liftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ x p).2).comp
        (C.augmentedPrefunctor.symmetrify.mapPath
          (C.liftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ _ _).2))
      (p.comp q)).1 (by
        rw [path_comp_cast_target]
        change (C.augmentedPrefunctor.symmetrify.mapPath
              (C.liftWalk hstable₁ hstable₂
                hbijective₁ hbijective₂ x p).2).comp
            (C.mappedLiftWalk hstable₁ hstable₂
              hbijective₁ hbijective₂ _ _) = p.comp q
        rw [C.liftWalk_mapPath_cast hstable₁ hstable₂
          hbijective₁ hbijective₂]
        change (C.augmentedPrefunctor.symmetrify.mapPath
              (C.liftWalk hstable₁ hstable₂
                hbijective₁ hbijective₂ x p).2).comp
            (C.castWalkStart q
              (C.liftWalk_endpoint hstable₁ hstable₂
                hbijective₁ hbijective₂ x p).symm) = p.comp q
        unfold castWalkStart
        rw [← path_comp_cast_middle]
        change (C.mappedLiftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ x p).comp q = p.comp q
        rw [C.liftWalk_mapPath_cast hstable₁ hstable₂
          hbijective₁ hbijective₂ x p])

/-- A lifted walk has the same signed degree as its target walk. -/
theorem liftWalk_walkDegree (x : Q₁) {y : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) :
    walkDegree T₁
        (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂
          x p).2 =
      walkDegree T₂ p := by
  calc
    _ = walkDegree T₂
          (C.augmentedPrefunctor.symmetrify.mapPath
            (C.liftWalk hstable₁ hstable₂
              hbijective₁ hbijective₂ x p).2) :=
      (C.walkDegree_symmetrifiedAugmentedPrefunctor_mapPath _).symm
    _ = walkDegree T₂
          (C.mappedLiftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ x p) := by
      exact (walkDegree_cast T₂ _ rfl
        (C.liftWalk_endpoint hstable₁ hstable₂
          hbijective₁ hbijective₂ x p)).symm
    _ = walkDegree T₂ p := by
      rw [C.liftWalk_mapPath_cast hstable₁ hstable₂
        hbijective₁ hbijective₂ x p]

/-- A target arrow followed by its formal reverse lifts to the corresponding
source arrow followed by its reverse, and therefore returns to its starting
source vertex. -/
theorem liftWalk_cancelPair (x : Q₁) {y : Q₂}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂))
      (C.toPrefunctor.obj x) y) :
    C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (e.toPath.comp (Quiver.reverse e).toPath) =
      ⟨x,
        (C.liftArrow hstable₁ hstable₂
          hbijective₁ hbijective₂ x e).2.toPath.comp
          (Quiver.reverse
            (C.liftArrow hstable₁ hstable₂
              hbijective₁ hbijective₂ x e).2).toPath⟩ := by
  apply (C.symmetrifiedAugmentedPrefunctor_pathStar_bijective
    hstable₁ hstable₂ hbijective₁ hbijective₂ x).1
  change C.augmentedPrefunctor.symmetrify.pathStar x
      (C.liftPathStar hstable₁ hstable₂ hbijective₁ hbijective₂ x
        ⟨C.toPrefunctor.obj x,
          e.toPath.comp (Quiver.reverse e).toPath⟩) = _
  rw [C.pathStar_map_liftPathStar hstable₁ hstable₂
    hbijective₁ hbijective₂]
  symm
  apply Sigma.ext
  · rfl
  · change HEq
      (C.augmentedPrefunctor.symmetrify.mapPath
        ((C.liftArrow hstable₁ hstable₂
            hbijective₁ hbijective₂ x e).2.toPath.comp
          (Quiver.reverse
            (C.liftArrow hstable₁ hstable₂
              hbijective₁ hbijective₂ x e).2).toPath))
      (e.toPath.comp (Quiver.reverse e).toPath)
    rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath,
      Prefunctor.mapPath_toPath, Prefunctor.map_reverse]
    exact heq_of_eq (cancelPath_eq_of_cast
      (C.augmentedPrefunctor.symmetrify.map
        (C.liftArrow hstable₁ hstable₂
          hbijective₁ hbijective₂ x e).2) e
      (C.liftArrow_endpoint hstable₁ hstable₂
        hbijective₁ hbijective₂ x e)
      (C.mappedLiftArrow_eq hstable₁ hstable₂
        hbijective₁ hbijective₂ x e))

/-- Appending a target arrow and its formal reverse to any prefix does not
change the endpoint of the lifted prefix. -/
theorem liftWalk_cancel_endpoint (x : Q₁) {y z : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y)
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) y z) :
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
      ((p.comp e.toPath).comp (Quiver.reverse e).toPath)).1 =
        (C.liftWalk hstable₁ hstable₂
          hbijective₁ hbijective₂ x p).1 := by
  rw [Quiver.Path.comp_assoc]
  rw [C.liftWalk_comp hstable₁ hstable₂
    hbijective₁ hbijective₂]
  let P := C.liftWalk hstable₁ hstable₂
    hbijective₁ hbijective₂ x p
  let hP := C.liftWalk_endpoint hstable₁ hstable₂
    hbijective₁ hbijective₂ x p
  let e' : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂))
      (C.toPrefunctor.obj P.1) z :=
    Quiver.Hom.cast hP.symm rfl e
  change (C.liftWalk hstable₁ hstable₂
      hbijective₁ hbijective₂ P.1
      (C.castWalkStart
        (e.toPath.comp (Quiver.reverse e).toPath) hP.symm)).1 = P.1
  rw [show C.castWalkStart
      (e.toPath.comp (Quiver.reverse e).toPath) hP.symm =
        @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl hP
          (e'.toPath.comp (Quiver.reverse e').toPath) from by
    unfold castWalkStart e'
    exact cancelPath_cast_start e hP.symm]
  rw [C.liftWalk_cast_target hstable₁ hstable₂
    hbijective₁ hbijective₂]
  rw [C.liftWalk_cancelPair hstable₁ hstable₂
    hbijective₁ hbijective₂]

/-- The augmented cover sends a source formal mesh edge to the target formal
mesh edge after restoring the translated endpoint. -/
theorem mapPath_meshArrowPath_cast
    (s : {s : Q₁ // s ∉ T₁.projective}) :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
        (congrArg
          (fun z : Q₂ ↦
            show Quiver.Symmetrify (AugmentedVertex T₂) from z)
          (C.map_tau s))
      (C.augmentedPrefunctor.symmetrify.mapPath
        (meshArrowPath T₁ s)) =
      meshArrowPath T₂ (C.mapNonprojective s) := by
  change
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
        (congrArg
          (fun z : Q₂ ↦
            show Quiver.Symmetrify (AugmentedVertex T₂) from z)
          (C.map_tau s))
      (@Quiver.Hom.toPath (Quiver.Symmetrify (AugmentedVertex T₂))
        (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _
        (Sum.inl (@Quiver.Hom.cast (AugmentedVertex T₂)
          (augmentedQuiver T₂) _ _ _ _ rfl
          (congrArg
            (fun z : Q₂ ↦ show AugmentedVertex T₂ from z)
            (C.map_tau s).symm)
          (AugmentedArrow.mesh (C.mapNonprojective s))))) =
      meshArrowPath T₂ (C.mapNonprojective s)
  exact positiveArrow_cast_toPath_inverse_target T₂ _ (C.map_tau s)

/-- The augmented cover sends a source polarized length-two mesh route to
the corresponding target route after restoring the translated endpoint. -/
theorem mapPath_oldMeshRoute_cast
    (s : {s : Q₁ // s ∉ T₁.projective}) (a : T₁.MeshArrow s) :
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
        (congrArg
          (fun z : Q₂ ↦
            show Quiver.Symmetrify (AugmentedVertex T₂) from z)
          (C.map_tau s))
      (C.augmentedPrefunctor.symmetrify.mapPath
        ((oldArrowPath T₁ a.2).comp
          (oldArrowPath T₁ ((T₁.arrowEquiv s a.1) a.2)))) =
      (oldArrowPath T₂ (C.toPrefunctor.map a.2)).comp
      (oldArrowPath T₂
          ((T₂.arrowEquiv (C.mapNonprojective s)
            (C.toPrefunctor.obj a.1)) (C.toPrefunctor.map a.2))) := by
  change
    @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
        (C.map_tau s)
      ((oldArrowPath T₂ (C.toPrefunctor.map a.2)).comp
        (oldArrowPath T₂
          (C.toPrefunctor.map ((T₁.arrowEquiv s a.1) a.2)))) = _
  exact oldPairPath_cast_target T₂
    (C.toPrefunctor.map a.2)
    (C.toPrefunctor.map ((T₁.arrowEquiv s a.1) a.2))
    ((T₂.arrowEquiv (C.mapNonprojective s)
      (C.toPrefunctor.obj a.1)) (C.toPrefunctor.map a.2))
    (C.map_tau s) (C.map_arrowEquiv s a.1 a.2)

/-- A formal mesh edge and any corresponding polarized target length-two
route have lifts with the same endpoint. -/
theorem liftWalk_mesh_endpoint
    (s : {s : Q₁ // s ∉ T₁.projective}) (a : T₁.MeshArrow s) :
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1
      (meshArrowPath T₂ (C.mapNonprojective s))).1 =
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1
      ((oldArrowPath T₂ (C.toPrefunctor.map a.2)).comp
        (oldArrowPath T₂
          ((T₂.arrowEquiv (C.mapNonprojective s)
            (C.toPrefunctor.obj a.1)) (C.toPrefunctor.map a.2))))).1 := by
  calc
    _ = (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1
        (@Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
          (C.map_tau s)
          (C.augmentedPrefunctor.symmetrify.mapPath
            (meshArrowPath T₁ s)))).1 :=
      congrArg (fun p ↦
        (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1 p).1)
        (C.mapPath_meshArrowPath_cast s).symm
    _ = (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1
        (C.augmentedPrefunctor.symmetrify.mapPath
          (meshArrowPath T₁ s))).1 :=
      congrArg Sigma.fst
        (C.liftWalk_cast_target hstable₁ hstable₂
          hbijective₁ hbijective₂ s.1 _ (C.map_tau s))
    _ = T₁.tau s := congrArg Sigma.fst
      (C.liftWalk_mapPath hstable₁ hstable₂
        hbijective₁ hbijective₂ (meshArrowPath T₁ s))
    _ = (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1
        (C.augmentedPrefunctor.symmetrify.mapPath
          ((oldArrowPath T₁ a.2).comp
            (oldArrowPath T₁ ((T₁.arrowEquiv s a.1) a.2))))).1 :=
      (congrArg Sigma.fst
        (C.liftWalk_mapPath hstable₁ hstable₂
          hbijective₁ hbijective₂
          ((oldArrowPath T₁ a.2).comp
            (oldArrowPath T₁ ((T₁.arrowEquiv s a.1) a.2))))).symm
    _ = (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1
        (@Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl
          (C.map_tau s)
          (C.augmentedPrefunctor.symmetrify.mapPath
            ((oldArrowPath T₁ a.2).comp
              (oldArrowPath T₁ ((T₁.arrowEquiv s a.1) a.2)))))).1 :=
      (congrArg Sigma.fst
        (C.liftWalk_cast_target hstable₁ hstable₂
          hbijective₁ hbijective₂ s.1 _ (C.map_tau s))).symm
    _ = _ := congrArg (fun p ↦
      (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1 p).1)
      (C.mapPath_oldMeshRoute_cast s a)

/-- The local lifted-mesh endpoint formula expressed using an arbitrary
target incoming mesh arrow. -/
theorem liftWalk_mesh_endpoint_target
    (s : {s : Q₁ // s ∉ T₁.projective})
    (a : T₂.MeshArrow (C.mapNonprojective s)) :
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1
      (meshArrowPath T₂ (C.mapNonprojective s))).1 =
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ s.1
      ((oldArrowPath T₂ a.2).comp
        (oldArrowPath T₂
          ((T₂.arrowEquiv (C.mapNonprojective s) a.1) a.2)))).1 := by
  let b : T₁.MeshArrow s := (C.meshArrowEquiv s).symm a
  have hb : C.meshArrowEquiv s b = a :=
    (C.meshArrowEquiv s).apply_symm_apply a
  rw [← hb]
  exact C.liftWalk_mesh_endpoint hstable₁ hstable₂
    hbijective₁ hbijective₂ s b

/-- Appending a target mesh move to any prefix does not change the endpoint
of its lift. -/
theorem liftWalk_mesh_endpoint_after_prefix (x : Q₁)
    (s : {s : Q₂ // s ∉ T₂.projective})
    (p : Walk T₂ (C.toPrefunctor.obj x) s.1) (a : T₂.MeshArrow s) :
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
      (p.comp (meshArrowPath T₂ s))).1 =
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
      ((p.comp (oldArrowPath T₂ a.2)).comp
        (oldArrowPath T₂ ((T₂.arrowEquiv s a.1) a.2)))).1 := by
  let P := C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x p
  let hP := C.liftWalk_endpoint hstable₁ hstable₂
    hbijective₁ hbijective₂ x p
  rw [Quiver.Path.comp_assoc]
  rw [C.liftWalk_comp hstable₁ hstable₂ hbijective₁ hbijective₂]
  rw [C.liftWalk_comp hstable₁ hstable₂ hbijective₁ hbijective₂]
  change
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1
      (C.castWalkStart (meshArrowPath T₂ s) hP.symm)).1 =
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1
      (C.castWalkStart
        ((oldArrowPath T₂ a.2).comp
          (oldArrowPath T₂ ((T₂.arrowEquiv s a.1) a.2))) hP.symm)).1
  let sp := T₁.stableNonprojective hstable₁ P.1
  have hs : C.mapNonprojective sp = s := Subtype.ext hP
  let a' : T₂.MeshArrow (C.mapNonprojective sp) := hs.symm ▸ a
  let ht : T₂.tau (C.mapNonprojective sp) = T₂.tau s :=
    congrArg T₂.tau hs
  let qmesh : Walk T₂ (C.toPrefunctor.obj P.1)
      (T₂.tau (C.mapNonprojective sp)) :=
    meshArrowPath T₂ (C.mapNonprojective sp)
  let qold : Walk T₂ (C.toPrefunctor.obj P.1)
      (T₂.tau (C.mapNonprojective sp)) :=
    (oldArrowPath T₂ a'.2).comp
      (oldArrowPath T₂
        ((T₂.arrowEquiv (C.mapNonprojective sp) a'.1) a'.2))
  have hmesh :
      @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
        (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl ht
        qmesh = C.castWalkStart (meshArrowPath T₂ s) hP.symm := by
    simpa only [ht, qmesh, sp, RightMeshData.stableNonprojective,
      mapNonprojective, mappedNonprojective, castWalkStart] using
      meshArrowPath_cast_start_eq T₂ (C.mapNonprojective sp) s hs
  have hold :
      @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
        (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl ht
        qold =
      C.castWalkStart
        ((oldArrowPath T₂ a.2).comp
          (oldArrowPath T₂ ((T₂.arrowEquiv s a.1) a.2))) hP.symm := by
    simpa only [ht, qold, a', sp, RightMeshData.stableNonprojective,
      mapNonprojective, mappedNonprojective, castWalkStart] using
      oldMeshRoute_cast_start_eq T₂ (C.mapNonprojective sp) s hs a
  calc
    _ = (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1
        (@Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl ht
          qmesh)).1 := congrArg (fun q ↦
      (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1 q).1)
      hmesh.symm
    _ = (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1
        qmesh).1 := congrArg Sigma.fst
      (C.liftWalk_cast_target hstable₁ hstable₂
        hbijective₁ hbijective₂ P.1 qmesh ht)
    _ = (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1
        qold).1 := by
      simpa only [qmesh, qold, a', sp,
        RightMeshData.stableNonprojective] using
        C.liftWalk_mesh_endpoint_target hstable₁ hstable₂
          hbijective₁ hbijective₂ sp a'
    _ = (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1
        (@Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _ rfl ht
          qold)).1 := (congrArg Sigma.fst
      (C.liftWalk_cast_target hstable₁ hstable₂
        hbijective₁ hbijective₂ P.1 qold ht)).symm
    _ = _ := congrArg (fun q ↦
      (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1 q).1)
      hold

/-- Lifting the same target suffix from equal source vertices gives equal
endpoints, independently of the endpoint-equality witnesses used to restore
its start. -/
theorem liftWalk_castWalkStart_endpoint_eq_of_eq
    (x x' : Q₁) (hxx' : x = x') {y z : Q₂} (r : Walk T₂ y z)
    (hx : C.toPrefunctor.obj x = y)
    (hx' : C.toPrefunctor.obj x' = y) :
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
      (C.castWalkStart r hx.symm)).1 =
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x'
      (C.castWalkStart r hx'.symm)).1 := by
  subst x'
  rfl

/-- Homotopic target augmented walks have lifts with the same endpoint. -/
theorem liftWalk_endpoint_eq_of_homotopic (x : Q₁) {y : Q₂}
    {p q : Walk T₂ (C.toPrefunctor.obj x) y}
    (h : Homotopic T₂ (C.toPrefunctor.obj x) p q) :
    (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x p).1 =
      (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x q).1 := by
  induction h with
  | refl p => rfl
  | symm h ih => exact ih.symm
  | trans hpq hqr ihpq ihqr => exact ihpq.trans ihqr
  | comp h r ih =>
      rw [C.liftWalk_comp hstable₁ hstable₂ hbijective₁ hbijective₂]
      rw [C.liftWalk_comp hstable₁ hstable₂ hbijective₁ hbijective₂]
      exact C.liftWalk_castWalkStart_endpoint_eq_of_eq
        hstable₁ hstable₂ hbijective₁ hbijective₂ _ _ ih r
        (C.liftWalk_endpoint hstable₁ hstable₂
          hbijective₁ hbijective₂ x _)
        (C.liftWalk_endpoint hstable₁ hstable₂
          hbijective₁ hbijective₂ x _)
  | cancel p e =>
      exact C.liftWalk_cancel_endpoint hstable₁ hstable₂
        hbijective₁ hbijective₂ x p e
  | mesh s p a =>
      exact C.liftWalk_mesh_endpoint_after_prefix hstable₁ hstable₂
        hbijective₁ hbijective₂ x s p a

/-- A mesh cover maps source based-walk vertices to target based-walk
vertices by applying its induced functor on mesh-homotopy classes. -/
def mapUniversalVertex (x : Q₁) :
    Vertex T₁ x → Vertex T₂ (C.toPrefunctor.obj x) :=
  fun W ↦ ⟨C.toPrefunctor.obj W.1, C.homotopyFunctor.map W.2⟩

/-- On a represented source vertex, `mapUniversalVertex` is represented by
the pointwise image of its augmented walk. -/
@[simp]
theorem mapUniversalVertex_mk (x z : Q₁) (p : Walk T₁ x z) :
    C.mapUniversalVertex x ⟨z, Quotient.mk _ p⟩ =
      ⟨C.toPrefunctor.obj z,
        Quotient.mk _
          (C.augmentedPrefunctor.symmetrify.mapPath p)⟩ := by
  change
    (⟨C.toPrefunctor.obj z,
      C.homotopyFunctor.map (Quotient.mk _ p)⟩ :
        Vertex T₂ (C.toPrefunctor.obj x)) = _
  fapply Sigma.ext
  · rfl
  · apply heq_of_eq
    exact C.homotopyFunctor_map_mk p

/-- Lift a vertex of the target augmented-walk universal cover to the source
vertex determined by any representative walk. -/
def liftVertex (x : Q₁) :
    Vertex T₂ (C.toPrefunctor.obj x) → Q₁ :=
  fun W ↦ Quotient.lift
    (fun p : Walk T₂ (C.toPrefunctor.obj x) W.1 ↦
      (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x p).1)
    (fun _ _ h ↦ C.liftWalk_endpoint_eq_of_homotopic
      hstable₁ hstable₂ hbijective₁ hbijective₂ x h) W.2

/-- On a represented target universal-cover vertex, `liftVertex` is the
endpoint of the explicit lifted walk. -/
@[simp]
theorem liftVertex_mk (x : Q₁) {y : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) :
    C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x
        ⟨y, Quotient.mk _ p⟩ =
      (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x p).1 :=
  rfl

/-- Mapping the source universal-cover vertex represented by a lifted target
walk recovers the original represented target vertex. -/
theorem mapUniversalVertex_liftWalk (x : Q₁) {y : Q₂}
    (p : Walk T₂ (C.toPrefunctor.obj x) y) :
    C.mapUniversalVertex x
        ⟨(C.liftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ x p).1,
          Quotient.mk _
            (C.liftWalk hstable₁ hstable₂
              hbijective₁ hbijective₂ x p).2⟩ =
      ⟨y, Quotient.mk _ p⟩ := by
  let L := C.liftWalk hstable₁ hstable₂
    hbijective₁ hbijective₂ x p
  have hL : C.toPrefunctor.obj L.1 = y :=
    C.liftWalk_endpoint hstable₁ hstable₂
      hbijective₁ hbijective₂ x p
  have hp := C.liftWalk_mapPath_cast hstable₁ hstable₂
    hbijective₁ hbijective₂ x p
  unfold mappedLiftWalk at hp
  rw [show C.liftWalk_endpoint hstable₁ hstable₂
      hbijective₁ hbijective₂ x p = hL from
    Subsingleton.elim _ _] at hp
  change
    (⟨C.toPrefunctor.obj L.1,
      C.homotopyFunctor.map (Quotient.mk _ L.2)⟩ :
        Vertex T₂ (C.toPrefunctor.obj x)) = _
  apply Sigma.ext hL
  refine HEq.trans (heq_of_eq (C.homotopyFunctor_map_mk L.2)) ?_
  refine HEq.trans
    (quotient_mk_cast_target_heq T₂
      (C.augmentedPrefunctor.symmetrify.mapPath L.2) hL) ?_
  apply heq_of_eq
  have hp' :
      @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _
          rfl hL
          (C.augmentedPrefunctor.symmetrify.mapPath L.2) = p := by
    change
      @Quiver.Path.cast (Quiver.Symmetrify (AugmentedVertex T₂))
          (Quiver.symmetrifyQuiver (AugmentedVertex T₂)) _ _ _ _
          rfl hL
          (C.augmentedPrefunctor.symmetrify.mapPath
            (C.liftWalk hstable₁ hstable₂
              hbijective₁ hbijective₂ x p).2) = p
    exact hp
  exact congrArg
    (fun q : Walk T₂ (C.toPrefunctor.obj x) y ↦ Quotient.mk _ q) hp'

/-- The lifted universal-cover vertex lies over its recorded target
endpoint. -/
theorem liftVertex_projection (x : Q₁)
    (W : Vertex T₂ (C.toPrefunctor.obj x)) :
    C.toPrefunctor.obj
        (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x W) =
      W.1 := by
  rcases W with ⟨y, W⟩
  induction W using Quotient.inductionOn with
  | _ p =>
      exact C.liftWalk_endpoint hstable₁ hstable₂
        hbijective₁ hbijective₂ x p

/-- Extending a target universal-cover vertex by an ordinary arrow lifts to
the endpoint of the corresponding ordinary source-arrow lift. -/
theorem liftVertex_extendOld (x : Q₁)
    (W : Vertex T₂ (C.toPrefunctor.obj x)) {z : Q₂} (a : W.1 ⟶ z) :
    C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x
        (extendOld T₂ (C.toPrefunctor.obj x) W a) =
      (C.liftOrdinaryArrow
        (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x W)
        (a.cast
          (C.liftVertex_projection hstable₁ hstable₂
            hbijective₁ hbijective₂ x W).symm rfl)).1 := by
  rcases W with ⟨y, W⟩
  induction W using Quotient.inductionOn with
  | _ p =>
      let P := C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x p
      let hP := C.liftWalk_endpoint hstable₁ hstable₂
        hbijective₁ hbijective₂ x p
      let a' : C.toPrefunctor.obj P.1 ⟶ z := a.cast hP.symm rfl
      change
        (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ x
          (p.comp (oldArrowPath T₂ a))).1 =
        (C.liftOrdinaryArrow P.1 a').1
      rw [C.liftWalk_comp hstable₁ hstable₂ hbijective₁ hbijective₂]
      change
        (C.liftWalk hstable₁ hstable₂ hbijective₁ hbijective₂ P.1
          (C.castWalkStart (oldArrowPath T₂ a) hP.symm)).1 = _
      rw [show C.castWalkStart (oldArrowPath T₂ a) hP.symm =
          oldArrowPath T₂ a' from by
        unfold castWalkStart a'
        exact oldArrowPath_cast_start T₂ a hP.symm]
      exact congrArg Sigma.fst
        (C.liftWalk_oldArrowPath hstable₁ hstable₂
          hbijective₁ hbijective₂ P.1 a')

/-- The based-walk universal cover of the target maps canonically to any
stable mesh cover after choosing a source vertex over its base. -/
def liftVertexPrefunctor (x : Q₁) :
    Vertex T₂ (C.toPrefunctor.obj x) ⥤q Q₁ where
  obj := C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x
  map {W Z} A := by
    let a' : C.toPrefunctor.obj
        (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x W) ⟶
        Z.1 :=
      A.1.cast
        (C.liftVertex_projection hstable₁ hstable₂
          hbijective₁ hbijective₂ x W).symm rfl
    let L := C.liftOrdinaryArrow
      (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x W) a'
    have hL : L.1 =
        C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x Z := by
      calc
        L.1 = C.liftVertex hstable₁ hstable₂
            hbijective₁ hbijective₂ x
            (extendOld T₂ (C.toPrefunctor.obj x) W A.1) :=
          (C.liftVertex_extendOld hstable₁ hstable₂
            hbijective₁ hbijective₂ x W A.1).symm
        _ = C.liftVertex hstable₁ hstable₂
            hbijective₁ hbijective₂ x Z := congrArg
          (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x) A.2
    exact L.2.cast rfl hL

@[simp]
theorem liftVertexPrefunctor_obj (x : Q₁)
    (W : Vertex T₂ (C.toPrefunctor.obj x)) :
    (C.liftVertexPrefunctor hstable₁ hstable₂
      hbijective₁ hbijective₂ x).obj W =
      C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x W :=
  rfl

/-- The map of a lifted universal-cover arrow projects to its underlying
target arrow, up to the endpoint transports forced by the dependent vertex
lift. -/
theorem liftVertexPrefunctor_map_heq (x : Q₁)
    {W Z : Vertex T₂ (C.toPrefunctor.obj x)}
    (A : W ⟶ Z) :
    C.toPrefunctor.map
        ((C.liftVertexPrefunctor hstable₁ hstable₂
          hbijective₁ hbijective₂ x).map A) ≍ A.1 := by
  let hW := C.liftVertex_projection hstable₁ hstable₂
    hbijective₁ hbijective₂ x W
  let a' : C.toPrefunctor.obj
      (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x W) ⟶
      Z.1 := A.1.cast hW.symm rfl
  let L := C.liftOrdinaryArrow
    (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x W) a'
  let hL : L.1 =
      C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x Z := by
    calc
      L.1 = C.liftVertex hstable₁ hstable₂
          hbijective₁ hbijective₂ x
          (extendOld T₂ (C.toPrefunctor.obj x) W A.1) :=
        (C.liftVertex_extendOld hstable₁ hstable₂
          hbijective₁ hbijective₂ x W A.1).symm
      _ = C.liftVertex hstable₁ hstable₂
          hbijective₁ hbijective₂ x Z := congrArg
        (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x) A.2
  change C.toPrefunctor.map (L.2.cast rfl hL) ≍ A.1
  exact (prefunctor_map_cast_heq C.toPrefunctor rfl hL L.2).trans
    ((Quiver.Hom.cast_heq rfl (C.liftOrdinaryArrow_endpoint _ a')
      (C.toPrefunctor.map L.2)).symm.trans
        ((heq_of_eq (C.liftOrdinaryArrow_map_cast _ a')).trans
          (Quiver.Hom.cast_heq hW.symm rfl A.1)))

/-- The canonical universal-cover lift lies over the target universal-cover
projection as a quiver prefunctor. -/
theorem liftVertexPrefunctor_comp_projection (x : Q₁) :
    C.liftVertexPrefunctor hstable₁ hstable₂ hbijective₁ hbijective₂ x ⋙q
        C.toPrefunctor =
      projection T₂ (C.toPrefunctor.obj x) := by
  apply prefunctor_ext_of_map_heq
  · intro W
    exact C.liftVertex_projection hstable₁ hstable₂
      hbijective₁ hbijective₂ x W
  · intro W Z A
    exact C.liftVertexPrefunctor_map_heq hstable₁ hstable₂
      hbijective₁ hbijective₂ x A

/-- The canonical map from the target based-walk universal cover to a stable
mesh cover is itself a quiver covering. -/
theorem liftVertexPrefunctor_isCovering (x : Q₁) :
    (C.liftVertexPrefunctor hstable₁ hstable₂
      hbijective₁ hbijective₂ x).IsCovering := by
  constructor
  · intro W
    have hcomp : Function.Bijective
        ((C.liftVertexPrefunctor hstable₁ hstable₂
          hbijective₁ hbijective₂ x ⋙q C.toPrefunctor).star W) := by
      rw [C.liftVertexPrefunctor_comp_projection hstable₁ hstable₂
        hbijective₁ hbijective₂ x]
      exact projection_star_bijective T₂ (C.toPrefunctor.obj x) W
    change Function.Bijective
      (C.toPrefunctor.star
          ((C.liftVertexPrefunctor hstable₁ hstable₂
            hbijective₁ hbijective₂ x).obj W) ∘
        (C.liftVertexPrefunctor hstable₁ hstable₂
          hbijective₁ hbijective₂ x).star W) at hcomp
    exact (Function.Bijective.of_comp_iff'
      (C.isCovering.star_bijective _) _).mp hcomp
  · intro W
    have hcomp : Function.Bijective
        ((C.liftVertexPrefunctor hstable₁ hstable₂
          hbijective₁ hbijective₂ x ⋙q C.toPrefunctor).costar W) := by
      rw [C.liftVertexPrefunctor_comp_projection hstable₁ hstable₂
        hbijective₁ hbijective₂ x]
      exact projection_costar_bijective T₂ (C.toPrefunctor.obj x) W
    change Function.Bijective
      (C.toPrefunctor.costar
          ((C.liftVertexPrefunctor hstable₁ hstable₂
            hbijective₁ hbijective₂ x).obj W) ∘
        (C.liftVertexPrefunctor hstable₁ hstable₂
          hbijective₁ hbijective₂ x).costar W) at hcomp
    exact (Function.Bijective.of_comp_iff'
      (C.isCovering.costar_bijective _) _).mp hcomp

/-- A target universal-cover vertex represented by the image of a source
walk lifts back to the endpoint of that source walk. -/
@[simp]
theorem liftVertex_mappedWalk (x z : Q₁) (p : Walk T₁ x z) :
    C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x
        ⟨C.toPrefunctor.obj z,
          Quotient.mk _
            (C.augmentedPrefunctor.symmetrify.mapPath p)⟩ = z := by
  exact congrArg Sigma.fst
    (C.liftWalk_mapPath hstable₁ hstable₂
      hbijective₁ hbijective₂ p)

/-- If every source vertex is reachable from the chosen source base by an
augmented walk, then every source vertex occurs as the lift of a target
universal-cover vertex. -/
theorem liftVertex_surjective (x : Q₁)
    (hconnected : IsWalkConnectedAt T₁ x) :
    Function.Surjective
      (C.liftVertex hstable₁ hstable₂ hbijective₁ hbijective₂ x) := by
  intro z
  obtain ⟨p⟩ := hconnected z
  exact ⟨⟨C.toPrefunctor.obj z,
    Quotient.mk _ (C.augmentedPrefunctor.symmetrify.mapPath p)⟩,
    C.liftVertex_mappedWalk hstable₁ hstable₂
      hbijective₁ hbijective₂ x z p⟩

/-- The object map of the canonical universal-cover comparison is
surjective whenever the source cover is augmented-walk connected at its
chosen base. -/
theorem liftVertexPrefunctor_obj_surjective (x : Q₁)
    (hconnected : IsWalkConnectedAt T₁ x) :
    Function.Surjective
      (C.liftVertexPrefunctor hstable₁ hstable₂
        hbijective₁ hbijective₂ x).obj :=
  C.liftVertex_surjective hstable₁ hstable₂
    hbijective₁ hbijective₂ x hconnected

/-- If the source mesh-homotopy groupoid is thin at the chosen base, then
the universal-cover comparison is injective on vertices. -/
theorem liftVertex_injective (x : Q₁)
    (hsimple : ∀ {z : Q₁} (p q : Walk T₁ x z),
      Homotopic T₁ x p q) :
    Function.Injective
      (C.liftVertex hstable₁ hstable₂
        hbijective₁ hbijective₂ x) := by
  rintro ⟨y, W⟩ ⟨z, Z⟩ h
  induction W using Quotient.inductionOn with
  | _ p =>
      induction Z using Quotient.inductionOn with
      | _ q =>
          let Lp := C.liftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ x p
          let Lq := C.liftWalk hstable₁ hstable₂
            hbijective₁ hbijective₂ x q
          have hendpoint : Lp.1 = Lq.1 := h
          have hsource :
              (⟨Lp.1, Quotient.mk _ Lp.2⟩ : Vertex T₁ x) =
                ⟨Lq.1, Quotient.mk _ Lq.2⟩ := by
            fapply Sigma.ext
            · exact hendpoint
            let Lq' : Walk T₁ x Lp.1 :=
              @Quiver.Path.cast
                (Quiver.Symmetrify (AugmentedVertex T₁))
                (Quiver.symmetrifyQuiver (AugmentedVertex T₁))
                _ _ _ _ rfl hendpoint.symm Lq.2
            refine HEq.trans ?_
              (quotient_mk_cast_target_heq T₁
                Lq.2 hendpoint.symm).symm
            apply heq_of_eq
            exact Quotient.sound (hsimple Lp.2 Lq')
          have hpRecover :
              C.mapUniversalVertex x
                    ⟨Lp.1, Quotient.mk _ Lp.2⟩ =
                (⟨y, Quotient.mk _ p⟩ : Vertex T₂
                  (C.toPrefunctor.obj x)) :=
            C.mapUniversalVertex_liftWalk hstable₁ hstable₂
              hbijective₁ hbijective₂ x p
          have hqRecover :
              C.mapUniversalVertex x
                    ⟨Lq.1, Quotient.mk _ Lq.2⟩ =
                (⟨z, Quotient.mk _ q⟩ : Vertex T₂
                  (C.toPrefunctor.obj x)) :=
            C.mapUniversalVertex_liftWalk hstable₁ hstable₂
              hbijective₁ hbijective₂ x q
          exact hpRecover.symm.trans
            ((congrArg (C.mapUniversalVertex x) hsource).trans hqRecover)

/-- Under source connectedness and source simple connectedness, the object
map of the universal-cover comparison is bijective. -/
theorem liftVertexPrefunctor_obj_bijective (x : Q₁)
    (hconnected : IsWalkConnectedAt T₁ x)
    (hsimple : ∀ {z : Q₁} (p q : Walk T₁ x z),
      Homotopic T₁ x p q) :
    Function.Bijective
      (C.liftVertexPrefunctor hstable₁ hstable₂
        hbijective₁ hbijective₂ x).obj :=
  ⟨C.liftVertex_injective hstable₁ hstable₂
      hbijective₁ hbijective₂ x hsimple,
    C.liftVertexPrefunctor_obj_surjective hstable₁ hstable₂
      hbijective₁ hbijective₂ x hconnected⟩

end MagnitudeConjecture.MeshCategory.RightMeshData.Cover
