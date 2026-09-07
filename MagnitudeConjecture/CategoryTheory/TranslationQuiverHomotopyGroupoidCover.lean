import MagnitudeConjecture.CategoryTheory.MeshCovering
import MagnitudeConjecture.CategoryTheory.TranslationQuiverHomotopyGroupoidPresentation
import MagnitudeConjecture.CategoryTheory.TranslationQuiverStable
import MagnitudeConjecture.CategoryTheory.TranslationQuiverUniversalGrading

/-!
# Mesh covers on mesh-homotopy groupoids

A covering of polarized right translation quivers preserves the augmented
walk presentation and therefore induces a functor on mesh-homotopy groupoids.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.Cover

universe v₁ v₂ w₁ w₂

open MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

variable {Q₁ : Type v₁} [Quiver.{w₁} Q₁]
variable {Q₂ : Type v₂} [Quiver.{w₂} Q₂]
variable {T₁ : RightMeshData Q₁} {T₂ : RightMeshData Q₂}

/-- The outgoing augmented star consists of the ordinary outgoing star and,
at a nonprojective vertex, the single formal mesh edge. -/
def augmentedStarEquiv (T : RightMeshData Q₁) (x : Q₁) :
    Quiver.Star (show AugmentedVertex T from x) ≃
      Quiver.Star x ⊕ PLift (x ∉ T.projective) where
  toFun A := by
    rcases A with ⟨y, a⟩
    cases a with
    | old a => exact Sum.inl ⟨y, a⟩
    | mesh s => exact Sum.inr ⟨s.2⟩
  invFun A := by
    rcases A with A | hx
    · exact ⟨A.1, AugmentedArrow.old A.2⟩
    · exact ⟨T.tau ⟨x, hx.down⟩, AugmentedArrow.mesh ⟨x, hx.down⟩⟩
  left_inv A := by
    rcases A with ⟨y, a⟩
    cases a <;> rfl
  right_inv A := by
    rcases A with A | hx
    · rfl
    · rfl

/-- Preservation and reflection of the projective boundary identifies the
possible formal mesh edge in corresponding augmented stars. -/
def nonprojectiveProofEquiv (C : Cover T₁ T₂) (x : Q₁) :
    PLift (x ∉ T₁.projective) ≃
      PLift (C.toPrefunctor.obj x ∉ T₂.projective) where
  toFun hx := ⟨fun h ↦ hx.down ((C.map_projective_iff x).2 h)⟩
  invFun hx := ⟨fun h ↦ hx.down ((C.map_projective_iff x).1 h)⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The augmented-quiver map underlying a polarized mesh cover.  The formal
mesh edge is transported along translation compatibility so that its endpoint
is literally the image of the source translate. -/
def augmentedPrefunctor (C : Cover T₁ T₂) :
    AugmentedVertex T₁ ⥤q AugmentedVertex T₂ where
  obj x := show AugmentedVertex T₂ from C.toPrefunctor.obj x
  map {x y} e := by
    cases e with
    | old a =>
        exact AugmentedArrow.old (C.toPrefunctor.map a)
    | mesh s =>
        exact Quiver.Hom.cast rfl
          (congrArg
            (fun z : Q₂ ↦ show AugmentedVertex T₂ from z)
            (C.map_tau s).symm)
          (AugmentedArrow.mesh (C.mapNonprojective s))

set_option backward.isDefEq.respectTransparency false in
/-- Under the outgoing-star decomposition, the augmented map is the sum of
the ordinary star map and projective-boundary transport. -/
theorem augmentedStarEquiv_naturality (C : Cover T₁ T₂) (x : Q₁) :
    C.augmentedPrefunctor.star x =
      (augmentedStarEquiv T₂ (C.toPrefunctor.obj x)).symm ∘
        Sum.map (C.toPrefunctor.star x) (C.nonprojectiveProofEquiv x) ∘
          augmentedStarEquiv T₁ x := by
  funext A
  rcases A with ⟨y, a⟩
  cases a with
  | old a => rfl
  | mesh s =>
      apply Sigma.ext
      · exact C.map_tau s
      · exact Quiver.Hom.cast_heq rfl _ _

/-- A polarized mesh cover is a covering on outgoing augmented stars. -/
theorem augmentedPrefunctor_star_bijective (C : Cover T₁ T₂)
    (x : Q₁) :
    Function.Bijective (C.augmentedPrefunctor.star x) := by
  rw [C.augmentedStarEquiv_naturality x]
  exact (augmentedStarEquiv T₂ _).symm.bijective.comp
    (((C.isCovering.star_bijective x).sumMap
      (C.nonprojectiveProofEquiv x).bijective).comp
        (augmentedStarEquiv T₁ x).bijective)

/-- A formal mesh edge ending at `x` is specified by a nonprojective
predecessor whose translate is `x`. -/
def MeshPredecessor (T : RightMeshData Q₁) (x : Q₁) :=
  {s : {s : Q₁ // s ∉ T.projective} // T.tau s = x}

/-- The incoming augmented costar consists of the ordinary incoming costar
and the formal mesh predecessors under translation. -/
def augmentedCostarEquiv (T : RightMeshData Q₁) (x : Q₁) :
    Quiver.Costar (show AugmentedVertex T from x) ≃
      Quiver.Costar x ⊕ MeshPredecessor T x where
  toFun A := by
    rcases A with ⟨y, a⟩
    cases a with
    | old a => exact Sum.inl ⟨y, a⟩
    | mesh s => exact Sum.inr ⟨s, rfl⟩
  invFun A := by
    rcases A with A | s
    · exact ⟨A.1, AugmentedArrow.old A.2⟩
    · exact ⟨s.1.1, Quiver.Hom.cast rfl s.2
        (AugmentedArrow.mesh s.1)⟩
  left_inv A := by
    rcases A with ⟨y, a⟩
    cases a <;> rfl
  right_inv A := by
    rcases A with A | s
    · rfl
    · rcases s with ⟨s, hs⟩
      subst x
      rfl

/-- A mesh cover sends a translation predecessor to the corresponding
translation predecessor of the image vertex. -/
def meshPredecessorMap (C : Cover T₁ T₂) (x : Q₁) :
    MeshPredecessor T₁ x →
      MeshPredecessor T₂ (C.toPrefunctor.obj x) :=
  fun s ↦ ⟨C.mapNonprojective s.1,
    (C.map_tau s.1).symm.trans
      (congrArg C.toPrefunctor.obj s.2)⟩

/-- In the stable bijective-translation case, a mesh cover bijects the formal
mesh predecessors of corresponding vertices. -/
theorem meshPredecessorMap_bijective (C : Cover T₁ T₂)
    (hstable₁ : T₁.projective = ∅) (hstable₂ : T₂.projective = ∅)
    (hbijective₁ : Function.Bijective (T₁.stableTau hstable₁))
    (hbijective₂ : Function.Bijective (T₂.stableTau hstable₂))
    (x : Q₁) :
    Function.Bijective (C.meshPredecessorMap x) := by
  constructor
  · intro s t _
    apply Subtype.ext
    apply Subtype.ext
    apply hbijective₁.1
    change T₁.tau s.1 = T₁.tau t.1
    exact s.2.trans t.2.symm
  · intro t
    obtain ⟨y, hy⟩ := hbijective₁.2 x
    let s₀ := T₁.stableNonprojective hstable₁ y
    let s : MeshPredecessor T₁ x := ⟨s₀, hy⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply hbijective₂.1
    change T₂.tau (C.mapNonprojective s.1) = T₂.tau t.1
    exact (C.map_tau s.1).symm.trans
      ((congrArg C.toPrefunctor.obj s.2).trans t.2.symm)

/-- Translation bijectivity upgrades the predecessor map to an equivalence. -/
def meshPredecessorEquiv (C : Cover T₁ T₂)
    (hstable₁ : T₁.projective = ∅) (hstable₂ : T₂.projective = ∅)
    (hbijective₁ : Function.Bijective (T₁.stableTau hstable₁))
    (hbijective₂ : Function.Bijective (T₂.stableTau hstable₂))
    (x : Q₁) :
    MeshPredecessor T₁ x ≃
      MeshPredecessor T₂ (C.toPrefunctor.obj x) :=
  Equiv.ofBijective (C.meshPredecessorMap x)
    (C.meshPredecessorMap_bijective hstable₁ hstable₂
      hbijective₁ hbijective₂ x)

set_option backward.isDefEq.respectTransparency false in
/-- Under the incoming-costar decomposition, the augmented map is the sum of
the ordinary costar map and translation-predecessor transport. -/
theorem augmentedCostarEquiv_naturality (C : Cover T₁ T₂) (x : Q₁) :
    C.augmentedPrefunctor.costar x =
      (augmentedCostarEquiv T₂ (C.toPrefunctor.obj x)).symm ∘
        Sum.map (C.toPrefunctor.costar x) (C.meshPredecessorMap x) ∘
          augmentedCostarEquiv T₁ x := by
  funext A
  rcases A with ⟨y, a⟩
  cases a with
  | old a => rfl
  | mesh s => rfl

/-- For stable meshes with bijective translation, a polarized mesh cover is a
covering on incoming augmented costars. -/
theorem augmentedPrefunctor_costar_bijective (C : Cover T₁ T₂)
    (hstable₁ : T₁.projective = ∅) (hstable₂ : T₂.projective = ∅)
    (hbijective₁ : Function.Bijective (T₁.stableTau hstable₁))
    (hbijective₂ : Function.Bijective (T₂.stableTau hstable₂))
    (x : Q₁) :
    Function.Bijective (C.augmentedPrefunctor.costar x) := by
  rw [C.augmentedCostarEquiv_naturality x]
  exact (augmentedCostarEquiv T₂ _).symm.bijective.comp
    (((C.isCovering.costar_bijective x).sumMap
      (C.meshPredecessorMap_bijective hstable₁ hstable₂
        hbijective₁ hbijective₂ x)).comp
          (augmentedCostarEquiv T₁ x).bijective)

/-- A polarized cover of stable translation quivers with bijective
translation is a covering of the augmented walk quivers. -/
theorem augmentedPrefunctor_isCovering (C : Cover T₁ T₂)
    (hstable₁ : T₁.projective = ∅) (hstable₂ : T₂.projective = ∅)
    (hbijective₁ : Function.Bijective (T₁.stableTau hstable₁))
    (hbijective₂ : Function.Bijective (T₂.stableTau hstable₂)) :
    C.augmentedPrefunctor.IsCovering where
  star_bijective := C.augmentedPrefunctor_star_bijective
  costar_bijective := C.augmentedPrefunctor_costar_bijective
    hstable₁ hstable₂ hbijective₁ hbijective₂

/-- After symmetrification, positive and negative augmented walks lift
uniquely along a stable polarized mesh cover. -/
theorem symmetrifiedAugmentedPrefunctor_isCovering
    (C : Cover T₁ T₂)
    (hstable₁ : T₁.projective = ∅) (hstable₂ : T₂.projective = ∅)
    (hbijective₁ : Function.Bijective (T₁.stableTau hstable₁))
    (hbijective₂ : Function.Bijective (T₂.stableTau hstable₂)) :
    C.augmentedPrefunctor.symmetrify.IsCovering :=
  (C.augmentedPrefunctor_isCovering hstable₁ hstable₂
    hbijective₁ hbijective₂).symmetrify

/-- Unique lifting of arbitrary augmented walks with a fixed initial
vertex. -/
theorem symmetrifiedAugmentedPrefunctor_pathStar_bijective
    (C : Cover T₁ T₂)
    (hstable₁ : T₁.projective = ∅) (hstable₂ : T₂.projective = ∅)
    (hbijective₁ : Function.Bijective (T₁.stableTau hstable₁))
    (hbijective₂ : Function.Bijective (T₂.stableTau hstable₂))
    (x : Q₁) :
    Function.Bijective
      (C.augmentedPrefunctor.symmetrify.pathStar x) :=
  (C.symmetrifiedAugmentedPrefunctor_isCovering hstable₁ hstable₂
    hbijective₁ hbijective₂).pathStar_bijective x

/-- The equivalence form of unique augmented-walk lifting from a fixed source
vertex. -/
def symmetrifiedAugmentedPathStarEquiv
    (C : Cover T₁ T₂)
    (hstable₁ : T₁.projective = ∅) (hstable₂ : T₂.projective = ∅)
    (hbijective₁ : Function.Bijective (T₁.stableTau hstable₁))
    (hbijective₂ : Function.Bijective (T₂.stableTau hstable₂))
    (x : Q₁) :
    Quiver.PathStar
        (show Quiver.Symmetrify (AugmentedVertex T₁) from x) ≃
      Quiver.PathStar
        (show Quiver.Symmetrify (AugmentedVertex T₂) from
          C.toPrefunctor.obj x) :=
  Equiv.ofBijective
    (C.augmentedPrefunctor.symmetrify.pathStar x)
    (C.symmetrifiedAugmentedPrefunctor_pathStar_bijective
      hstable₁ hstable₂ hbijective₁ hbijective₂ x)

private theorem arrowDegree_positive_cast (T : RightMeshData Q₁)
    {x y x' y' : AugmentedVertex T} (a : x ⟶ y)
    (hx : x = x') (hy : y = y') :
    arrowDegree T (Sum.inl (Quiver.Hom.cast hx hy a)) =
      arrowDegree T (Sum.inl a) := by
  subst x'
  subst y'
  rfl

private theorem arrowDegree_negative_cast (T : RightMeshData Q₁)
    {x y x' y' : AugmentedVertex T} (a : x ⟶ y)
    (hx : x = x') (hy : y = y') :
    arrowDegree T (Sum.inr (Quiver.Hom.cast hx hy a)) =
      arrowDegree T (Sum.inr a) := by
  subst x'
  subst y'
  rfl

/-- Mapping a symmetric augmented arrow along a mesh cover preserves its
signed degree. -/
theorem arrowDegree_symmetrifiedAugmentedPrefunctor_map
    (C : Cover T₁ T₂) {x y : Q₁}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T₁))
      (Quiver.symmetrifyQuiver (AugmentedVertex T₁)) x y) :
    arrowDegree T₂ (C.augmentedPrefunctor.symmetrify.map e) =
      arrowDegree T₁ e := by
  rcases e with e | e
  · cases e with
    | old a => rfl
    | mesh s =>
        exact arrowDegree_positive_cast T₂
          (AugmentedArrow.mesh (C.mapNonprojective s)) rfl
          (congrArg
            (fun z : Q₂ ↦ show AugmentedVertex T₂ from z)
            (C.map_tau s).symm)
  · cases e with
    | old a => rfl
    | mesh s =>
        exact arrowDegree_negative_cast T₂
          (AugmentedArrow.mesh (C.mapNonprojective s)) rfl
          (congrArg
            (fun z : Q₂ ↦ show AugmentedVertex T₂ from z)
            (C.map_tau s).symm)

/-- Mapping an augmented walk along a mesh cover preserves its signed
degree. -/
theorem walkDegree_symmetrifiedAugmentedPrefunctor_mapPath
    (C : Cover T₁ T₂) {x y : Q₁}
    (p : Walk T₁ x y) :
    walkDegree T₂ (C.augmentedPrefunctor.symmetrify.mapPath p) =
      walkDegree T₁ p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change walkDegree T₂
            (C.augmentedPrefunctor.symmetrify.mapPath p) +
          arrowDegree T₂
            (C.augmentedPrefunctor.symmetrify.map e) =
        walkDegree T₁ p + arrowDegree T₁ e
      rw [ih, C.arrowDegree_symmetrifiedAugmentedPrefunctor_map e]

set_option backward.isDefEq.respectTransparency false in
/-- A polarized mesh cover maps the augmented source quiver into the target
mesh-homotopy groupoid.  A formal mesh edge uses translation compatibility to
transport its target back to the image of the source translate. -/
def homotopyLabelling (C : Cover T₁ T₂) :
    AugmentedVertex T₁ ⥤q HomotopyGroupoid T₂ where
  obj x := show HomotopyGroupoid T₂ from C.toPrefunctor.obj x
  map {x y} e := by
    cases e with
    | old a =>
        exact (HomotopyGroupoid.of T₂).map
          (AugmentedArrow.old (C.toPrefunctor.map a))
    | mesh s =>
        exact (HomotopyGroupoid.of T₂).map
            (AugmentedArrow.mesh (C.mapNonprojective s)) ≫
          eqToHom (congrArg
            (fun z : Q₂ ↦ show HomotopyGroupoid T₂ from z)
            (C.map_tau s).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The homotopy labelling is the augmented cover followed by the canonical
inclusion into the target mesh-homotopy groupoid. -/
theorem augmentedPrefunctor_comp_of (C : Cover T₁ T₂) :
    C.augmentedPrefunctor ⋙q HomotopyGroupoid.of T₂ =
      C.homotopyLabelling := by
  fapply Prefunctor.ext
  · intro x
    rfl
  · intro x y e
    cases e with
    | old a => rfl
    | mesh s =>
        change
          (HomotopyGroupoid.of T₂).map
              (Quiver.Hom.cast rfl
                (congrArg
                  (fun z : Q₂ ↦ show AugmentedVertex T₂ from z)
                  (C.map_tau s).symm)
                (AugmentedArrow.mesh (C.mapNonprojective s))) =
            (HomotopyGroupoid.of T₂).map
                (AugmentedArrow.mesh (C.mapNonprojective s)) ≫
              eqToHom (congrArg
                (fun z : Q₂ ↦ show HomotopyGroupoid T₂ from z)
                (C.map_tau s).symm)
        exact HomotopyGroupoid.of_cast_target T₂
          (AugmentedArrow.mesh (C.mapNonprojective s)) _

set_option backward.isDefEq.respectTransparency false in
/-- The augmented-quiver labelling induced by a polarized mesh cover respects
the source mesh relations. -/
theorem homotopyLabelling_meshCompatible (C : Cover T₁ T₂) :
    HomotopyGroupoid.MeshCompatible T₁ C.homotopyLabelling := by
  intro s a
  change
    (HomotopyGroupoid.of T₂).map
          (AugmentedArrow.mesh (C.mapNonprojective s)) ≫
        eqToHom (congrArg
          (fun z : Q₂ ↦ show HomotopyGroupoid T₂ from z)
          (C.map_tau s).symm) =
      (HomotopyGroupoid.of T₂).map
          (AugmentedArrow.old (C.toPrefunctor.map a.2)) ≫
        (HomotopyGroupoid.of T₂).map
          (AugmentedArrow.old
            (C.toPrefunctor.map ((T₁.arrowEquiv s a.1) a.2)))
  rw [HomotopyGroupoid.of_mesh_eq_old_comp_old T₂
    (C.mapNonprojective s) (C.meshArrowMap s a)]
  change
    ((HomotopyGroupoid.of T₂).map
          (AugmentedArrow.old (C.toPrefunctor.map a.2)) ≫
        (HomotopyGroupoid.of T₂).map
          (AugmentedArrow.old
            ((T₂.arrowEquiv (C.mapNonprojective s)
              (C.toPrefunctor.obj a.1))
              (C.toPrefunctor.map a.2)))) ≫
        eqToHom (congrArg
          (fun z : Q₂ ↦ show HomotopyGroupoid T₂ from z)
          (C.map_tau s).symm) = _
  rw [← C.map_arrowEquiv s a.1 a.2]
  rw [HomotopyGroupoid.of_old_cast_target]
  simp only [Category.assoc, eqToHom_trans]
  simp

/-- A polarized mesh cover induces a functor between the corresponding
mesh-homotopy groupoids. -/
def homotopyFunctor (C : Cover T₁ T₂) :
    HomotopyGroupoid T₁ ⥤ HomotopyGroupoid T₂ :=
  HomotopyGroupoid.lift T₁ C.homotopyLabelling
    C.homotopyLabelling_meshCompatible

@[simp]
theorem homotopyFunctor_obj (C : Cover T₁ T₂) (x : Q₁) :
    C.homotopyFunctor.obj x = C.toPrefunctor.obj x :=
  rfl

@[simp]
theorem homotopyFunctor_map_old (C : Cover T₁ T₂)
    {x y : Q₁} (a : x ⟶ y) :
    C.homotopyFunctor.map
        ((HomotopyGroupoid.of T₁).map (AugmentedArrow.old a)) =
      (HomotopyGroupoid.of T₂).map
        (AugmentedArrow.old (C.toPrefunctor.map a)) := by
  exact HomotopyGroupoid.lift_map_of T₁ C.homotopyLabelling
    C.homotopyLabelling_meshCompatible (AugmentedArrow.old a)

@[simp]
theorem homotopyFunctor_map_mesh (C : Cover T₁ T₂)
    (s : {s : Q₁ // s ∉ T₁.projective}) :
    C.homotopyFunctor.map
        ((HomotopyGroupoid.of T₁).map (AugmentedArrow.mesh s)) =
      (HomotopyGroupoid.of T₂).map
          (AugmentedArrow.mesh (C.mapNonprojective s)) ≫
        eqToHom (congrArg
          (fun z : Q₂ ↦ show HomotopyGroupoid T₂ from z)
          (C.map_tau s).symm) := by
  exact HomotopyGroupoid.lift_map_of T₁ C.homotopyLabelling
    C.homotopyLabelling_meshCompatible (AugmentedArrow.mesh s)

/-- On a represented mesh-homotopy class, the functor induced by a mesh
cover is represented by the pointwise image of the augmented walk. -/
theorem homotopyFunctor_map_mk (C : Cover T₁ T₂)
    {x y : Q₁} (p : Walk T₁ x y) :
    C.homotopyFunctor.map (Quotient.mk _ p) =
      Quotient.mk _ (C.augmentedPrefunctor.symmetrify.mapPath p) := by
  change HomotopyGroupoid.evalWalk T₁ C.homotopyLabelling p = _
  induction p with
  | nil => rfl
  | cons p e ih =>
      change
        HomotopyGroupoid.evalWalk T₁ C.homotopyLabelling p ≫
            (Quiver.Symmetrify.lift
              C.homotopyLabelling).map e = _
      rw [ih]
      cases e with
      | inl a =>
          cases a with
          | old a => rfl
          | mesh s =>
              let ht := congrArg
                (fun z : Q₂ ↦ show HomotopyGroupoid T₂ from z)
                (C.map_tau s).symm
              change
                Quotient.mk _
                      (C.augmentedPrefunctor.symmetrify.mapPath p) ≫
                    ((HomotopyGroupoid.of T₂).map
                        (AugmentedArrow.mesh (C.mapNonprojective s)) ≫
                      eqToHom ht) =
                  Quotient.mk _
                      (C.augmentedPrefunctor.symmetrify.mapPath p) ≫
                    (HomotopyGroupoid.of T₂).map
                      (Quiver.Hom.cast rfl ht
                        (AugmentedArrow.mesh (C.mapNonprojective s)))
              exact congrArg
                (fun f ↦ Quotient.mk _
                    (C.augmentedPrefunctor.symmetrify.mapPath p) ≫ f)
                (HomotopyGroupoid.of_cast_target T₂
                  (AugmentedArrow.mesh (C.mapNonprojective s)) ht).symm
      | inr a =>
          cases a with
          | old a => rfl
          | mesh s =>
              let ht := congrArg
                (fun z : Q₂ ↦ show HomotopyGroupoid T₂ from z)
                (C.map_tau s).symm
              change
                Quotient.mk _
                      (C.augmentedPrefunctor.symmetrify.mapPath p) ≫
                    Groupoid.inv
                      ((HomotopyGroupoid.of T₂).map
                          (AugmentedArrow.mesh (C.mapNonprojective s)) ≫
                        eqToHom ht) =
                  Quotient.mk _
                      (C.augmentedPrefunctor.symmetrify.mapPath p) ≫
                    Groupoid.inv
                      ((HomotopyGroupoid.of T₂).map
                        (Quiver.Hom.cast rfl ht
                          (AugmentedArrow.mesh (C.mapNonprojective s))))
              exact congrArg
                (fun f ↦ Quotient.mk _
                    (C.augmentedPrefunctor.symmetrify.mapPath p) ≫
                      Groupoid.inv f)
                (HomotopyGroupoid.of_cast_target T₂
                  (AugmentedArrow.mesh (C.mapNonprojective s)) ht).symm

end MagnitudeConjecture.MeshCategory.RightMeshData.Cover
