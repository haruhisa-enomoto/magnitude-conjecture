import MagnitudeConjecture.Algebra.StringDetectorLift
import MagnitudeConjecture.Algebra.StringEmbeddingFunctor
import MagnitudeConjecture.Algebra.StringEndpointDeterminism
import MagnitudeConjecture.Algebra.StringExtension

/-!
# Coherent trajectories along a string word

A trajectory assigns an ambient-module vector to every position of a string
word.  Membership records a source-subspace condition and compatibility along
every displayed word edge.  Thus all position maps obtained from one linear
section of the trajectory space are coherent by construction, rather than by
comparison of separately chosen path lifts.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

namespace Word

/-- The two arrows entering an internal peak from its adjacent word
positions are distinct. -/
theorem incomingAdjacentArrows_ne
    (C : Word R) {w x z : Q} (a : w ⟶ x) (b : z ⟶ x)
    (previous : C.PositionAt w) (i : C.PositionAt x)
    (next : C.PositionAt z)
    (hpreviousIndex : previous.index + 1 = i.index)
    (hnextIndex : next.index = i.index + 1)
    (ha : C.ArrowStep a previous i)
    (hb : C.ArrowStep b next i) :
    (⟨w, a⟩ : Quiver.Costar x) ≠ ⟨z, b⟩ := by
  intro hab
  cases hab
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · have hbackward : next.index + 1 = i.index := by
        change next.1.length + 1 = i.1.length
        rw [hb, Quiver.Path.length_comp, Quiver.Path.length_toPath]
      omega
    · rcases next.2 with ⟨tail, htail⟩
      apply C.isString.1 (positiveArrow a)
      refine ⟨previous.1, tail, ?_⟩
      calc
        C.path = next.1.comp tail := htail
        _ = (i.1.comp (negativeArrow a).toPath).comp tail := by rw [hb]
        _ = ((previous.1.comp (positiveArrow a).toPath).comp
            (negativeArrow a).toPath).comp tail := by rw [ha]
        _ = previous.1.comp
            (((positiveArrow a).toPath.comp
              (negativeArrow a).toPath).comp tail) := by
          simp only [Quiver.Path.comp_assoc]
  · have hbackward : i.index + 1 = previous.index := by
      change i.1.length + 1 = previous.1.length
      rw [ha, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega

/-- The two arrows leaving an internal valley toward its adjacent word
positions are distinct. -/
theorem outgoingAdjacentArrows_ne
    (C : Word R) {w x z : Q} (a : x ⟶ w) (b : x ⟶ z)
    (previous : C.PositionAt w) (i : C.PositionAt x)
    (next : C.PositionAt z)
    (hpreviousIndex : previous.index + 1 = i.index)
    (hnextIndex : next.index = i.index + 1)
    (ha : C.ArrowStep a i previous)
    (hb : C.ArrowStep b i next) :
    (⟨w, a⟩ : Quiver.Star x) ≠ ⟨z, b⟩ := by
  intro hab
  cases hab
  rcases ha with ha | ha
  · have hforward : previous.index = i.index + 1 := by
      change previous.1.length = i.1.length + 1
      rw [ha, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega
  · rcases hb with hb | hb
    · rcases next.2 with ⟨tail, htail⟩
      apply C.isString.1 (negativeArrow a)
      refine ⟨previous.1, tail, ?_⟩
      calc
        C.path = next.1.comp tail := htail
        _ = (i.1.comp (positiveArrow a).toPath).comp tail := by rw [hb]
        _ = ((previous.1.comp (negativeArrow a).toPath).comp
            (positiveArrow a).toPath).comp tail := by rw [ha]
        _ = previous.1.comp
            (((negativeArrow a).toPath.comp
              (positiveArrow a).toPath).comp tail) := by
          simp only [Quiver.Path.comp_assoc]
    · have hbackward : i.index = next.index + 1 := by
        change i.1.length = next.1.length + 1
        rw [hb, Quiver.Path.length_comp, Quiver.Path.length_toPath]
      omega

/-- A reversed positive path occurring literally between two word prefixes
gives reachability by that ordinary path in the displayed arrow direction. -/
theorem pathReach_of_prefix_eq_positivePath_reverse
    (C : Word R) :
    ∀ {x y : Q} (p : Quiver.Path x y)
      (i : C.PositionAt x) (j : C.PositionAt y),
      i.1 = j.1.comp (positivePath p).reverse →
        C.PathReach p i j := by
  intro x y p
  induction p with
  | nil =>
      intro i j hij
      change i.1 = j.1 at hij
      exact Subtype.ext hij
  | @cons z y p a ih =>
      intro i j hij
      rcases i.2 with ⟨tail, htail⟩
      let middle : C.PositionAt z :=
        ⟨j.1.comp (negativeArrow a).toPath,
          ⟨(positivePath p).reverse.comp tail, by
            calc
              C.path = i.1.comp tail := htail
              _ = (j.1.comp (positivePath (p.cons a)).reverse).comp
                  tail := by rw [hij]
              _ = (j.1.comp (negativeArrow a).toPath).comp
                  ((positivePath p).reverse.comp tail) := by
                simp only [positivePath_cons, positivePath_toPath,
                  Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
                  reverse_positiveArrow, Quiver.Path.comp_assoc]⟩⟩
      refine ⟨middle, ?_, Or.inr rfl⟩
      apply ih i middle
      calc
        i.1 = j.1.comp (positivePath (p.cons a)).reverse := hij
        _ = middle.1.comp (positivePath p).reverse := by
          simp only [middle, positivePath_cons, positivePath_toPath,
            Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
            reverse_positiveArrow, Quiver.Path.comp_assoc]

/-- A vector in the ambient module at every total position of a word. -/
abbrev PositionFamily
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k) (C : Word R) :=
  (i : C.Position) →
    N.obj (Opposite.op (obj R i.1))

/-- The source endpoint regarded as a total word position. -/
abbrev totalSourcePosition (C : Word R) : C.Position :=
  ⟨C.source, C.sourcePosition⟩

/-- The target endpoint regarded as a total word position. -/
abbrev totalTargetPosition (C : Word R) : C.Position :=
  ⟨C.target, C.targetPosition⟩

@[simp]
theorem totalSourcePosition_index (C : Word R) :
    C.totalSourcePosition.index = 0 :=
  rfl

@[simp]
theorem totalTargetPosition_index (C : Word R) :
    C.totalTargetPosition.index = C.length :=
  rfl

/-- Trajectories which start in `U` and satisfy the ambient-module arrow
equation along every edge displayed by the word. -/
def trajectorySubmodule
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source)))) :
    Submodule k (PositionFamily N C) where
  carrier := {v |
    v C.totalSourcePosition ∈ U ∧
      ∀ {x y : Q} (a : x ⟶ y)
        (i : C.PositionAt x) (j : C.PositionAt y),
        C.ArrowStep a i j →
          moduleArrowMap N a (v ⟨x, i⟩) = v ⟨y, j⟩}
  zero_mem' := by
    constructor
    · exact U.zero_mem
    · intro x y a i j _
      exact map_zero (moduleArrowMap N a).hom
  add_mem' hv hw := by
    constructor
    · exact U.add_mem hv.1 hw.1
    · intro x y a i j hij
      rw [Pi.add_apply, map_add, hv.2 a i j hij, hw.2 a i j hij,
        Pi.add_apply]
  smul_mem' c v hv := by
    constructor
    · exact U.smul_mem c hv.1
    · intro x y a i j hij
      rw [Pi.smul_apply, map_smul, hv.2 a i j hij, Pi.smul_apply]

@[simp]
theorem mem_trajectorySubmodule
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (v : PositionFamily N C) :
    v ∈ C.trajectorySubmodule N U ↔
      v C.totalSourcePosition ∈ U ∧
        ∀ {x y : Q} (a : x ⟶ y)
          (i : C.PositionAt x) (j : C.PositionAt y),
          C.ArrowStep a i j →
            moduleArrowMap N a (v ⟨x, i⟩) = v ⟨y, j⟩ :=
  Iff.rfl

/-- Evaluation of a coherent trajectory at a total word position. -/
def trajectoryPositionMap
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (i : C.Position) :
    C.trajectorySubmodule N U →ₗ[k]
      N.obj (Opposite.op (obj R i.1)) :=
  (LinearMap.proj i).comp (C.trajectorySubmodule N U).subtype

/-- Evaluation at a position over a specified displayed vertex. -/
def trajectoryPositionAtMap
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    {x : Q} (i : C.PositionAt x) :
    C.trajectorySubmodule N U →ₗ[k]
      N.obj (Opposite.op (obj R x)) :=
  C.trajectoryPositionMap N U ⟨x, i⟩

@[simp]
theorem trajectoryPositionAtMap_apply
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    {x : Q} (i : C.PositionAt x)
    (v : C.trajectorySubmodule N U) :
    C.trajectoryPositionAtMap N U i v = v.1 ⟨x, i⟩ :=
  rfl

/-- Position evaluation respects every displayed arrow step by definition of
the trajectory submodule. -/
theorem moduleArrowMap_trajectoryPositionAtMap_of_arrowStep
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j)
    (v : C.trajectorySubmodule N U) :
    moduleArrowMap N a (C.trajectoryPositionAtMap N U i v) =
      C.trajectoryPositionAtMap N U j v :=
  (C.mem_trajectorySubmodule N U v.1).1 v.property |>.2 a i j hij

/-- Position evaluation respects every ordinary path realized monotonically
along the word. -/
theorem modulePathMap_trajectoryPositionAtMap_of_pathReach
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    {x y : Q} (p : Quiver.Path x y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.PathReach p i j)
    (v : C.trajectorySubmodule N U) :
    modulePathMap N p (C.trajectoryPositionAtMap N U i v) =
      C.trajectoryPositionAtMap N U j v := by
  induction p with
  | nil =>
      subst j
      rw [modulePathMap_nil, ModuleCat.id_apply]
  | @cons z y p a ih =>
      rcases hij with ⟨middle, himiddle, hmiddlej⟩
      rw [modulePathMap_cons, ModuleCat.comp_apply,
        ih middle himiddle]
      exact C.moduleArrowMap_trajectoryPositionAtMap_of_arrowStep
        N U a middle j hmiddlej v

/-- The value of a coherent trajectory at each prefix belongs to the
subspace obtained by transporting `U` along that prefix. -/
theorem trajectory_value_mem_signedPathSubspace
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (v : C.trajectorySubmodule N U)
    (i : C.Position) :
    v.1 i ∈ signedPathSubspace N i.2.1 U := by
  refine Nat.strong_induction_on
    (p := fun n ↦ ∀ i : C.Position, i.index = n →
      v.1 i ∈ signedPathSubspace N i.2.1 U)
    i.index ?_ i rfl
  intro n ih current hcurrent
  by_cases hn : n = 0
  · have hsource : current = C.totalSourcePosition := by
      apply Position.ext_index
      simp only [hcurrent, hn, totalSourcePosition_index]
    rw [hsource]
    rw [show C.totalSourcePosition.2.1 =
        (Quiver.Path.nil : SignedPath C.source C.source) from rfl,
      signedPathSubspace_nil]
    exact ((C.mem_trajectorySubmodule N U v.1).1 v.property).1
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hmle : m ≤ C.length := by
      have hle := current.2.index_le
      change current.index ≤ C.length at hle
      rw [hcurrent] at hle
      omega
    obtain ⟨previous, hprevious⟩ := C.exists_position_index_eq m hmle
    have hindex : current.index = previous.index + 1 := by
      omega
    have hvprevious :
        v.1 previous ∈ signedPathSubspace N previous.2.1 U :=
      ih m (Nat.lt_succ_self m) previous hprevious
    rcases C.exists_arrowStep_of_position_index_succ
        previous current hindex with
      ⟨a, hstep⟩ | ⟨a, hstep⟩
    · rcases hstep with hpositive | hnegative
      · rw [hpositive, Quiver.Path.comp_toPath_eq_cons,
          signedPathSubspace_cons, signedArrowSubspace_positive]
        refine ⟨v.1 previous, hvprevious, ?_⟩
        exact ((C.mem_trajectorySubmodule N U v.1).1 v.property).2
          a previous.2 current.2 (Or.inl hpositive)
      · have hbad := congrArg Quiver.Path.length hnegative
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hbad
        have hbad' : previous.index = current.index + 1 := hbad
        rw [hprevious, hcurrent] at hbad'
        omega
    · rcases hstep with hpositive | hnegative
      · have hbad := congrArg Quiver.Path.length hpositive
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hbad
        have hbad' : previous.index = current.index + 1 := hbad
        rw [hprevious, hcurrent] at hbad'
        omega
      · rw [hnegative, Quiver.Path.comp_toPath_eq_cons,
          signedPathSubspace_cons, signedArrowSubspace_negative]
        change moduleArrowMap N a (v.1 current) ∈
          signedPathSubspace N previous.2.1 U
        have hcoherence :=
          ((C.mem_trajectorySubmodule N U v.1).1 v.property).2
            a current.2 previous.2 (Or.inr hnegative)
        change moduleArrowMap N a (v.1 current) = v.1 previous at hcoherence
        rw [hcoherence]
        exact hvprevious

/-- Terminal evaluation from the trajectory submodule. -/
def trajectoryTerminalMap
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source)))) :
    C.trajectorySubmodule N U →ₗ[k]
      N.obj (Opposite.op (obj R C.target)) :=
  C.trajectoryPositionAtMap N U C.targetPosition

/-- Every terminal value of a coherent trajectory lies in the full
transported subspace. -/
theorem trajectoryTerminalMap_range_le_signedPathSubspace
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source)))) :
    LinearMap.range (C.trajectoryTerminalMap N U) ≤
      signedPathSubspace N C.path U := by
  rintro z ⟨v, rfl⟩
  exact C.trajectory_value_mem_signedPathSubspace N U v
    C.totalTargetPosition

/-- Terminal evaluation with its codomain restricted to the full transported
subspace. -/
def trajectoryTransportMap
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source)))) :
    C.trajectorySubmodule N U →ₗ[k]
      signedPathSubspace N C.path U :=
  LinearMap.codRestrict (signedPathSubspace N C.path U)
    (C.trajectoryTerminalMap N U)
    (fun v ↦ C.trajectory_value_mem_signedPathSubspace N U v
      C.totalTargetPosition)

@[simp]
theorem trajectoryTransportMap_coe
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (v : C.trajectorySubmodule N U) :
    (C.trajectoryTransportMap N U v :
        N.obj (Opposite.op (obj R C.target))) =
      v.1 C.totalTargetPosition :=
  rfl

/-- Extend a position family across one appended letter by retaining all old
values and assigning a specified value to the unique new endpoint. -/
def extendPositionFamily
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R) {z : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (v : PositionFamily N C)
    (w : N.obj (Opposite.op (obj R z))) :
    PositionFamily N (append R C e h) := fun i ↦ by
  rcases i with ⟨x, i⟩
  classical
  by_cases hold : ∃ j : C.PositionAt x,
      appendPosition C e h j = i
  · exact v ⟨x, Classical.choose hold⟩
  · have hnotle : ¬ i.index ≤ C.length := by
      intro hle
      exact hold (exists_eq_appendPosition_of_index_le C e h i hle)
    have hfinal : i.index = (append R C e h).length := by
      have hiUpper : i.index ≤ C.length + 1 := by
        simpa only [append_length] using i.index_le
      rw [append_length]
      omega
    have hx : x = z := i.eq_target_of_index_eq_length hfinal
    subst x
    exact w

@[simp]
theorem extendPositionFamily_appendPosition
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R) {z x : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (v : PositionFamily N C)
    (w : N.obj (Opposite.op (obj R z)))
    (i : C.PositionAt x) :
    C.extendPositionFamily N e h v w
        ⟨x, appendPosition C e h i⟩ = v ⟨x, i⟩ := by
  classical
  simp only [extendPositionFamily]
  let hold : ∃ j : C.PositionAt x,
      appendPosition C e h j = appendPosition C e h i := ⟨i, rfl⟩
  rw [dif_pos hold]
  have hchosen : Classical.choose hold = i := by
    apply appendPosition_injective C e h
    exact Classical.choose_spec hold
  rw [hchosen]

@[simp]
theorem extendPositionFamily_appendEndPosition
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R) {z : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (v : PositionFamily N C)
    (w : N.obj (Opposite.op (obj R z))) :
    C.extendPositionFamily N e h v w
        ⟨z, appendEndPosition C e h⟩ = w := by
  classical
  simp only [extendPositionFamily]
  rw [dif_neg (not_exists_appendPosition_eq_appendEndPosition C e h)]

/-- A total position of an appended word which is not inherited from the old
word is its unique new target position. -/
theorem eq_totalTargetPosition_of_not_exists_old
    (C : Word R) {z : Q} (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (i : (append R C e h).Position)
    (hi : ¬ ∃ j : C.PositionAt i.1,
      appendPosition C e h j = i.2) :
    i = (append R C e h).totalTargetPosition := by
  apply Position.ext_index
  have hnotle : ¬ i.2.index ≤ C.length := by
    intro hle
    exact hi (exists_eq_appendPosition_of_index_le C e h i.2 hle)
  have hiUpper : i.2.index ≤ C.length + 1 := by
    simpa only [append_length] using i.2.index_le
  change i.2.index =
    (append R C e h).targetPosition.index
  rw [targetPosition_index, append_length]
  omega

/-- Extending a coherent trajectory across a positive letter preserves
coherence when the new endpoint value is the arrow image of the old terminal
value. -/
theorem extendPositionFamily_mem_trajectorySubmodule_positive
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (v : C.trajectorySubmodule N U)
    (w : N.obj (Opposite.op (obj R z)))
    (hw : moduleArrowMap N a
      (v.1 C.totalTargetPosition) = w) :
    C.extendPositionFamily N (positiveArrow a) h v.1 w ∈
      (append R C (positiveArrow a) h).trajectorySubmodule N U := by
  rw [mem_trajectorySubmodule]
  constructor
  · have hsource :
        (append R C (positiveArrow a) h).sourcePosition =
          appendPosition C (positiveArrow a) h C.sourcePosition := by
      apply Subtype.ext
      rfl
    change C.extendPositionFamily N (positiveArrow a) h v.1 w
        ⟨C.source,
          (append R C (positiveArrow a) h).sourcePosition⟩ ∈ U
    rw [hsource, extendPositionFamily_appendPosition]
    exact ((C.mem_trajectorySubmodule N U v.1).1 v.property).1
  · intro x y b i j hij
    classical
    by_cases hiold : ∃ i₀ : C.PositionAt x,
        appendPosition C (positiveArrow a) h i₀ = i
    · rcases hiold with ⟨i₀, rfl⟩
      by_cases hjold : ∃ j₀ : C.PositionAt y,
          appendPosition C (positiveArrow a) h j₀ = j
      · rcases hjold with ⟨j₀, rfl⟩
        rw [extendPositionFamily_appendPosition,
          extendPositionFamily_appendPosition]
        apply ((C.mem_trajectorySubmodule N U v.1).1 v.property).2
          b i₀ j₀
        exact hij
      · have hjEnd : (⟨y, j⟩ :
            (append R C (positiveArrow a) h).Position) =
            (append R C (positiveArrow a) h).totalTargetPosition :=
          eq_totalTargetPosition_of_not_exists_old C
            (positiveArrow a) h ⟨y, j⟩ hjold
        cases hjEnd
        have hend :
            (append R C (positiveArrow a) h).targetPosition =
              appendEndPosition C (positiveArrow a) h := by
          apply Subtype.ext
          rfl
        rw [extendPositionFamily_appendPosition, hend]
        change moduleArrowMap N b (v.1 ⟨x, i₀⟩) =
          C.extendPositionFamily N (positiveArrow a) h v.1 w
            ⟨z, appendEndPosition C (positiveArrow a) h⟩
        rw [
          extendPositionFamily_appendEndPosition]
        rcases hij with hpositive | hnegative
        · change C.path.comp (positiveArrow a).toPath =
              i₀.1.comp (positiveArrow b).toPath at hpositive
          have hlength := congrArg Quiver.Path.length hpositive
          change C.path.length + 1 = i₀.1.length + 1 at hlength
          have hiFinal : i₀.index = C.length := by
            change i₀.1.length = C.path.length
            omega
          have hiTarget :
              (⟨x, i₀⟩ : C.Position) = C.totalTargetPosition := by
            apply Position.ext_index
            rw [totalTargetPosition_index]
            exact hiFinal
          cases hiTarget
          have hsuffix := Quiver.Path.comp_injective_right C.path hpositive
          have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
          have hba : b = a := Sum.inl.inj (eq_of_heq harrows).symm
          subst b
          exact hw
        · change i₀.1 =
              (C.path.comp (positiveArrow a).toPath).comp
                (negativeArrow b).toPath at hnegative
          have hlength := congrArg Quiver.Path.length hnegative
          simp only [Quiver.Path.length_comp,
            Quiver.Path.length_toPath] at hlength
          have hiLe := i₀.index_le
          change i₀.1.length ≤ C.path.length at hiLe
          omega
    · have hiEnd : (⟨x, i⟩ :
          (append R C (positiveArrow a) h).Position) =
          (append R C (positiveArrow a) h).totalTargetPosition :=
        eq_totalTargetPosition_of_not_exists_old C
          (positiveArrow a) h ⟨x, i⟩ hiold
      cases hiEnd
      exact False.elim
        (not_exists_arrowStep_appendEndPosition_positive C a h b ⟨j, hij⟩)

/-- Extending a coherent trajectory across a negative letter preserves
coherence when the old terminal value is the arrow image of the new endpoint
value. -/
theorem extendPositionFamily_mem_trajectorySubmodule_negative
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (v : C.trajectorySubmodule N U)
    (w : N.obj (Opposite.op (obj R z)))
    (hw : moduleArrowMap N a w =
      v.1 C.totalTargetPosition) :
    C.extendPositionFamily N (negativeArrow a) h v.1 w ∈
      (append R C (negativeArrow a) h).trajectorySubmodule N U := by
  rw [mem_trajectorySubmodule]
  constructor
  · have hsource :
        (append R C (negativeArrow a) h).sourcePosition =
          appendPosition C (negativeArrow a) h C.sourcePosition := by
      apply Subtype.ext
      rfl
    change C.extendPositionFamily N (negativeArrow a) h v.1 w
        ⟨C.source,
          (append R C (negativeArrow a) h).sourcePosition⟩ ∈ U
    rw [hsource, extendPositionFamily_appendPosition]
    exact ((C.mem_trajectorySubmodule N U v.1).1 v.property).1
  · intro x y b i j hij
    classical
    by_cases hiold : ∃ i₀ : C.PositionAt x,
        appendPosition C (negativeArrow a) h i₀ = i
    · rcases hiold with ⟨i₀, rfl⟩
      rcases exists_old_of_arrowStep_appendPosition_negative
          C a h b i₀ j hij with ⟨j₀, rfl⟩
      rw [extendPositionFamily_appendPosition,
        extendPositionFamily_appendPosition]
      apply ((C.mem_trajectorySubmodule N U v.1).1 v.property).2
        b i₀ j₀
      exact hij
    · have hiEnd : (⟨x, i⟩ :
          (append R C (negativeArrow a) h).Position) =
          (append R C (negativeArrow a) h).totalTargetPosition :=
        eq_totalTargetPosition_of_not_exists_old C
          (negativeArrow a) h ⟨x, i⟩ hiold
      cases hiEnd
      have hend :
          (append R C (negativeArrow a) h).targetPosition =
            appendEndPosition C (negativeArrow a) h := by
        apply Subtype.ext
        rfl
      rw [hend]
      change moduleArrowMap N b
          (C.extendPositionFamily N (negativeArrow a) h v.1 w
            ⟨z, appendEndPosition C (negativeArrow a) h⟩) =
        C.extendPositionFamily N (negativeArrow a) h v.1 w ⟨y, j⟩
      rw [extendPositionFamily_appendEndPosition]
      rcases hij with hpositive | hnegative
      · change j.1 =
            (C.path.comp (negativeArrow a).toPath).comp
              (positiveArrow b).toPath at hpositive
        have hlength := congrArg Quiver.Path.length hpositive
        change j.1.length = (C.path.length + 1) + 1 at hlength
        have hjUpper := j.index_le
        change j.1.length ≤ C.path.length + 1 at hjUpper
        omega
      · change C.path.comp (negativeArrow a).toPath =
            j.1.comp (negativeArrow b).toPath at hnegative
        have hlength := congrArg Quiver.Path.length hnegative
        change C.path.length + 1 = j.1.length + 1 at hlength
        have hjIndex : j.index = C.length := by
          change j.1.length = C.path.length
          omega
        obtain ⟨j₀, hj₀⟩ := exists_eq_appendPosition_of_index_le
          C (negativeArrow a) h j (by omega)
        subst j
        rw [extendPositionFamily_appendPosition]
        have hjTarget :
            (⟨y, j₀⟩ : C.Position) = C.totalTargetPosition := by
          apply Position.ext_index
          rw [totalTargetPosition_index]
          change j₀.index = C.length
          simpa only [appendPosition_index] using hjIndex
        cases hjTarget
        have hsuffix := Quiver.Path.comp_injective_right C.path hnegative
        have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
        have hba : b = a := Sum.inr.inj (eq_of_heq harrows).symm
        subst b
        exact hw

/-- Surjectivity of coherent terminal evaluation is preserved by appending a
positive letter. -/
theorem trajectoryTransportMap_surjective_append_positive
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (hsurj : Function.Surjective (C.trajectoryTransportMap N U)) :
    Function.Surjective
      ((append R C (positiveArrow a) h).trajectoryTransportMap N U) := by
  rintro ⟨q, hq⟩
  change N.obj (Opposite.op (obj R z)) at q
  rw [append_path, Quiver.Path.comp_toPath_eq_cons] at hq
  unfold signedPathSubspace at hq
  unfold signedArrowSubspace at hq
  rcases hq with ⟨w, hw, hwq⟩
  rcases hsurj ⟨w, hw⟩ with ⟨v, hv⟩
  have hvTerminal : v.1 C.totalTargetPosition = w := by
    have hv' := congrArg Subtype.val hv
    exact hv'
  let family := C.extendPositionFamily N (positiveArrow a) h v.1 q
  have hfamily : family ∈
      (append R C (positiveArrow a) h).trajectorySubmodule N U :=
    C.extendPositionFamily_mem_trajectorySubmodule_positive
      N a h U v q
        ((congrArg (fun r ↦ moduleArrowMap N a r) hvTerminal).trans hwq)
  refine ⟨⟨family, hfamily⟩, Subtype.ext ?_⟩
  change family
      (append R C (positiveArrow a) h).totalTargetPosition = q
  have hend :
      (append R C (positiveArrow a) h).targetPosition =
        appendEndPosition C (positiveArrow a) h := by
    apply Subtype.ext
    rfl
  change family
      ⟨z, (append R C (positiveArrow a) h).targetPosition⟩ = q
  rw [hend]
  dsimp only [family]
  exact C.extendPositionFamily_appendEndPosition
    N (positiveArrow a) h v.1 q

/-- Surjectivity of coherent terminal evaluation is preserved by appending a
negative letter. -/
theorem trajectoryTransportMap_surjective_append_negative
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (hsurj : Function.Surjective (C.trajectoryTransportMap N U)) :
    Function.Surjective
      ((append R C (negativeArrow a) h).trajectoryTransportMap N U) := by
  rintro ⟨q, hq⟩
  change N.obj (Opposite.op (obj R z)) at q
  rw [append_path, Quiver.Path.comp_toPath_eq_cons] at hq
  unfold signedPathSubspace at hq
  unfold signedArrowSubspace at hq
  rcases hsurj ⟨moduleArrowMap N a q, hq⟩ with ⟨v, hv⟩
  have hvTerminal : v.1 C.totalTargetPosition =
      moduleArrowMap N a q := by
    have hv' := congrArg Subtype.val hv
    exact hv'
  let family := C.extendPositionFamily N (negativeArrow a) h v.1 q
  have hfamily : family ∈
      (append R C (negativeArrow a) h).trajectorySubmodule N U :=
    C.extendPositionFamily_mem_trajectorySubmodule_negative
      N a h U v q hvTerminal.symm
  refine ⟨⟨family, hfamily⟩, Subtype.ext ?_⟩
  change family
      (append R C (negativeArrow a) h).totalTargetPosition = q
  have hend :
      (append R C (negativeArrow a) h).targetPosition =
        appendEndPosition C (negativeArrow a) h := by
    apply Subtype.ext
    rfl
  change family
      ⟨z, (append R C (negativeArrow a) h).targetPosition⟩ = q
  rw [hend]
  dsimp only [family]
  exact C.extendPositionFamily_appendEndPosition
    N (negativeArrow a) h v.1 q

/-- For a length-zero word, coherent terminal evaluation is the identity on
the chosen source subspace. -/
theorem trajectoryTransportMap_surjective_of_length_eq_zero
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (hzero : C.length = 0) :
    Function.Surjective (C.trajectoryTransportMap N U) := by
  rcases C with ⟨source, target, path, hstring⟩
  change path.length = 0 at hzero
  have hsourceTarget : source = target :=
    path.eq_of_length_zero hzero
  subst target
  have hpathNil : path =
      (Quiver.Path.nil : SignedPath source source) :=
    path.eq_nil_of_length_zero hzero
  subst path
  let C : Word R :=
    { source := source
      target := source
      path := Quiver.Path.nil
      isString := hstring }
  change Function.Surjective (C.trajectoryTransportMap N U)
  have hCzero : C.length = 0 := hzero
  rintro ⟨q, hq⟩
  rw [signedPathSubspace_nil] at hq
  let family : PositionFamily N C := fun i ↦ by
    have hiZero : i.index = 0 := by
      have hiLe := i.2.index_le
      change i.index ≤ C.length at hiLe
      omega
    have hiSource : i = C.totalSourcePosition := by
      apply Position.ext_index
      rw [totalSourcePosition_index]
      exact hiZero
    cases hiSource
    exact q
  have hfamilySource : family C.totalSourcePosition = q := by
    dsimp only [family]
  have hfamily : family ∈ C.trajectorySubmodule N U := by
    rw [mem_trajectorySubmodule]
    constructor
    · rw [hfamilySource]
      exact hq
    · intro x y a i j hij
      have hiZero : i.index = 0 := by
        have hiLe := i.index_le
        rw [hCzero] at hiLe
        omega
      have hjZero : j.index = 0 := by
        have hjLe := j.index_le
        rw [hCzero] at hjLe
        omega
      rcases ArrowStep.index C a i j hij with hforward | hbackward
      · omega
      · omega
  refine ⟨⟨family, hfamily⟩, Subtype.ext ?_⟩
  change family C.totalTargetPosition = q
  have htarget : C.totalTargetPosition = C.totalSourcePosition := by
    apply Position.ext_index
    rw [totalTargetPosition_index, totalSourcePosition_index, hCzero]
  cases htarget
  exact hfamilySource

/-- Path-inductive form of surjectivity of coherent terminal evaluation. -/
theorem trajectoryTransportMap_surjective_path
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x target : Q} (p : SignedPath x target) :
    ∀ (hstring : IsString R p)
      (U : Submodule k (N.obj (Opposite.op (obj R x)))),
      Function.Surjective
        (({ source := x, target := target, path := p,
            isString := hstring } : Word R).trajectoryTransportMap N U) := by
  induction hlength : p.length using Nat.strong_induction_on generalizing x target with
  | h n ih =>
    cases p with
    | nil =>
        intro hstring U
        apply trajectoryTransportMap_surjective_of_length_eq_zero
        rfl
    | @cons middle _ p e =>
        change Q at middle
        intro hfullString U
        have hn : p.length + 1 = n := by
          simpa only [Quiver.Path.length_cons] using hlength
        have hpSub : IsContiguousSubpath p (p.cons e) := by
          refine ⟨Quiver.Path.nil, e.toPath, ?_⟩
          simp only [Quiver.Path.nil_comp,
            Quiver.Path.comp_toPath_eq_cons]
        have hpString : IsString R p :=
          IsString.of_contiguousSubpath R hfullString hpSub
        let prefixWord : Word R :=
          { source := x
            target := middle
            path := p
            isString := hpString }
        have happend :
            IsString R (prefixWord.path.comp e.toPath) := by
          simpa only [prefixWord, Quiver.Path.comp_toPath_eq_cons] using
            hfullString
        let C : Word R := append R prefixWord e happend
        have hlt : p.length < n := by omega
        have hprefixSurjective :=
          ih p.length hlt p rfl hpString U
        change Function.Surjective (C.trajectoryTransportMap N U)
        cases e with
        | inl a =>
            exact trajectoryTransportMap_surjective_append_positive
              N prefixWord a happend U hprefixSurjective
        | inr a =>
            exact trajectoryTransportMap_surjective_append_negative
              N prefixWord a happend U hprefixSurjective

/-- Coherent terminal evaluation is onto the transported subspace for every
finite string word. -/
theorem trajectoryTransportMap_surjective
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source)))) :
    Function.Surjective (C.trajectoryTransportMap N U) := by
  exact trajectoryTransportMap_surjective_path N C.path C.isString U

/-- A single chosen linear section of terminal evaluation into coherent
trajectories. -/
def trajectorySection
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source)))) :
    signedPathSubspace N C.path U →ₗ[k]
      C.trajectorySubmodule N U :=
  Classical.choose
    ((C.trajectoryTransportMap N U).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2
        (C.trajectoryTransportMap_surjective N U)))

/-- The coherent trajectory section has the requested terminal value. -/
theorem trajectoryTransportMap_comp_trajectorySection
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source)))) :
    C.trajectoryTransportMap N U ∘ₗ C.trajectorySection N U =
      LinearMap.id :=
  Classical.choose_spec
    ((C.trajectoryTransportMap N U).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2
        (C.trajectoryTransportMap_surjective N U)))

/-- The coherent linear lift from the full transported subspace to one word
position. -/
def coherentPositionMap
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    {x : Q} (i : C.PositionAt x) :
    signedPathSubspace N C.path U →ₗ[k]
      N.obj (Opposite.op (obj R x)) :=
  (C.trajectoryPositionAtMap N U i).comp
    (C.trajectorySection N U)

/-- Coherent position lifts respect every arrow step displayed by the word. -/
theorem moduleArrowMap_coherentPositionMap_of_arrowStep
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j)
    (q : signedPathSubspace N C.path U) :
    moduleArrowMap N a (C.coherentPositionMap N U i q) =
      C.coherentPositionMap N U j q := by
  exact C.moduleArrowMap_trajectoryPositionAtMap_of_arrowStep
    N U a i j hij (C.trajectorySection N U q)

/-- Coherent position lifts respect every ordinary path realized
monotonically along the word. -/
theorem modulePathMap_coherentPositionMap_of_pathReach
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    {x y : Q} (p : Quiver.Path x y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.PathReach p i j)
    (q : signedPathSubspace N C.path U) :
    modulePathMap N p (C.coherentPositionMap N U i q) =
      C.coherentPositionMap N U j q := by
  exact C.modulePathMap_trajectoryPositionAtMap_of_pathReach
    N U p i j hij (C.trajectorySection N U q)

/-- At the terminal position, the coherent lift recovers the given
transported vector. -/
theorem coherentPositionMap_targetPosition
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : Word R)
    (U : Submodule k
      (N.obj (Opposite.op (obj R C.source))))
    (q : signedPathSubspace N C.path U) :
    C.coherentPositionMap N U C.targetPosition q = q := by
  have hright := LinearMap.congr_fun
    (C.trajectoryTransportMap_comp_trajectorySection N U) q
  have hright' := congrArg Subtype.val hright
  exact hright'

end Word

namespace EndpointWord

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

/-- Coherent detector-class evaluation at one position of the detector word.
All position maps factor through the same trajectory section. -/
def coherentDetectorPositionMap
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t)
    {x : Q} (i : C.word.PositionAt x) :
    DetectorSpace N C →ₗ[k]
      N.obj (Opposite.op (obj P.toPresentation.relations x)) :=
  (C.word.coherentPositionMap N (upperBoundarySubspace N C) i).comp
    (detectorUpperRepresentative N C)

/-- Bilinear evaluation of a string-space vector and a detector class by the
coherent position lifts. -/
def coherentDetectorBilinearMap
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) (x : Q) :
    C.word.Space x →ₗ[k] (DetectorSpace N C : Type u) →ₗ[k]
      (N.obj (Opposite.op (obj P.toPresentation.relations x)) : Type u) :=
  LinearMap.mk₂ k
    (fun v q ↦
      Finsupp.linearCombination k
        (fun i ↦ C.coherentDetectorPositionMap N i q) v)
    (by
      intro v w q
      exact map_add _ v w)
    (by
      intro c v q
      exact map_smul _ c v)
    (by
      intro v q r
      simp only [Finsupp.linearCombination_apply, map_add, smul_add,
        Finsupp.sum_add])
    (by
      intro c v q
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw => simp only [map_add, hv, hw, smul_add]
      | single i a =>
          simp only [Finsupp.linearCombination_single, map_smul, smul_smul]
          rw [mul_comm])

/-- Evaluation from the coefficient-copy string space to the ambient module
at one quiver vertex. -/
def coherentDetectorTensorMap
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) (x : Q) :
    TensorProduct k (C.word.Space x) (DetectorSpace N C : Type u) →ₗ[k]
      (N.obj (Opposite.op (obj P.toPresentation.relations x)) : Type u) :=
  TensorProduct.lift (C.coherentDetectorBilinearMap N x)

@[simp]
theorem coherentDetectorTensorMap_single_tmul
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) {x : Q}
    (i : C.word.PositionAt x) (c : k) (q : DetectorSpace N C) :
    C.coherentDetectorTensorMap N x
        (Finsupp.single i c ⊗ₜ[k] q) =
      c • C.coherentDetectorPositionMap N i q := by
  exact Finsupp.linearCombination_single k c i

/-- If a word begins with an inverse arrow, then an additional outgoing
inverse either extends the whole string or closes a monomial relation against
an incoming path realized by the initial inverse arm. -/
theorem sourceIncomingStep_zeroPath_or_outgoingInverseExtension
    (C : EndpointWord S u₀ t)
    {y z : Q} (b : C.source ⟶ y) (a : z ⟶ C.source)
    (next : C.word.PositionAt z)
    (hnextIndex : next.index = 1)
    (ha : C.word.ArrowStep a next C.word.sourcePosition) :
    (∃ (w : Q) (p : Quiver.Path w C.source)
        (previous : C.word.PositionAt w),
        C.word.PathReach p previous C.word.sourcePosition ∧
          arrowMap P.toPresentation.relations b ≫
            pathMap P.toPresentation.relations p = 0) ∨
      IsString P.toPresentation.relations
          ((negativeArrow b).toPath.comp C.path) ∧
        C.sourceSign = Bool.not (S.sourceSign b) := by
  have hfirst : next.1 = (negativeArrow a).toPath := by
    rcases ha with hforward | hbackward
    · have hlength := congrArg Quiver.Path.length hforward
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
      change next.index = 1 at hnextIndex
      change 0 = next.index + 1 at hlength
      omega
    · exact hbackward.trans (Quiver.Path.nil_comp _)
  rcases next.2 with ⟨tail, htail⟩
  have hpath : C.path = (negativeArrow a).toPath.comp tail := by
    change C.path = next.1.comp tail at htail
    exact htail.trans (congrArg (fun p ↦ p.comp tail) hfirst)
  let extended : SignedPath y u₀ :=
    (negativeArrow b).toPath.comp C.path
  by_cases hstring : IsString P.toPresentation.relations extended
  · right
    have hsourceOption :=
      signedPathSourceSign_eq_not_targetSign_of_isString_prepend S
        (negativeArrow b) C.path (by
          change 0 < C.word.length
          have hle := next.index_le
          change next.index ≤ C.word.length at hle
          omega) hstring
    have hsource : C.sourceSign = Bool.not (S.sourceSign b) := by
      unfold EndpointWord.sourceSign signedPathSourceSignOr
      rw [hsourceOption]
      rfl
    exact ⟨hstring, hsource⟩
  · left
    have htwoReduced : IsReduced
        ((negativeArrow b).toPath.comp (negativeArrow a).toPath) := by
      exact Word.isReduced_negativeArrow_comp_negativeArrow b a
    have hreduced : IsReduced extended := by
      change IsReduced ((negativeArrow b).toPath.comp C.path)
      rw [hpath]
      apply isReduced_comp_of_overlap
        (negativeArrow b).toPath (negativeArrow a).toPath tail (by simp)
      · exact htwoReduced
      · rw [← hpath]
        exact C.isString.1
    have hforward : AvoidsRelations P.toPresentation.relations extended := by
      have hnil : AvoidsRelations P.toPresentation.relations
          (Quiver.Path.nil : SignedPath y y) :=
        avoidsRelations_of_length_lt_two
          P.toPresentation.relations P.toPresentation.admissible
          (Quiver.Path.nil : SignedPath y y) (by simp)
      have hright : AvoidsRelations P.toPresentation.relations C.path :=
        C.isString.2.1
      have hglue : AvoidsRelations P.toPresentation.relations
          ((Quiver.Path.nil : SignedPath y y).comp
            ((negativeArrow b).toPath.comp C.path)) :=
        avoidsRelations_comp_negativeArrow_comp
          P.toPresentation.relations
          (Quiver.Path.nil : SignedPath y y) b C.path
          hnil hright
      intro r s p hp
      apply hglue p
      simpa only [extended, Quiver.Path.nil_comp] using hp
    have hnotReverse :
        ¬ AvoidsRelations P.toPresentation.relations extended.reverse := by
      intro hreverse
      exact hstring ⟨hreduced, hforward, hreverse⟩
    unfold AvoidsRelations at hnotReverse
    push Not at hnotReverse
    obtain ⟨r, s, p, hpSub, hpZero⟩ := hnotReverse
    have hpSub' : IsContiguousSubpath (positivePath p)
        (C.path.reverse.comp (positiveArrow b).toPath) := by
      simpa only [extended, Quiver.Path.reverse_comp,
        Quiver.Path.reverse_toPath, reverse_negativeArrow] using hpSub
    rcases hpSub' with ⟨before, after, htotal⟩
    have hafterZero : after.length = 0 := by
      by_contra hafter
      have hafterPos : 0 < after.length := Nat.pos_of_ne_zero hafter
      have hlength := congrArg Quiver.Path.length htotal
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath,
        positivePath_length, length_reverse] at hlength
      have hle : before.length + (positivePath p).length ≤
          C.path.reverse.length := by
        simp only [positivePath_length, length_reverse]
        omega
      have hprefix :
          (before.comp (positivePath p)).comp after =
            C.path.reverse.comp (positiveArrow b).toPath := by
        simpa only [Quiver.Path.comp_assoc] using htotal.symm
      have hle' : (before.comp (positivePath p)).length ≤
          C.path.reverse.length := by
        simpa only [Quiver.Path.length_comp] using hle
      rcases path_exists_comp_of_comp_eq_comp_of_length_le
          hprefix hle' with ⟨suffix, hfactor⟩
      have hpInside : IsContiguousSubpath (positivePath p) C.path.reverse :=
        ⟨before, suffix, by rw [hfactor, Quiver.Path.comp_assoc]⟩
      exact (C.isString.2.2 p hpInside) hpZero
    have hafterTarget := after.eq_of_length_zero hafterZero
    cases hafterTarget
    have hafterNil : after = Quiver.Path.nil :=
      after.eq_nil_of_length_zero hafterZero
    subst after
    cases p with
    | nil =>
        have hpNonzero := pathMap_ne_zero_of_length_lt_two
          P.toPresentation.admissible
          (Quiver.Path.nil : Quiver.Path r r) (by simp)
        exact False.elim (hpNonzero hpZero)
    | @cons v _ p d =>
        have hcomp :
            C.path.reverse.comp (positiveArrow b).toPath =
              (before.comp (positivePath p)).comp
                (positiveArrow d).toPath := by
          simpa only [positivePath_cons, positivePath_toPath,
            Quiver.Path.comp_assoc, Quiver.Path.comp_nil] using htotal
        have hprefLength : C.path.reverse.length =
            (before.comp (positivePath p)).length := by
          have hlength := congrArg Quiver.Path.length hcomp
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          rw [positivePath_length] at hlength
          simp only [Quiver.Path.length_comp, positivePath_length]
          change C.path.reverse.length = before.length + p.length
          omega
        rcases path_comp_decomposition_unique hcomp hprefLength with
          ⟨hsource, hprefixHeq, hsuffixHeq⟩
        cases hsource
        have hd : d = b := by
          have hsuffix : (positiveArrow b).toPath =
              (positiveArrow d).toPath := hsuffixHeq.eq
          have harrow := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
          exact (Sum.inl.inj (eq_of_heq harrow)).symm
        cases hd
        have hprefix : C.path.reverse = before.comp (positivePath p) :=
          hprefixHeq.eq
        have hpathReverse :
            C.path = (positivePath p).reverse.comp before.reverse := by
          have hreversed := congrArg Quiver.Path.reverse hprefix
          simpa only [Quiver.Path.reverse_reverse,
            Quiver.Path.reverse_comp] using hreversed
        let previous : C.word.PositionAt r :=
          ⟨(positivePath p).reverse, ⟨before.reverse, hpathReverse⟩⟩
        refine ⟨r, p, previous, ?_, ?_⟩
        · apply C.word.pathReach_of_prefix_eq_positivePath_reverse
          exact (Quiver.Path.nil_comp _).symm
        · rw [arrowMap, pathMap_comp]
          exact hpZero

/-- If a word begins with an ordinary outgoing arrow, every distinct
outgoing arrow gives a compatible inverse extension at the source boundary. -/
theorem sourceOutgoingStep_outgoingInverseExtension
    (C : EndpointWord S u₀ t)
    {y z : Q} (b : C.source ⟶ y) (a : C.source ⟶ z)
    (next : C.word.PositionAt z)
    (hnextIndex : next.index = 1)
    (ha : C.word.ArrowStep a C.word.sourcePosition next)
    (hnot : ¬ ∃ j : C.word.PositionAt y,
      C.word.ArrowStep b C.word.sourcePosition j) :
    IsString P.toPresentation.relations
        ((negativeArrow b).toPath.comp C.path) ∧
      C.sourceSign = Bool.not (S.sourceSign b) := by
  have hfirst : next.1 = (positiveArrow a).toPath := by
    rcases ha with hforward | hbackward
    · exact hforward.trans (Quiver.Path.nil_comp _)
    · have hlength := congrArg Quiver.Path.length hbackward
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
      change next.index = 1 at hnextIndex
      change 0 = next.index + 1 at hlength
      omega
  rcases next.2 with ⟨tail, htail⟩
  have hpath : C.path = (positiveArrow a).toPath.comp tail := by
    change C.path = next.1.comp tail at htail
    exact htail.trans (congrArg (fun p ↦ p.comp tail) hfirst)
  have hba : (⟨y, b⟩ : Quiver.Star C.source) ≠ ⟨z, a⟩ := by
    intro hba
    cases hba
    exact hnot ⟨next, ha⟩
  have htwoReduced : IsReduced
      ((negativeArrow b).toPath.comp (positiveArrow a).toPath) := by
    exact Word.isReduced_negativeArrow_comp_positiveArrow_of_star_ne b a hba
  have hreduced : IsReduced
      ((negativeArrow b).toPath.comp C.path) := by
    rw [hpath]
    apply isReduced_comp_of_overlap
      (negativeArrow b).toPath (positiveArrow a).toPath tail (by simp)
    · exact htwoReduced
    · rw [← hpath]
      exact C.isString.1
  have hforward : AvoidsRelations P.toPresentation.relations
      ((negativeArrow b).toPath.comp C.path) := by
    have hnil : AvoidsRelations P.toPresentation.relations
        (Quiver.Path.nil : SignedPath y y) :=
      avoidsRelations_of_length_lt_two
        P.toPresentation.relations P.toPresentation.admissible
        (Quiver.Path.nil : SignedPath y y) (by simp)
    have hglue : AvoidsRelations P.toPresentation.relations
        ((Quiver.Path.nil : SignedPath y y).comp
          ((negativeArrow b).toPath.comp C.path)) :=
      avoidsRelations_comp_negativeArrow_comp
        P.toPresentation.relations
        (Quiver.Path.nil : SignedPath y y) b C.path
        hnil C.isString.2.1
    intro r s p hp
    apply hglue p
    simpa only [Quiver.Path.nil_comp] using hp
  have htailReverse : AvoidsRelations P.toPresentation.relations
      tail.reverse := by
    apply AvoidsRelations.of_contiguousSubpath
      P.toPresentation.relations C.isString.2.2
    refine ⟨Quiver.Path.nil, (negativeArrow a).toPath, ?_⟩
    have hreversed : C.path.reverse =
        tail.reverse.comp (negativeArrow a).toPath := by
      calc
        C.path.reverse =
            ((positiveArrow a).toPath.comp tail).reverse :=
          congrArg Quiver.Path.reverse hpath
        _ = tail.reverse.comp (negativeArrow a).toPath := by
          rw [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
            reverse_positiveArrow]
    exact hreversed.trans (Quiver.Path.nil_comp _).symm
  have hsingle : AvoidsRelations P.toPresentation.relations
      (positiveArrow b).toPath := by
    exact avoidsRelations_of_length_lt_two
      P.toPresentation.relations P.toPresentation.admissible
      (positiveArrow b).toPath (by simp)
  have hreverse : AvoidsRelations P.toPresentation.relations
      ((negativeArrow b).toPath.comp C.path).reverse := by
    have hglue : AvoidsRelations P.toPresentation.relations
        (tail.reverse.comp ((negativeArrow a).toPath.comp
          (positiveArrow b).toPath)) :=
      avoidsRelations_comp_negativeArrow_comp
        P.toPresentation.relations tail.reverse a (positiveArrow b).toPath
        htailReverse hsingle
    have hreversed : C.path.reverse =
        tail.reverse.comp (negativeArrow a).toPath := by
      calc
        C.path.reverse =
            ((positiveArrow a).toPath.comp tail).reverse :=
          congrArg Quiver.Path.reverse hpath
        _ = tail.reverse.comp (negativeArrow a).toPath := by
          rw [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
            reverse_positiveArrow]
    have htotal : ((negativeArrow b).toPath.comp C.path).reverse =
        tail.reverse.comp ((negativeArrow a).toPath.comp
          (positiveArrow b).toPath) := by
      calc
        ((negativeArrow b).toPath.comp C.path).reverse =
            C.path.reverse.comp (positiveArrow b).toPath := by
          rw [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
            reverse_negativeArrow]
        _ = (tail.reverse.comp (negativeArrow a).toPath).comp
            (positiveArrow b).toPath :=
          congrArg (fun p ↦ p.comp (positiveArrow b).toPath) hreversed
        _ = tail.reverse.comp ((negativeArrow a).toPath.comp
            (positiveArrow b).toPath) := by
          rfl
    intro r s p hp
    apply hglue p
    rw [← htotal]
    exact hp
  have hstring : IsString P.toPresentation.relations
      ((negativeArrow b).toPath.comp C.path) :=
    ⟨hreduced, hforward, hreverse⟩
  have hsource : C.sourceSign = Bool.not (S.sourceSign b) := by
    have hsourceA : C.sourceSign = S.sourceSign a := by
      unfold EndpointWord.sourceSign signedPathSourceSignOr
      have hs : signedPathSourceSign S C.path =
          some (S.sourceSign a) := by
        calc
          signedPathSourceSign S C.path =
              signedPathSourceSign S
                ((positiveArrow a).toPath.comp tail) :=
            congrArg (signedPathSourceSign S) hpath
          _ = some (S.sourceSign a) :=
            signedPathSourceSign_toPath_comp S (positiveArrow a) tail
      rw [hs]
      rfl
    have hsignNe := S.sourceSign_ne hba
    rw [hsourceA]
    cases haSign : S.sourceSign a <;>
      cases hbSign : S.sourceSign b <;> simp_all
  exact ⟨hstring, hsource⟩

/-- At an internal word position, every ordinary arrow not displayed out of
that position forms a zero two-arrow path with some displayed incoming
arrow.  Peaks use uniqueness of a left continuation, valleys use the
degree-two bound, and the two mixed orientations use uniqueness of a right
continuation. -/
theorem exists_incomingArrowStep_comp_eq_zero_of_internal_not_arrowStep
    (C : EndpointWord S u₀ t)
    {x y : Q} (b : x ⟶ y) (i : C.word.PositionAt x)
    (hpos : 0 < i.index) (hlt : i.index < C.word.length)
    (hnot : ¬ ∃ j : C.word.PositionAt y,
      C.word.ArrowStep b i j) :
    ∃ (w : Q) (a : w ⟶ x) (previous : C.word.PositionAt w),
      C.word.ArrowStep a previous i ∧
        arrowMap P.toPresentation.relations b ≫
          arrowMap P.toPresentation.relations a = 0 := by
  rcases C.word.exists_arrowStep_of_index_pos ⟨x, i⟩ hpos with
    ⟨w, previous, a, hpreviousIndex, ha⟩ |
    ⟨w, previous, a, hpreviousIndex, ha⟩ <;>
  rcases C.word.exists_arrowStep_of_index_lt_length ⟨x, i⟩ hlt with
    ⟨z, next, c, hnextIndex, hc⟩ |
    ⟨z, next, c, hnextIndex, hc⟩
  · refine ⟨w, a, previous, ha, ?_⟩
    by_contra hbSurvives
    have hcSurvives :
        arrowMap P.toPresentation.relations c ≫
          arrowMap P.toPresentation.relations a ≠ 0 := by
      rw [arrowMap, arrowMap, pathMap_comp]
      apply C.word.pathMap_ne_zero_of_pathReach
        (a.toPath.cons c) previous next
      exact ⟨i, ⟨previous, rfl, ha⟩, hc⟩
    have hbc : (⟨y, b⟩ : Quiver.Star x) = ⟨z, c⟩ :=
      congrArg Subtype.val
        (@Subsingleton.elim _ (P.rightContinuationArrow_subsingleton a)
          (⟨⟨y, b⟩, hbSurvives⟩ : P.RightContinuationArrow a)
          (⟨⟨z, c⟩, hcSurvives⟩ : P.RightContinuationArrow a))
    cases hbc
    exact hnot ⟨next, hc⟩
  · by_cases hba : arrowMap P.toPresentation.relations b ≫
        arrowMap P.toPresentation.relations a = 0
    · exact ⟨w, a, previous, ha, hba⟩
    · refine ⟨z, c, next, hc, ?_⟩
      by_contra hbc
      have hac : (⟨w, a⟩ : Quiver.Costar x) = ⟨z, c⟩ :=
        congrArg Subtype.val
          (@Subsingleton.elim _ (P.leftContinuationArrow_subsingleton b)
            (⟨⟨w, a⟩, hba⟩ : P.LeftContinuationArrow b)
            (⟨⟨z, c⟩, hbc⟩ : P.LeftContinuationArrow b))
      exact (C.word.incomingAdjacentArrows_ne a c previous i next
        hpreviousIndex hnextIndex ha hc) hac
  · exfalso
    have hba : (⟨y, b⟩ : Quiver.Star x) ≠ ⟨w, a⟩ := by
      intro hba
      cases hba
      exact hnot ⟨previous, ha⟩
    have hca : (⟨z, c⟩ : Quiver.Star x) ≠ ⟨w, a⟩ :=
      C.word.outgoingAdjacentArrows_ne a c previous i next
        hpreviousIndex hnextIndex ha hc |>.symm
    have hbc : (⟨y, b⟩ : Quiver.Star x) = ⟨z, c⟩ :=
      Word.eq_of_ne_of_ne_of_natCard_le_two
        (⟨w, a⟩ : Quiver.Star x) ⟨y, b⟩ ⟨z, c⟩
        hba hca (P.arrows_starting_le_two x)
    cases hbc
    exact hnot ⟨next, hc⟩
  · refine ⟨z, c, next, hc, ?_⟩
    by_contra hbSurvives
    have haSurvives :
        arrowMap P.toPresentation.relations a ≫
          arrowMap P.toPresentation.relations c ≠ 0 := by
      rw [arrowMap, arrowMap, pathMap_comp]
      apply C.word.pathMap_ne_zero_of_pathReach
        (c.toPath.cons a) next previous
      exact ⟨i, ⟨next, rfl, hc⟩, ha⟩
    have hba : (⟨y, b⟩ : Quiver.Star x) = ⟨w, a⟩ :=
      congrArg Subtype.val
        (@Subsingleton.elim _ (P.rightContinuationArrow_subsingleton c)
          (⟨⟨y, b⟩, hbSurvives⟩ : P.RightContinuationArrow c)
          (⟨⟨w, a⟩, haSurvives⟩ : P.RightContinuationArrow c))
    cases hba
    exact hnot ⟨previous, ha⟩

/-- Detector position maps respect every arrow step displayed by the word. -/
theorem moduleArrowMap_coherentDetectorPositionMap_of_arrowStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t)
    {x y : Q} (a : x ⟶ y)
    (i : C.word.PositionAt x) (j : C.word.PositionAt y)
    (hij : C.word.ArrowStep a i j)
    (q : DetectorSpace N C) :
    moduleArrowMap N a (C.coherentDetectorPositionMap N i q) =
      C.coherentDetectorPositionMap N j q := by
  exact C.word.moduleArrowMap_coherentPositionMap_of_arrowStep
    N (upperBoundarySubspace N C) a i j hij
      (detectorUpperRepresentative N C q)

/-- An incoming displayed path annihilates every outgoing arrow whose
concatenation with that path is a relation. -/
theorem moduleArrowMap_coherentDetectorPositionMap_eq_zero_of_incomingPath
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {w x y : Q} (p : Quiver.Path w x) (b : x ⟶ y)
    (previous : C.word.PositionAt w) (i : C.word.PositionAt x)
    (hp : C.word.PathReach p previous i)
    (hzero : arrowMap P.toPresentation.relations b ≫
        pathMap P.toPresentation.relations p = 0)
    (q : DetectorSpace N C) :
    moduleArrowMap N b (C.coherentDetectorPositionMap N i q) = 0 := by
  change moduleArrowMap N b
      (C.word.coherentPositionMap N (upperBoundarySubspace N C) i
        (detectorUpperRepresentative N C q)) = 0
  rw [← C.word.modulePathMap_coherentPositionMap_of_pathReach
    N (upperBoundarySubspace N C) p previous i hp
      (detectorUpperRepresentative N C q)]
  have hmorphism :
      modulePathMap N p ≫ moduleArrowMap N b = 0 := by
    unfold modulePathMap moduleArrowMap
    rw [← Functor.map_comp, ← op_comp, hzero]
    exact N.map_zero _ _
  have happly := congrArg
    (fun f ↦ f.hom (C.coherentDetectorPositionMap N previous q))
    hmorphism
  change moduleArrowMap N b
      (modulePathMap N p
        (C.coherentDetectorPositionMap N previous q)) = 0
  exact happly.trans (by rfl)

/-- Every non-displayed outgoing arrow kills the coherent detector value at
an internal word position. -/
theorem moduleArrowMap_coherentDetectorPositionMap_eq_zero_of_internal_not_arrowStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {x y : Q} (b : x ⟶ y) (i : C.word.PositionAt x)
    (hpos : 0 < i.index) (hlt : i.index < C.word.length)
    (hnot : ¬ ∃ j : C.word.PositionAt y,
      C.word.ArrowStep b i j)
    (q : DetectorSpace N C) :
    moduleArrowMap N b (C.coherentDetectorPositionMap N i q) = 0 := by
  obtain ⟨w, a, previous, ha, hzero⟩ :=
    C.exists_incomingArrowStep_comp_eq_zero_of_internal_not_arrowStep
      b i hpos hlt hnot
  apply C.moduleArrowMap_coherentDetectorPositionMap_eq_zero_of_incomingPath
    N a.toPath b previous i
  · exact ⟨previous, rfl, ha⟩
  · simpa only [arrowMap] using hzero

/-- Membership in an upper boundary subspace is exactly the vanishing needed
for any witnessed compatible outgoing inverse extension. -/
theorem moduleArrowMap_eq_zero_of_mem_upperBoundarySubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t)
    (out : C.OutgoingInverseExtension)
    (v : N.obj (Opposite.op
      (obj P.toPresentation.relations C.source)))
    (hv : v ∈ upperBoundarySubspace N C) :
    moduleArrowMap N out.1.2 v = 0 := by
  let hnon : Nonempty C.OutgoingInverseExtension := ⟨out⟩
  simp only [upperBoundarySubspace, hnon, dite_true] at hv
  let chosen := Classical.choice hnon
  have hchosen : chosen = out :=
    @Subsingleton.elim C.OutgoingInverseExtension
      C.outgoingInverseExtension_subsingleton chosen out
  change moduleArrowMap N chosen.1.2 v = 0 at hv
  rwa [hchosen] at hv

/-- A witnessed compatible outgoing inverse extension kills the coherent
detector value at the source endpoint. -/
theorem moduleArrowMap_coherentDetectorPositionMap_source_eq_zero
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t)
    (out : C.OutgoingInverseExtension)
    (q : DetectorSpace N C) :
    moduleArrowMap N out.1.2
      (C.coherentDetectorPositionMap N C.word.sourcePosition q) = 0 := by
  let trajectory := C.word.trajectorySection N
    (upperBoundarySubspace N C) (detectorUpperRepresentative N C q)
  have hsourceMem : trajectory.1 C.word.totalSourcePosition ∈
      upperBoundarySubspace N C :=
    ((C.word.mem_trajectorySubmodule N
      (upperBoundarySubspace N C) trajectory.1).1 trajectory.property).1
  apply C.moduleArrowMap_eq_zero_of_mem_upperBoundarySubspace
    N out
  exact hsourceMem

/-- A witnessed compatible outgoing inverse extension of the opposite
trivial word kills the coherent detector value at the target endpoint. -/
theorem moduleArrowMap_coherentDetectorPositionMap_target_eq_zero
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t)
    (out : C.oppositeVertex.OutgoingInverseExtension)
    (q : DetectorSpace N C) :
    moduleArrowMap N out.1.2
      (C.coherentDetectorPositionMap N C.word.targetPosition q) = 0 := by
  let representative := detectorRepresentative N C q
  have hupper :
      (representative :
        N.obj (Opposite.op
          (obj P.toPresentation.relations u₀))) ∈
        upperBoundarySubspace N C.oppositeVertex := by
    rw [← upperSubspace_oppositeVertex]
    exact representative.property.1
  let value : N.obj (Opposite.op
      (obj P.toPresentation.relations C.oppositeVertex.source)) := by
    change N.obj (Opposite.op
      (obj P.toPresentation.relations u₀))
    exact representative.1
  have hupper' : value ∈
      upperBoundarySubspace N C.oppositeVertex := by
    change representative.1 ∈
      upperBoundarySubspace N C.oppositeVertex
    exact hupper
  have hzero := C.oppositeVertex.moduleArrowMap_eq_zero_of_mem_upperBoundarySubspace
    N out value hupper'
  have htarget := C.word.coherentPositionMap_targetPosition N
    (upperBoundarySubspace N C) (detectorUpperRepresentative N C q)
  change C.coherentDetectorPositionMap N C.word.targetPosition q =
      (detectorUpperRepresentative N C q :
        N.obj (Opposite.op
          (obj P.toPresentation.relations u₀))) at htarget
  rw [htarget]
  have hrepresentative :
      (detectorUpperRepresentative N C q :
        N.obj (Opposite.op
          (obj P.toPresentation.relations u₀))) = representative.1 :=
    rfl
  rw [hrepresentative]
  change moduleArrowMap N out.1.2 value = 0
  exact hzero

/-- Every non-displayed outgoing arrow kills the coherent detector value at
the source endpoint.  A failed inverse extension contributes its exact
initial monomial relation; a successful extension is killed by the source
upper boundary.  For a trivial word the two endpoint polarizations partition
all outgoing arrows. -/
theorem moduleArrowMap_coherentDetectorPositionMap_source_eq_zero_of_not_arrowStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {y : Q} (b : C.source ⟶ y)
    (hnot : ¬ ∃ j : C.word.PositionAt y,
      C.word.ArrowStep b C.word.sourcePosition j)
    (q : DetectorSpace N C) :
    moduleArrowMap N b
      (C.coherentDetectorPositionMap N C.word.sourcePosition q) = 0 := by
  by_cases hlength : C.word.length = 0
  · rcases C with ⟨source, path, hCstring, hCtarget⟩
    change path.length = 0 at hlength
    have hsourceTarget : source = u₀ :=
      path.eq_of_length_zero hlength
    subst source
    have hpathNil : path = Quiver.Path.nil :=
      path.eq_nil_of_length_zero hlength
    subst path
    let C : EndpointWord S u₀ t :=
      ⟨u₀, Quiver.Path.nil, hCstring, hCtarget⟩
    change DetectorSpace N C at q
    change moduleArrowMap N b
      (C.coherentDetectorPositionMap N C.word.sourcePosition q) = 0
    have hClength : C.word.length = 0 := rfl
    have hsourceSign : C.sourceSign = Bool.not t := by
      unfold EndpointWord.sourceSign signedPathSourceSignOr
      rw [signedPathSourceSign_nil]
      rfl
    have hpositions : C.word.sourcePosition = C.word.targetPosition := by
      apply Word.PositionAt.ext_index
      change 0 = C.word.length
      exact hClength.symm
    by_cases hsign : C.sourceSign = Bool.not (S.sourceSign b)
    · have hstring : IsString P.toPresentation.relations
          ((negativeArrow b).toPath.comp C.path) := by
        change IsString P.toPresentation.relations
          ((negativeArrow b).toPath.comp
            (Quiver.Path.nil : SignedPath u₀ u₀))
        apply isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath,
          Quiver.Path.length_nil]
        omega
      let out : C.OutgoingInverseExtension :=
        ⟨⟨y, b⟩, hstring, hsign⟩
      exact C.moduleArrowMap_coherentDetectorPositionMap_source_eq_zero
        N out q
    · have hoppositeSign : C.oppositeVertex.sourceSign =
          Bool.not (S.sourceSign b) := by
        have hopposite : C.oppositeVertex.sourceSign = t := by
          simp only [oppositeVertex, vertex_sourceSign, Bool.not_not]
        rw [hopposite]
        apply Bool.eq_not_iff.mpr
        intro ht
        apply hsign
        exact hsourceSign.trans (congrArg Bool.not ht)
      have hstring : IsString P.toPresentation.relations
          ((negativeArrow b).toPath.comp C.oppositeVertex.path) := by
        change IsString P.toPresentation.relations
          ((negativeArrow b).toPath.comp
            (Quiver.Path.nil : SignedPath u₀ u₀))
        apply isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible
        simp only [Quiver.Path.length_comp,
          Quiver.Path.length_toPath, Quiver.Path.length_nil]
        omega
      let out : C.oppositeVertex.OutgoingInverseExtension :=
        ⟨⟨y, b⟩, hstring, hoppositeSign⟩
      rw [hpositions]
      exact C.moduleArrowMap_coherentDetectorPositionMap_target_eq_zero
        N out q
  · have hpositiveLength : 0 < C.word.length := Nat.pos_of_ne_zero hlength
    rcases C.word.exists_arrowStep_of_index_lt_length
        C.word.totalSourcePosition hpositiveLength with
      ⟨z, next, a, hnextIndex, ha⟩ |
      ⟨z, next, a, hnextIndex, ha⟩
    · obtain ⟨hstring, hsign⟩ :=
        C.sourceOutgoingStep_outgoingInverseExtension
          b a next hnextIndex ha hnot
      let out : C.OutgoingInverseExtension :=
        ⟨⟨y, b⟩, hstring, hsign⟩
      exact C.moduleArrowMap_coherentDetectorPositionMap_source_eq_zero
        N out q
    · rcases C.sourceIncomingStep_zeroPath_or_outgoingInverseExtension
        b a next hnextIndex ha with hzero | hout
      · obtain ⟨w, p, previous, hp, hrelation⟩ := hzero
        exact C.moduleArrowMap_coherentDetectorPositionMap_eq_zero_of_incomingPath
          N p b previous C.word.sourcePosition hp hrelation q
      · obtain ⟨hstring, hsign⟩ := hout
        let out : C.OutgoingInverseExtension :=
          ⟨⟨y, b⟩, hstring, hsign⟩
        exact C.moduleArrowMap_coherentDetectorPositionMap_source_eq_zero
          N out q

/-- Every non-displayed outgoing arrow kills the coherent detector value at
the target endpoint.  The opposite trivial upper boundary handles every
surviving or distinct outgoing continuation; a zero continuation is killed
by the incoming-path relation. -/
theorem moduleArrowMap_coherentDetectorPositionMap_target_eq_zero_of_not_arrowStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {y : Q} (b : u₀ ⟶ y)
    (hnot : ¬ ∃ j : C.word.PositionAt y,
      C.word.ArrowStep b C.word.targetPosition j)
    (q : DetectorSpace N C) :
    moduleArrowMap N b
      (C.coherentDetectorPositionMap N C.word.targetPosition q) = 0 := by
  by_cases hlength : C.word.length = 0
  · rcases C with ⟨source, path, hCstring, hCtarget⟩
    change path.length = 0 at hlength
    have hsourceTarget : source = u₀ :=
      path.eq_of_length_zero hlength
    subst source
    have hpathNil : path = Quiver.Path.nil :=
      path.eq_nil_of_length_zero hlength
    subst path
    let C : EndpointWord S u₀ t :=
      ⟨u₀, Quiver.Path.nil, hCstring, hCtarget⟩
    change DetectorSpace N C at q
    change moduleArrowMap N b
      (C.coherentDetectorPositionMap N C.word.targetPosition q) = 0
    have hClength : C.word.length = 0 := rfl
    have hpositions : C.word.sourcePosition = C.word.targetPosition := by
      apply Word.PositionAt.ext_index
      change 0 = C.word.length
      exact hClength.symm
    have hnotSource : ¬ ∃ j : C.word.PositionAt y,
        C.word.ArrowStep b C.word.sourcePosition j := by
      rintro ⟨j, hj⟩
      apply hnot
      exact ⟨j, hpositions ▸ hj⟩
    rw [← hpositions]
    exact C.moduleArrowMap_coherentDetectorPositionMap_source_eq_zero_of_not_arrowStep
      N b hnotSource q
  · have hpositiveLength : 0 < C.word.length := Nat.pos_of_ne_zero hlength
    rcases C.word.exists_arrowStep_of_index_pos
        C.word.totalTargetPosition (by
          change 0 < C.word.targetPosition.index
          simpa only [Word.targetPosition_index] using hpositiveLength) with
      ⟨z, previous, a, hpreviousIndex, ha⟩ |
      ⟨z, previous, a, hpreviousIndex, ha⟩
    · by_cases hzero : arrowMap P.toPresentation.relations b ≫
          arrowMap P.toPresentation.relations a = 0
      · apply C.moduleArrowMap_coherentDetectorPositionMap_eq_zero_of_incomingPath
          N a.toPath b previous C.word.targetPosition
        · exact ⟨previous, rfl, ha⟩
        · change arrowMap P.toPresentation.relations b ≫
            arrowMap P.toPresentation.relations a = 0
          exact hzero
      · have hpath : C.path =
            previous.1.comp (positiveArrow a).toPath := by
          rcases ha with hforward | hbackward
          · exact hforward
          · have hlength' := congrArg Quiver.Path.length hbackward
            simp only [Quiver.Path.length_comp,
              Quiver.Path.length_toPath] at hlength'
            change previous.index + 1 = C.word.targetPosition.index at hpreviousIndex
            change previous.index = C.word.targetPosition.index + 1 at hlength'
            omega
        have htargetA : t = S.targetSign a := by
          have hs : signedPathTargetSign S C.path =
              some (S.targetSign a) := by
            calc
              signedPathTargetSign S C.path =
                  signedPathTargetSign S
                    (previous.1.comp (positiveArrow a).toPath) :=
                congrArg (signedPathTargetSign S) hpath
              _ = some (S.targetSign a) := by
                rw [Quiver.Path.comp_toPath_eq_cons,
                  signedPathTargetSign_cons]
                rfl
          have ht := C.targetSign_eq
          unfold signedPathTargetSignOr at ht
          rw [hs] at ht
          exact ht.symm
        have hsourceB : S.sourceSign b =
            Bool.not (S.targetSign a) :=
          S.sourceSign_eq_not_targetSign a b hzero
        have hoppositeSign : C.oppositeVertex.sourceSign =
            Bool.not (S.sourceSign b) := by
          have hopposite : C.oppositeVertex.sourceSign = t := by
            simp only [oppositeVertex, vertex_sourceSign, Bool.not_not]
          rw [hopposite]
          calc
            t = S.targetSign a := htargetA
            _ = Bool.not (Bool.not (S.targetSign a)) :=
              (Bool.not_not _).symm
            _ = Bool.not (S.sourceSign b) :=
              (congrArg Bool.not hsourceB).symm
        have hstring : IsString P.toPresentation.relations
            ((negativeArrow b).toPath.comp C.oppositeVertex.path) := by
          change IsString P.toPresentation.relations
            ((negativeArrow b).toPath.comp
              (Quiver.Path.nil : SignedPath u₀ u₀))
          apply isString_of_length_lt_two P.toPresentation.relations
            P.toPresentation.admissible
          simp only [Quiver.Path.length_comp,
            Quiver.Path.length_toPath, Quiver.Path.length_nil]
          omega
        let out : C.oppositeVertex.OutgoingInverseExtension :=
          ⟨⟨y, b⟩, hstring, hoppositeSign⟩
        exact C.moduleArrowMap_coherentDetectorPositionMap_target_eq_zero
          N out q
    · have hba : (⟨y, b⟩ : Quiver.Star u₀) ≠ ⟨z, a⟩ := by
        intro hba
        cases hba
        exact hnot ⟨previous, ha⟩
      have hpath : C.path =
          previous.1.comp (negativeArrow a).toPath := by
        rcases ha with hforward | hbackward
        · have hlength' := congrArg Quiver.Path.length hforward
          simp only [Quiver.Path.length_comp,
            Quiver.Path.length_toPath] at hlength'
          change previous.index + 1 = C.word.targetPosition.index at hpreviousIndex
          change previous.index = C.word.targetPosition.index + 1 at hlength'
          omega
        · exact hbackward
      have htargetA : t = S.sourceSign a := by
        have hs : signedPathTargetSign S C.path =
            some (S.sourceSign a) := by
          calc
            signedPathTargetSign S C.path =
                signedPathTargetSign S
                  (previous.1.comp (negativeArrow a).toPath) :=
              congrArg (signedPathTargetSign S) hpath
            _ = some (S.sourceSign a) := by
              rw [Quiver.Path.comp_toPath_eq_cons,
                signedPathTargetSign_cons]
              rfl
        have ht := C.targetSign_eq
        unfold signedPathTargetSignOr at ht
        rw [hs] at ht
        exact ht.symm
      have hsignNe := S.sourceSign_ne hba
      have hoppositeSign : C.oppositeVertex.sourceSign =
          Bool.not (S.sourceSign b) := by
        have hopposite : C.oppositeVertex.sourceSign = t := by
          simp only [oppositeVertex, vertex_sourceSign, Bool.not_not]
        rw [hopposite, htargetA]
        exact Bool.eq_not_iff.mpr hsignNe.symm
      have hstring : IsString P.toPresentation.relations
          ((negativeArrow b).toPath.comp C.oppositeVertex.path) := by
        change IsString P.toPresentation.relations
          ((negativeArrow b).toPath.comp
            (Quiver.Path.nil : SignedPath u₀ u₀))
        apply isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible
        simp only [Quiver.Path.length_comp,
          Quiver.Path.length_toPath, Quiver.Path.length_nil]
        omega
      let out : C.oppositeVertex.OutgoingInverseExtension :=
        ⟨⟨y, b⟩, hstring, hoppositeSign⟩
      exact C.moduleArrowMap_coherentDetectorPositionMap_target_eq_zero
        N out q

/-- The coherent detector position maps satisfy the zero equation for every
ordinary arrow not displayed out of the given word position. -/
theorem moduleArrowMap_coherentDetectorPositionMap_eq_zero_of_not_arrowStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {x y : Q} (b : x ⟶ y) (i : C.word.PositionAt x)
    (hnot : ¬ ∃ j : C.word.PositionAt y,
      C.word.ArrowStep b i j)
    (q : DetectorSpace N C) :
    moduleArrowMap N b (C.coherentDetectorPositionMap N i q) = 0 := by
  by_cases hzero : i.index = 0
  · have hsource : C.source = x := i.1.eq_of_length_zero hzero
    subst x
    have hi : i = C.word.sourcePosition := by
      apply Word.PositionAt.ext_index
      change i.index = 0
      exact hzero
    subst i
    exact C.moduleArrowMap_coherentDetectorPositionMap_source_eq_zero_of_not_arrowStep
      N b hnot q
  · by_cases htarget : i.index = C.word.length
    · have hx : x = u₀ := i.eq_target_of_index_eq_length htarget
      subst x
      have hi : i = C.word.targetPosition := by
        apply Word.PositionAt.ext_index
        change i.index = C.word.length
        exact htarget
      subst i
      exact C.moduleArrowMap_coherentDetectorPositionMap_target_eq_zero_of_not_arrowStep
        N b hnot q
    · apply C.moduleArrowMap_coherentDetectorPositionMap_eq_zero_of_internal_not_arrowStep
        N b i (Nat.pos_of_ne_zero hzero) _ hnot q
      exact Nat.lt_of_le_of_ne i.index_le htarget

/-- Tensor evaluation intertwines one ordinary arrow on every position-basis
pure tensor. -/
theorem moduleArrowMap_coherentDetectorTensorMap_single_tmul
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {x y : Q} (a : x ⟶ y) (i : C.word.PositionAt x)
    (c : k) (q : DetectorSpace N C) :
    moduleArrowMap N a
        (C.coherentDetectorTensorMap N x
          (Finsupp.single i c ⊗ₜ[k] q)) =
      C.coherentDetectorTensorMap N y
        (C.word.arrowLinearMap a (Finsupp.single i c) ⊗ₜ[k] q) := by
  classical
  by_cases hstep : ∃ j : C.word.PositionAt y,
      C.word.ArrowStep a i j
  · let j := Classical.choose hstep
    have hij : C.word.ArrowStep a i j := Classical.choose_spec hstep
    rw [C.coherentDetectorTensorMap_single_tmul, map_smul,
      C.moduleArrowMap_coherentDetectorPositionMap_of_arrowStep N a i j hij]
    rw [C.word.arrowLinearMap_single,
      C.word.arrowOnBasis_eq_single_of_step a i j hij,
      Finsupp.smul_single_one, C.coherentDetectorTensorMap_single_tmul]
  · rw [C.coherentDetectorTensorMap_single_tmul, map_smul,
      C.moduleArrowMap_coherentDetectorPositionMap_eq_zero_of_not_arrowStep
        N a i hstep q,
      smul_zero]
    rw [C.word.arrowLinearMap_single,
      C.word.arrowOnBasis_eq_zero_of_not_exists a i hstep,
      smul_zero, TensorProduct.zero_tmul, map_zero]

/-- Tensor evaluation intertwines one ordinary arrow on an arbitrary pure
tensor. -/
theorem moduleArrowMap_coherentDetectorTensorMap_tmul
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {x y : Q} (a : x ⟶ y) (v : C.word.Space x)
    (q : DetectorSpace N C) :
    moduleArrowMap N a
        (C.coherentDetectorTensorMap N x (v ⊗ₜ[k] q)) =
      C.coherentDetectorTensorMap N y
        (C.word.arrowLinearMap a v ⊗ₜ[k] q) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      simp only [TensorProduct.add_tmul, map_add, hv, hw]
  | single i c =>
      exact C.moduleArrowMap_coherentDetectorTensorMap_single_tmul
        N a i c q

/-- The tensor evaluation maps satisfy the quiver-arrow naturality square. -/
theorem coherentDetectorTensorMap_arrow_naturality
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {x y : Q} (a : x ⟶ y) :
    ModuleCat.ofHom (C.coherentDetectorTensorMap N x) ≫
        moduleArrowMap N a =
      (ModuleCat.ofHom (C.word.arrowLinearMap a) ▷
          ModuleCat.of k (DetectorSpace N C)) ≫
        ModuleCat.ofHom (C.coherentDetectorTensorMap N y) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro v q
  change moduleArrowMap N a
      (C.coherentDetectorTensorMap N x (v ⊗ₜ[k] q)) =
    C.coherentDetectorTensorMap N y
      (C.word.arrowLinearMap a v ⊗ₜ[k] q)
  exact C.moduleArrowMap_coherentDetectorTensorMap_tmul N a v q

/-- The tensor evaluation maps satisfy naturality along every ordinary
quiver path. -/
theorem coherentDetectorTensorMap_path_naturality
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    {x y : Q} (p : Quiver.Path x y) :
    ModuleCat.ofHom (C.coherentDetectorTensorMap N x) ≫
        modulePathMap N p =
      (C.word.quiverMap p ▷ ModuleCat.of k (DetectorSpace N C)) ≫
        ModuleCat.ofHom (C.coherentDetectorTensorMap N y) := by
  induction p with
  | nil => simp
  | @cons z y p a ih =>
      rw [modulePathMap_cons,
        show C.word.quiverMap (p.cons a) =
            C.word.quiverMap p ≫ C.word.quiverMap a.toPath from
          C.word.quiverMap_comp p a.toPath,
        C.word.quiverMap_toPath]
      calc
        ModuleCat.ofHom (C.coherentDetectorTensorMap N x) ≫
              modulePathMap N p ≫ moduleArrowMap N a =
            (ModuleCat.ofHom (C.coherentDetectorTensorMap N x) ≫
              modulePathMap N p) ≫ moduleArrowMap N a :=
          (Category.assoc _ _ _).symm
        _ = ((C.word.quiverMap p ▷
              ModuleCat.of k (DetectorSpace N C)) ≫
            ModuleCat.ofHom (C.coherentDetectorTensorMap N z)) ≫
              moduleArrowMap N a := by rw [ih]
        _ = (C.word.quiverMap p ▷
              ModuleCat.of k (DetectorSpace N C)) ≫
            (ModuleCat.ofHom (C.coherentDetectorTensorMap N z) ≫
              moduleArrowMap N a) := Category.assoc _ _ _
        _ = (C.word.quiverMap p ▷
              ModuleCat.of k (DetectorSpace N C)) ≫
            ((ModuleCat.ofHom (C.word.arrowLinearMap a) ▷
                ModuleCat.of k (DetectorSpace N C)) ≫
              ModuleCat.ofHom (C.coherentDetectorTensorMap N y)) := by
          rw [C.coherentDetectorTensorMap_arrow_naturality N a]
        _ = ((C.word.quiverMap p ▷
                ModuleCat.of k (DetectorSpace N C)) ≫
              (ModuleCat.ofHom (C.word.arrowLinearMap a) ▷
                ModuleCat.of k (DetectorSpace N C))) ≫
            ModuleCat.ofHom (C.coherentDetectorTensorMap N y) :=
          (Category.assoc _ _ _).symm
        _ = ((C.word.quiverMap p ≫
              ModuleCat.ofHom (C.word.arrowLinearMap a)) ▷
                ModuleCat.of k (DetectorSpace N C)) ≫
            ModuleCat.ofHom (C.coherentDetectorTensorMap N y) := by
          rw [MonoidalCategory.comp_whiskerRight]

/-- Path naturality written directly for the descended coefficient-copy
string module and the ambient bound-quiver module. -/
theorem coherentDetectorTensorMap_boundPath_naturality
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    (hmono : IsMonomial P.toPresentation.relations)
    {x y : Q} (p : Quiver.Path x y) :
    (C.word.scalarRightModule hmono
        (ModuleCat.of k (DetectorSpace N C))).map
          (pathMap P.toPresentation.relations p).op ≫
        ModuleCat.ofHom (C.coherentDetectorTensorMap N y) =
      ModuleCat.ofHom (C.coherentDetectorTensorMap N x) ≫
        N.map (pathMap P.toPresentation.relations p).op := by
  rw [C.word.scalarRightModule_map_pathMap]
  exact (C.coherentDetectorTensorMap_path_naturality N p).symm

/-- The same path square with source and target retained as arbitrary objects
of the free linear path category. -/
theorem coherentDetectorTensorMap_pathHom_naturality
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t)
    (hmono : IsMonomial P.toPresentation.relations)
    {X Y : LinearPathCategory.Category k Q}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    (C.word.scalarRightModule hmono
        (ModuleCat.of k (DetectorSpace N C))).map
          ((LinearPathCategory.HomogeneousQuotient.quotientFunctor
            P.toPresentation.relations).map
              (LinearPathCategory.pathHom p)).op ≫
        ModuleCat.ofHom (C.coherentDetectorTensorMap N
          (LinearPathCategory.vertex X)) =
      ModuleCat.ofHom (C.coherentDetectorTensorMap N
          (LinearPathCategory.vertex Y)) ≫
        N.map ((LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map
            (LinearPathCategory.pathHom p)).op := by
  convert C.coherentDetectorTensorMap_boundPath_naturality N hmono p using 1
  all_goals rfl

/-- Tensor evaluation is natural for every morphism before passage from the
free linear path category to the bound-path quotient. -/
theorem coherentDetectorTensorMap_free_naturality
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] [N.Linear k]
    (C : EndpointWord S u₀ t)
    (hmono : IsMonomial P.toPresentation.relations)
    {X Y : LinearPathCategory.Category k Q} (f : X ⟶ Y) :
    (C.word.scalarRightModule hmono
        (ModuleCat.of k (DetectorSpace N C))).map
          ((LinearPathCategory.HomogeneousQuotient.quotientFunctor
            P.toPresentation.relations).map f).op ≫
        ModuleCat.ofHom (C.coherentDetectorTensorMap N
          (LinearPathCategory.vertex X)) =
      ModuleCat.ofHom (C.coherentDetectorTensorMap N
          (LinearPathCategory.vertex Y)) ≫
        N.map ((LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f).op := by
  let f' := LinearPathCategory.homPathLinearEquiv X Y f
  rw [← (LinearPathCategory.homPathLinearEquiv X Y).symm_apply_apply f]
  change
    (C.word.scalarRightModule hmono
        (ModuleCat.of k (DetectorSpace N C))).map
          ((LinearPathCategory.HomogeneousQuotient.quotientFunctor
            P.toPresentation.relations).map
              ((LinearPathCategory.homPathLinearEquiv X Y).symm f')).op ≫
        ModuleCat.ofHom (C.coherentDetectorTensorMap N
          (LinearPathCategory.vertex X)) =
      ModuleCat.ofHom (C.coherentDetectorTensorMap N
          (LinearPathCategory.vertex Y)) ≫
        N.map ((LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map
            ((LinearPathCategory.homPathLinearEquiv X Y).symm f')).op
  induction f' using Finsupp.induction_linear with
  | zero =>
      simp
      rfl
  | add g h hg hh =>
      simp only [map_add, op_add, Functor.map_add,
        Preadditive.add_comp, Preadditive.comp_add, hg, hh]
      rfl
  | single p c =>
      rw [LinearPathCategory.homPathLinearEquiv_symm_single]
      simp only [MagnitudeConjecture.CoveringHom.opposite_op_smul,
        Functor.map_smul,
        CategoryTheory.Linear.smul_comp,
        CategoryTheory.Linear.comp_smul]
      exact congrArg (fun g ↦ c • g)
        (C.coherentDetectorTensorMap_pathHom_naturality N hmono p)

/-- The coherent trajectory evaluation is an actual morphism from the
coefficient-copy string module to the ambient bound-quiver module. -/
def coherentDetectorModuleMap
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] [N.Linear k]
    (C : EndpointWord S u₀ t)
    (hmono : IsMonomial P.toPresentation.relations) :
    C.word.scalarRightModule hmono
        (ModuleCat.of k (DetectorSpace N C)) ⟶ N where
  app X := ModuleCat.ofHom (C.coherentDetectorTensorMap N
    (LinearPathCategory.vertex X.unop.as))
  naturality {X Y} f := by
    obtain ⟨g, hg⟩ :=
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map_surjective f.unop
    have hf : f =
        ((LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map g).op := by
      apply Quiver.Hom.unop_inj
      exact hg.symm
    rw [hf]
    exact C.coherentDetectorTensorMap_free_naturality N hmono g

@[simp]
theorem coherentDetectorModuleMap_app_obj
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] [N.Linear k]
    (C : EndpointWord S u₀ t)
    (hmono : IsMonomial P.toPresentation.relations) (x : Q) :
    (C.coherentDetectorModuleMap N hmono).app
        (Opposite.op (obj P.toPresentation.relations x)) =
      ModuleCat.ofHom (C.coherentDetectorTensorMap N x) :=
  rfl

/-- Objectwise Butler--Ringel evaluation
`S_C(F_C(N)) → N`, bundled in the category of linear modules. -/
def coherentDetectorEvaluation
    (N : MagnitudeConjecture.CoveringHom.LinearModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (C : EndpointWord S u₀ t)
    (hmono : IsMonomial P.toPresentation.relations) :
    (C.word.stringEmbeddingFunctor hmono).obj
        (C.detectorFunctor.obj N) ⟶ N :=
  ⟨C.coherentDetectorModuleMap N.obj hmono⟩

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
