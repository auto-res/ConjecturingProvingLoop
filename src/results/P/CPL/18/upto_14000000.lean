import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

def P1 (A : Set X) : Prop :=
  A ⊆ closure (interior A)

def P2 (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

def P3 (A : Set X) : Prop :=
  A ⊆ interior (closure A)


theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  exact Set.Subset.trans h interior_subset

theorem P3_of_open {A : Set X} (hA : IsOpen A) : P3 A := by
  dsimp [P3]
  exact interior_maximal subset_closure hA

theorem P2_of_open {A : Set X} (hA : IsOpen A) : P2 A := by
  dsimp [P2]
  simpa [hA.interior_eq] using (P3_of_open hA)

theorem P2_iff_P3_of_open {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  dsimp [P2, P3]
  simpa [hA.interior_eq]

theorem exists_open_subset_P2 {A : Set X} : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ P2 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro x hx
    trivial
  · dsimp [P2]
    simp [interior_univ, closure_univ]

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  dsimp [P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ closure (interior A) := hA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hx'
  | inr hxB =>
      have hx' : x ∈ closure (interior B) := hB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx'

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  dsimp [P3]
  simpa [interior_interior] using
    (interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A)))

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx'

theorem exists_P3_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, A ⊆ U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · intro x hx
    trivial
  · dsimp [Topology.P3]
    intro x hx
    simpa [closure_univ, interior_univ] using hx

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  exact Set.empty_subset _

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  simpa [hA.interior_eq] using (subset_closure hx)

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure A) := hA hxA
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure B) := hB hxB
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx'

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, Topology.P2 A) : Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := h𝒜 A hA_mem
  have hx' : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion_of_mem hy hA_mem
  exact hsubset hx'

theorem exists_open_superset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro _ _; trivial
  · dsimp [Topology.P3]
    intro x hx
    simpa [closure_univ, interior_univ] using hx

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  dsimp [Topology.P2, Topology.P3]
  -- `A` is closed, so its closure is itself
  have h_closure : (closure (A : Set X)) = A := hA.closure_eq
  constructor
  · intro hP2
    -- first, relate the two interiors that appear
    have h_closure_mono : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    have h_int_mono : interior (closure (interior A)) ⊆ interior A := by
      have h := interior_mono h_closure_mono
      simpa [h_closure] using h
    -- chain the inclusions
    have : A ⊆ interior A := Set.Subset.trans hP2 h_int_mono
    simpa [h_closure] using this
  · intro hP3
    -- `interior A` is open and contained in its closure, hence in the interior
    -- of that closure
    have h_sub : interior A ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    -- chain the inclusions
    have : A ⊆ interior A := by
      simpa [h_closure] using hP3
    exact Set.Subset.trans this h_sub

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  -- From the density hypothesis we get that the closure is the whole space
  have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _; exact h y
  -- Hence its interior is also the whole space, so the desired membership is trivial
  simpa [h_closure, interior_univ] using (by
    have : x ∈ (Set.univ : Set X) := by simp
    exact this)

theorem exists_P2_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, A ⊆ U ∧ Topology.P2 U := by
  rcases exists_open_subset_P2 (A := A) with ⟨U, _hUopen, hAU, hP2U⟩
  exact ⟨U, hAU, hP2U⟩

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P3 A) : Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := h A hA_mem
  have hx' : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion_of_mem hy hA_mem
  exact hsubset hx'

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P1 A) : Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : Topology.P1 A := h A hA_mem
  have hx' : x ∈ closure (interior A) := hP1A hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion_of_mem hy hA_mem
  exact hsubset hx'

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  exact Set.empty_subset _

theorem P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P1 A ↔ Topology.P2 A := by
  -- The density of `interior A` implies that its closure is the whole space.
  have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Hence `P2 A` holds unconditionally.
  have hP2_dense : Topology.P2 A := by
    dsimp [Topology.P2]
    intro x _
    simpa [h_closure, interior_univ] using (by
      simp : x ∈ (Set.univ : Set X))
  -- Establish the equivalence.
  constructor
  · intro _hP1
    exact hP2_dense
  · intro hP2
    exact P2_implies_P1 hP2

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    apply closure_mono
    exact interior_subset
  exact Set.Subset.trans hP2 hmono

theorem P1_iff_P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P1 A ↔ Topology.P3 A := by
  -- From the density hypothesis we have `P2 A`.
  have hP2 : Topology.P2 A := P2_of_dense_interior (X := X) h
  -- Hence `P3 A` and `P1 A` follow.
  have hP3 : Topology.P3 A := P2_implies_P3 (X := X) hP2
  have hP1 : Topology.P1 A := P2_implies_P1 hP2
  -- Establish the desired equivalence.
  exact ⟨fun _ => hP3, fun _ => hP1⟩

theorem exists_closed_superset_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ F : Set X, IsClosed F ∧ A ⊆ F ∧ Topology.P2 F := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_, ?_⟩
  · intro _ _
    simp
  · dsimp [Topology.P2]
    intro x hx
    simpa [interior_univ, closure_univ] using hx

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod A B) := by
  -- Unfold the definition of `P2` in the hypotheses and in the goal.
  dsimp [Topology.P2] at hA hB ⊢
  -- Take an arbitrary point of `A × B`.
  intro p hp
  -- Split that point into its two coordinates.
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy⟩
  -- Apply the hypotheses to each coordinate.
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hy' : y ∈ interior (closure (interior B)) := hB hy
  -- The point lies in the product of the two interior‐closures.
  have hxy :
      (x, y) ∈
        (interior (closure (interior A))).prod
        (interior (closure (interior B))) :=
    ⟨hx', hy'⟩
  -- This product set is open.
  have h_open :
      IsOpen ((interior (closure (interior A))).prod
              (interior (closure (interior B)))) :=
    (isOpen_interior).prod isOpen_interior
  -- Show that this open set is contained in the closure of
  -- `interior (A × B)`.
  have hsubset_to_closure :
      (interior (closure (interior A))).prod
        (interior (closure (interior B)))
        ⊆ closure (interior (A.prod B)) := by
    -- First enlarge to the product of the closures.
    have h1 :
        (interior (closure (interior A))).prod
          (interior (closure (interior B))) ⊆
        (closure (interior A)).prod (closure (interior B)) := by
      intro p hp
      rcases hp with ⟨hp1, hp2⟩
      exact And.intro (interior_subset hp1) (interior_subset hp2)
    -- Identify the latter set with a closure of a product.
    have h2 :
        (closure (interior A)).prod (closure (interior B)) =
          closure ((interior A).prod (interior B)) := by
      simpa using
        (closure_prod_eq (s := interior A) (t := interior B)).symm
    -- Relate the interior of a product.
    have h3 :
        interior (A.prod B) = (interior A).prod (interior B) := by
      simpa using interior_prod_eq (s := A) (t := B)
    -- Combine the inclusions.
    intro p hp
    have hp₁ : p ∈ (closure (interior A)).prod (closure (interior B)) :=
      h1 hp
    have hp₂ : p ∈ closure ((interior A).prod (interior B)) := by
      simpa [h2] using hp₁
    simpa [h3] using hp₂
  -- Use `interior_maximal` to pass from the closure to its interior.
  have hsubset :
      (interior (closure (interior A))).prod
        (interior (closure (interior B)))
        ⊆ interior (closure (interior (A.prod B))) :=
    interior_maximal hsubset_to_closure h_open
  -- Conclude by applying the inclusion to the point `hxy`.
  exact hsubset hxy

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod A B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy⟩
  -- apply the hypotheses to each coordinate
  have hx' : x ∈ closure (interior A) := hA hx
  have hy' : y ∈ closure (interior B) := hB hy
  -- point belongs to the product of the two closures
  have hxy_prod : (x, y) ∈ (closure (interior A)).prod (closure (interior B)) :=
    ⟨hx', hy'⟩
  -- rewrite using `closure_prod_eq`
  have hxy_closure : (x, y) ∈ closure ((interior A).prod (interior B)) := by
    -- `closure_prod_eq` is `closure (s.prod t) = (closure s).prod (closure t)`
    -- so we use its symmetric form
    have hEq :=
      (closure_prod_eq (s := interior A) (t := interior B)).symm
    simpa using (hEq ▸ hxy_prod)
  -- identify the interior of the product
  have hInt :
      interior (A.prod B) = (interior A).prod (interior B) := by
    simpa using interior_prod_eq (s := A) (t := B)
  -- final rewriting to reach the desired set
  simpa [hInt] using hxy_closure

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod A B) := by
  -- Unfold the definition of `P3` in the hypotheses and in the goal.
  dsimp [Topology.P3] at hA hB ⊢
  -- Take an arbitrary point of `A × B`.
  intro p hp
  -- Split that point into its two coordinates.
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy⟩
  -- Apply the hypotheses to each coordinate.
  have hx' : x ∈ interior (closure A) := hA hx
  have hy' : y ∈ interior (closure B) := hB hy
  -- The point lies in the product of the two interior‐closures.
  have hxy :
      (x, y) ∈ (interior (closure A)).prod (interior (closure B)) := by
    exact ⟨hx', hy'⟩
  -- This product set is open.
  have h_open :
      IsOpen ((interior (closure A)).prod (interior (closure B))) :=
    (isOpen_interior).prod isOpen_interior
  -- Show that this open set is contained in the closure of `A × B`.
  have hsubset_to_closure :
      (interior (closure A)).prod (interior (closure B))
        ⊆ closure (A.prod B) := by
    intro q hq
    -- First enlarge to the product of the closures.
    have hq_in :
        q ∈ (closure A).prod (closure B) := by
      rcases hq with ⟨hq1, hq2⟩
      exact ⟨interior_subset hq1, interior_subset hq2⟩
    -- Identify the latter set with a closure of a product.
    have hEq :
        (closure A).prod (closure B) = closure (A.prod B) := by
      simpa using (closure_prod_eq (s := A) (t := B)).symm
    simpa [hEq] using hq_in
  -- Use `interior_maximal` to pass from the closure to its interior.
  have hsubset :
      (interior (closure A)).prod (interior (closure B))
        ⊆ interior (closure (A.prod B)) :=
    interior_maximal hsubset_to_closure h_open
  -- Conclude by applying the inclusion to the point `hxy`.
  exact hsubset hxy

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, A i) := by
  -- Unfold the definition of `P1` in the hypotheses and goal.
  dsimp [Topology.P1] at hA ⊢
  -- Take an arbitrary point of the union.
  intro x hx
  -- Extract the index witnessing that `x` belongs to one of the sets.
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Apply the hypothesis for this index.
  have hx' : x ∈ closure (interior (A i)) := hA i hxAi
  -- Relate the two closures that appear.
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ i, A i)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Conclude by the inclusion.
  exact hsubset hx'

theorem P3_bUnion {X ι : Type*} [TopologicalSpace X] {s : Set ι} {A : ι → Set X} (hA : ∀ i ∈ s, Topology.P3 (A i)) : Topology.P3 (⋃ i ∈ s, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨his, hxAi⟩
  have hP3i : Topology.P3 (A i) := hA i his
  have hx' : x ∈ interior (closure (A i)) := hP3i hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ j ∈ s, A j)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    -- show `y` belongs to the big union
    have : y ∈ ⋃ j ∈ s, A j := by
      apply Set.mem_iUnion.2
      exact ⟨i, Set.mem_iUnion.2 ⟨his, hy⟩⟩
    exact this
  exact hsubset hx'

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, Topology.P3 (A i)) : Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Use the hypothesis on the chosen index.
  have hx' : x ∈ interior (closure (A i)) := hA i hxAi
  -- Relate the two interiors that appear.
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ i, A i)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Conclude by the inclusion.
  exact hsubset hx'

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx' : x ∈ interior (closure (interior (A i))) := hA i hxAi
  have hsubset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ i, A i))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hsubset hx'

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  exact Set.empty_subset _

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P3 A) : Topology.P3 (e '' A) := by
  -- unpack the hypothesis and the goal
  dsimp [Topology.P3] at hA ⊢
  intro y hy
  -- write `y` as `e x` with `x ∈ A`
  rcases hy with ⟨x, hxA, rfl⟩
  -- use the hypothesis on `A`
  have hx : x ∈ interior (closure (A : Set X)) := hA hxA
  -- `e x` belongs to the image of this interior
  have h_mem : (e : X → Y) x ∈ e '' interior (closure (A : Set X)) :=
    ⟨x, hx, rfl⟩
  -- this image is open, since `e` is an open map
  have h_open : IsOpen (e '' interior (closure (A : Set X))) :=
    (e.isOpenMap) _ isOpen_interior
  -- and it is contained in the closure of `e '' A`
  have h_subset :
      (e '' interior (closure (A : Set X))) ⊆ closure (e '' A) := by
    intro y hy
    rcases hy with ⟨x', hx', rfl⟩
    have hx'_cl : x' ∈ closure (A : Set X) := interior_subset hx'
    have h_in : (e : X → Y) x' ∈ e '' closure (A : Set X) :=
      ⟨x', hx'_cl, rfl⟩
    have h_eq : e '' closure (A : Set X) = closure (e '' A) := by
      simpa using e.image_closure (s := A)
    simpa [h_eq] using h_in
  -- therefore it is contained in the interior of that closure
  have h_subset' :
      (e '' interior (closure (A : Set X))) ⊆
        interior (closure (e '' A)) :=
    interior_maximal h_subset h_open
  -- conclude for our point
  exact h_subset' h_mem

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} (hB : Topology.P2 B) : Topology.P2 (e.symm '' B) := by
  -- Unfold the definition of `P2`.
  dsimp [Topology.P2] at hB ⊢
  -- Take a point `x` of the set `e.symm '' B`.
  intro x hx
  -- Write it as the image of a point `y ∈ B`.
  rcases hx with ⟨y, hyB, rfl⟩
  -- Apply the hypothesis `hB`.
  have hy : y ∈ interior (closure (interior (B : Set Y))) := hB hyB
  -- Consider the open set
  --   W = e.symm '' interior (closure (interior B)).
  have hW_open :
      IsOpen (e.symm '' interior (closure (interior (B : Set Y)))) :=
    (e.symm.isOpenMap) _ isOpen_interior
  -- The point belongs to `W`.
  have hxW :
      e.symm y ∈ e.symm '' interior (closure (interior (B : Set Y))) :=
    ⟨y, hy, rfl⟩
  -- We claim that `W` is contained in the closure of
  -- `interior (e.symm '' B)`.
  have hW_sub :
      (e.symm '' interior (closure (interior (B : Set Y)))) ⊆
        closure (interior (e.symm '' B)) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    -- `w ∈ interior (closure (interior B))` implies
    -- `w ∈ closure (interior B)`.
    have hw_cl : w ∈ closure (interior (B : Set Y)) :=
      interior_subset hw
    -- Use the behaviour of `closure` under a homeomorphism.
    have h_cl_eq :
        (e.symm '' closure (interior (B : Set Y))) =
          closure (e.symm '' interior (B : Set Y)) := by
      simpa using (e.symm.image_closure (s := interior (B : Set Y)))
    have hz₁ :
        e.symm w ∈ closure (e.symm '' interior (B : Set Y)) := by
      have : e.symm w ∈ e.symm '' closure (interior (B : Set Y)) :=
        ⟨w, hw_cl, rfl⟩
      simpa [h_cl_eq] using this
    -- Show that `e.symm '' interior B ⊆ interior (e.symm '' B)`.
    have h_int_in :
        (e.symm '' interior (B : Set Y)) ⊆ interior (e.symm '' B) := by
      have h_sub :
          (e.symm '' interior (B : Set Y)) ⊆ e.symm '' B := by
        intro u hu
        rcases hu with ⟨w', hw'int, rfl⟩
        exact ⟨w', interior_subset hw'int, rfl⟩
      have h_open' :
          IsOpen (e.symm '' interior (B : Set Y)) :=
        (e.symm.isOpenMap) _ isOpen_interior
      exact interior_maximal h_sub h_open'
    -- Pass to closures.
    have h_cl_mono :
        closure (e.symm '' interior (B : Set Y)) ⊆
          closure (interior (e.symm '' B)) :=
      closure_mono h_int_in
    exact h_cl_mono hz₁
  -- Since `W` is open and contained in the closure, it is contained in its interior.
  have hW_sub_int :
      (e.symm '' interior (closure (interior (B : Set Y)))) ⊆
        interior (closure (interior (e.symm '' B))) :=
    interior_maximal hW_sub hW_open
  -- Conclude for our point.
  exact hW_sub_int hxW

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  classical
  -- `A` is nonempty since it contains `x`, hence it is the whole space.
  have hAuniv : (A : Set X) = (Set.univ : Set X) := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      have hz : z = x := Subsingleton.elim z x
      simpa [hz] using hx
  -- Rewrite the goal using this fact.
  simpa [hAuniv, closure_univ, interior_univ]

theorem P3_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P3 (closure A) := by
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3]
  -- First, prove that `closure A = univ`.
  have h_closure_univ : (closure (A : Set X)) = (Set.univ : Set X) := by
    -- From the density hypothesis we have `closure (interior A) = univ`.
    have h1 : closure (interior (A : Set X)) = (Set.univ : Set X) := by
      simpa using h.closure_eq
    -- And clearly `closure (interior A) ⊆ closure A`.
    have h2 : closure (interior (A : Set X)) ⊆ closure A :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    -- Hence `univ ⊆ closure A`.
    have h3 : (Set.univ : Set X) ⊆ closure A := by
      simpa [h1] using h2
    -- Combine the two inclusions to get equality.
    exact subset_antisymm (Set.subset_univ _) h3
  -- Now establish the required inclusion.
  intro x hx
  -- After rewriting, the goal is trivial.
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [closure_closure, h_closure_univ, interior_univ] using this

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  -- Unfold the definition of `P2` in the hypothesis and in the goal.
  dsimp [Topology.P2] at hA ⊢
  -- Take a point `x` in `A \ B`.
  intro x hx
  rcases hx with ⟨hxA, hx_notB⟩
  -- Apply the hypothesis on `A`.
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  /-  Work with the open set
        V = interior (closure (interior A)) \ B. -/
  have hV_open : IsOpen (interior (closure (interior A)) \ B) := by
    --  `V` is the intersection of two open sets.
    have h1 : IsOpen (interior (closure (interior A))) := isOpen_interior
    have h2 : IsOpen (Bᶜ) := hB.isOpen_compl
    simpa [Set.diff_eq] using h1.inter h2
  have hxV : x ∈ interior (closure (interior A)) \ B :=
    ⟨hx_int, hx_notB⟩
  -- Main inclusion: `V ⊆ closure (interior (A \ B))`.
  have hV_sub :
      (interior (closure (interior A)) \ B : Set X) ⊆
        closure (interior (A \ B)) := by
    intro y hy
    rcases hy with ⟨hy_int, hy_notB⟩
    -- From `hy_int` we deduce that `y` is in the closure of `interior A`.
    have hy_cl : y ∈ closure (interior A) := interior_subset hy_int
    -- We now prove that `y` is in the closure of `interior (A \ B)`.
    have : y ∈ closure (interior (A \ B)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro W hW_open hyW
      -- Shrink the neighbourhood to avoid `B`.
      have hW_diff_open : IsOpen (W \ B) := by
        have h_open_compl : IsOpen (Bᶜ) := hB.isOpen_compl
        simpa [Set.diff_eq] using hW_open.inter h_open_compl
      have hyWdiff : y ∈ W \ B := by
        exact ⟨hyW, hy_notB⟩
      -- Since `y` is in the closure of `interior A`, this set meets `interior A`.
      have h_nonempty :
          ((W \ B) ∩ interior A).Nonempty := by
        have h_prop := (mem_closure_iff).1 hy_cl
        exact h_prop (W \ B) hW_diff_open hyWdiff
      -- Pick a point `z` in the intersection.
      rcases h_nonempty with ⟨z, hz⟩
      rcases hz with ⟨hzWdiff, hz_intA⟩
      rcases hzWdiff with ⟨hzW, hz_notB⟩
      -- `z` belongs to `interior A \ B`.
      have hz_intA_notB : z ∈ interior A \ B := ⟨hz_intA, hz_notB⟩
      -- Show that `interior A \ B ⊆ interior (A \ B)`.
      have h_int_subset :
          (interior A \ B : Set X) ⊆ interior (A \ B) := by
        -- `interior A \ B` is open and contained in `A \ B`.
        have h_open_int_diff : IsOpen (interior A \ B) := by
          have h_open_compl : IsOpen (Bᶜ) := hB.isOpen_compl
          simpa [Set.diff_eq] using (isOpen_interior).inter h_open_compl
        have h_sub : (interior A \ B : Set X) ⊆ A \ B := by
          intro t ht
          rcases ht with ⟨ht_intA, ht_notB⟩
          exact ⟨interior_subset ht_intA, ht_notB⟩
        exact interior_maximal h_sub h_open_int_diff
      -- Hence `z ∈ interior (A \ B)`.
      have hz_int_diff : z ∈ interior (A \ B) :=
        h_int_subset hz_intA_notB
      -- Provide the required witness in `W ∩ interior (A \ B)`.
      exact ⟨z, ⟨hzW, hz_int_diff⟩⟩
    exact this
  -- Since `V` is open and contained in the closure, it is contained in its interior.
  have hV_sub_int :
      (interior (closure (interior A)) \ B : Set X) ⊆
        interior (closure (interior (A \ B))) :=
    interior_maximal hV_sub hV_open
  -- Conclude for the original point `x`.
  exact hV_sub_int hxV

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (closure A) := by
  -- Unfold the definition of `P1` in the hypothesis and the goal.
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)`.
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    -- `closure_mono` applied to `hA`, and then rewrite with `closure_closure`.
    have h := closure_mono (hA : (A : Set X) ⊆ closure (interior A))
    simpa [closure_closure] using h
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    -- first `interior A ⊆ interior (closure A)`
    have h' : interior (A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    -- then take closures
    exact closure_mono h'
  -- Chain the inclusions to send `x` to the desired set.
  exact h₂ (h₁ hx)

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P1 A) : Topology.P1 (e '' A) := by
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at hA ⊢
  -- Take a point of the image.
  intro y hy
  -- Write it as `e x` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Apply the hypothesis on `A`.
  have hx : x ∈ closure (interior (A : Set X)) := hA hxA
  -- Transport this membership with `e`.
  have h_mem : (e : X → Y) x ∈ e '' closure (interior (A : Set X)) :=
    ⟨x, hx, rfl⟩
  -- Turn it into a membership in `closure (e '' interior A)`.
  have hx_cl : (e : X → Y) x ∈ closure (e '' interior (A : Set X)) := by
    have h_eq :
        e '' closure (interior (A : Set X)) =
          closure (e '' interior (A : Set X)) := by
      simpa using e.image_closure (s := interior (A : Set X))
    simpa [h_eq] using h_mem
  -- We now relate the two closures that appear.
  have h_closure_mono :
      closure (e '' interior (A : Set X)) ⊆
        closure (interior (e '' A)) := by
    -- It suffices to show the inclusion without the closures.
    apply closure_mono
    -- Show that `e '' interior A ⊆ interior (e '' A)`.
    have h_sub :
        (e '' interior (A : Set X)) ⊆ interior (e '' A) := by
      -- The left set is open (as `e` is an open map) and contained in `e '' A`.
      have h_open :
          IsOpen (e '' interior (A : Set X)) :=
        (e.isOpenMap) _ isOpen_interior
      apply interior_maximal
      · intro z hz
        rcases hz with ⟨x', hx'int, rfl⟩
        exact ⟨x', interior_subset hx'int, rfl⟩
      · exact h_open
    exact h_sub
  -- Conclude for our point.
  exact h_closure_mono hx_cl

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P2 A) : Topology.P2 (e '' A) := by
  -- Unfold the definition of `P2` in the hypothesis and in the goal.
  dsimp [Topology.P2] at hA ⊢
  -- Take a point in the image.
  intro y hy
  -- Write it as `e x` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Use the hypothesis `hA`.
  have hx : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  -- Consider the open set  `W = e '' interior (closure (interior A))`.
  have hW_open :
      IsOpen (e '' interior (closure (interior (A : Set X)))) :=
    (e.isOpenMap) _ isOpen_interior
  -- Our point belongs to `W`.
  have hxW :
      (e : X → Y) x ∈ e '' interior (closure (interior (A : Set X))) :=
    ⟨x, hx, rfl⟩
  -- We claim that `W ⊆ closure (interior (e '' A))`.
  have hW_sub :
      (e '' interior (closure (interior (A : Set X)))) ⊆
        closure (interior (e '' (A : Set X))) := by
    intro z hz
    rcases hz with ⟨x', hx', rfl⟩
    -- From `hx'` we get `x' ∈ closure (interior A)`.
    have hx'_cl : x' ∈ closure (interior (A : Set X)) :=
      interior_subset hx'
    -- Transport this membership with `e`.
    have hmem :
        (e : X → Y) x' ∈ e '' closure (interior (A : Set X)) :=
      ⟨x', hx'_cl, rfl⟩
    -- Rewrite using `e.image_closure`.
    have h_eq :
        e '' closure (interior (A : Set X)) =
          closure (e '' interior (A : Set X)) := by
      simpa using e.image_closure (s := interior (A : Set X))
    have hz1 :
        (e : X → Y) x' ∈ closure (e '' interior (A : Set X)) := by
      simpa [h_eq] using hmem
    -- Relate the two closures.
    have h_cl_sub :
        closure (e '' interior (A : Set X)) ⊆
          closure (interior (e '' (A : Set X))) := by
      -- First show the inclusion without closures.
      have h_sub :
          (e '' interior (A : Set X)) ⊆ interior (e '' (A : Set X)) := by
        -- The left-hand set is open and contained in `e '' A`.
        have h_open' :
            IsOpen (e '' interior (A : Set X)) :=
          (e.isOpenMap) _ isOpen_interior
        have h_incl :
            (e '' interior (A : Set X)) ⊆ e '' (A : Set X) := by
          intro y hy
          rcases hy with ⟨x0, hx0, rfl⟩
          exact ⟨x0, interior_subset hx0, rfl⟩
        exact interior_maximal h_incl h_open'
      exact closure_mono h_sub
    exact h_cl_sub hz1
  -- Since `W` is open and contained in the closure, it is contained in its interior.
  have hW_sub_int :
      (e '' interior (closure (interior (A : Set X)))) ⊆
        interior (closure (interior (e '' (A : Set X)))) :=
    interior_maximal hW_sub hW_open
  -- Conclude for our point.
  exact hW_sub_int hxW

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (A ∪ B ∪ C) := by
  have hAB : Topology.P3 (A ∪ B) := P3_union (X := X) hA hB
  simpa [Set.union_assoc] using
    (P3_union (X := X) (A := A ∪ B) (B := C) hAB hC)

theorem exists_P1_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, A ⊆ U ∧ Topology.P1 U := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · intro _ _
    trivial
  · dsimp [Topology.P1]
    simpa [interior_univ, closure_univ]

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) : Topology.P3 (closure A) := by
  dsimp [Topology.P3]
  intro x hx
  -- `A` is dense, hence its closure is the whole space.
  have hclosure : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Rewrite `hx` using this information.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [hclosure] using hx
  -- Conclude, as the interior of `univ` is `univ`.
  simpa [closure_closure, hclosure, interior_univ] using hx_univ

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P3_of_compact_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsCompact A) (h_dense : Dense A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hclosure : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using h_dense.closure_eq
  simpa [hclosure, interior_univ] using (Set.mem_univ x)

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  exact
    ⟨fun _ => P3_of_open (A := A) hA,
     fun _ => P1_of_open (X := X) (A := A) hA⟩

theorem exists_P3_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, U ⊆ A ∧ Topology.P3 U := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  simpa using (P3_empty (X := X))

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  simpa using
    (P1_iff_P3_of_open (X := X) (A := A) hA).trans
      ((P2_iff_P3_of_open (A := A) hA).symm)

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 ((Set.prod A B).prod C) := by
  -- First, establish `P1` for `A × B`.
  have hAB : Topology.P1 (Set.prod A B) :=
    P1_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Then use it together with `hC` to get `P1` for `(A × B) × C`.
  have hABC : Topology.P1 ((Set.prod A B).prod C) :=
    P1_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A)) := by
  -- `interior A` satisfies `P1`.
  have h : Topology.P1 (interior A) := P1_interior (X := X) (A := A)
  -- Hence its closure also satisfies `P1`.
  simpa using (P1_closure (X := X) (A := interior A) h)

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∪ B ∪ C) := by
  have hAB : Topology.P2 (A ∪ B) := P2_union (X := X) (A := A) (B := B) hA hB
  simpa [Set.union_assoc] using
    (P2_union (X := X) (A := A ∪ B) (B := C) hAB hC)

theorem exists_P2_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, U ⊆ A ∧ Topology.P2 U := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  simpa using (P2_empty (X := X))

theorem P1_map_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} : Topology.P1 (e '' A) ↔ Topology.P1 A := by
  constructor
  · intro h_image
    -- First, transport `P1` back with the inverse homeomorphism.
    have h_preimage : Topology.P1 (e.symm '' (e '' A)) :=
      (P1_image_homeomorph (e := e.symm) (A := e '' A)) h_image
    -- Show that this set is just `A`.
    have h_eq : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨z, hzA, rfl⟩
        -- Now `hxy : e.symm (e z) = x`.
        have hzx : z = x := by
          simpa [hxy] using (e.symm_apply_apply z).symm
        simpa [hzx] using hzA
      · intro hxA
        refine ⟨e x, ?_, ?_⟩
        · exact ⟨x, hxA, rfl⟩
        · simpa using e.symm_apply_apply x
    simpa [h_eq] using h_preimage
  · intro hA
    exact P1_image_homeomorph (e := e) hA

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 ((Set.prod A B).prod C) := by
  -- First, obtain `P2` for `A × B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    P2_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Then combine this with `C` to get `P2` for `(A × B) × C`.
  have hABC : Topology.P2 ((Set.prod A B).prod C) :=
    P2_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem exists_closed_subset_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ F : Set X, IsClosed F ∧ F ⊆ A ∧ Topology.P2 F := by
  refine ⟨(∅ : Set X), isClosed_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · simpa using (P2_empty (X := X))

theorem P1_bUnion {X ι : Type*} [TopologicalSpace X] {s : Set ι} {A : ι → Set X} (hA : ∀ i ∈ s, Topology.P1 (A i)) : Topology.P1 (⋃ i ∈ s, A i) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨his, hxAi⟩
  have hP1i : Topology.P1 (A i) := hA i his
  have hx' : x ∈ closure (interior (A i)) := hP1i hxAi
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j ∈ s, A j)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    -- Show that `y` belongs to the big union.
    have : y ∈ ⋃ j ∈ s, A j := by
      apply Set.mem_iUnion.2
      exact ⟨i, Set.mem_iUnion.2 ⟨his, hy⟩⟩
    exact this
  exact hsubset hx'

theorem P1_union_compl {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P1_univ (X := X))

theorem exists_open_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ Topology.P1 U := by
  rcases exists_open_subset_P2 (X := X) (A := A) with ⟨U, hUopen, hAU, hP2U⟩
  exact ⟨U, hUopen, hAU, P2_implies_P1 (A := U) hP2U⟩

theorem P1_inter_interior {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (interior A ∩ interior B) := by
  -- `interior A` and `interior B` are open, hence so is their intersection.
  have h_open : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  -- Any open set satisfies `P1`.
  exact P1_of_open (X := X) (A := interior A ∩ interior B) h_open

theorem P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Dense A) (hAB : A ⊆ B) : Topology.P3 B := by
  dsimp [Topology.P3]
  intro x hxB
  -- Show that `closure B = univ`.
  have h_closureB : closure (B : Set X) = (Set.univ : Set X) := by
    -- `closure A = univ` since `A` is dense.
    have h_closureA : closure (A : Set X) = (Set.univ : Set X) := by
      simpa using hA.closure_eq
    -- `closure A ⊆ closure B` because `A ⊆ B`.
    have h_subset : closure (A : Set X) ⊆ closure B := closure_mono hAB
    -- Hence `univ ⊆ closure B`.
    have h_subset' : (Set.univ : Set X) ⊆ closure B := by
      simpa [h_closureA] using h_subset
    -- Combine the inclusions to get equality.
    exact subset_antisymm (Set.subset_univ _) h_subset'
  -- With `closure B = univ`, the interior is also `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closureB, interior_univ] using this

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  have hP2 : Topology.P2 A := (P2_iff_P3_of_closed (X := X) (A := A) hA).2 hP3
  exact P2_implies_P1 (A := A) hP2

theorem P1_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : Topology.P1 (A.prod B)) : Topology.P1 (B.prod A) := by
  -- Transport the property through the coordinate swap homeomorphism.
  have h_image :
      Topology.P1
        ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) := by
    simpa using
      (P1_image_homeomorph
          (e := Homeomorph.prodComm (X := X) (Y := Y))
          (A := A.prod B)) h
  -- Identify this image with `B × A`.
  have h_eq :
      ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) =
        B.prod A := by
    ext p
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      rcases hxy with ⟨hxA, hyB⟩
      exact And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, rfl⟩
      exact And.intro hxA hyB
  -- Conclude using this identification.
  simpa [h_eq] using h_image

theorem exists_open_P1_dense {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P1 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact dense_univ
  · simpa using (P1_univ (X := X))

theorem P1_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : IsClosed B) : Topology.P1 (A \ B) := by
  -- Unfold the definition of `P1` in the hypothesis and in the goal.
  dsimp [Topology.P1] at hA ⊢
  -- Take an arbitrary point of `A \ B`.
  intro x hx
  rcases hx with ⟨hxA, hx_notB⟩
  -- Use the hypothesis `hA`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := hA hxA
  -- Neighbourhood characterization of the closure.
  have h_prop := (mem_closure_iff).1 hx_cl
  -- We prove that every open neighbourhood of `x` meets
  -- `interior (A \ B)`, hence `x` is in its closure.
  apply (mem_closure_iff).2
  intro W hW_open hxW
  /- Consider the open set `V = W \ B`, which still contains `x`
     and avoids `B`. -/
  have hV_open : IsOpen (W \ B) := by
    have hB_open : IsOpen (Bᶜ) := hB.isOpen_compl
    simpa [Set.diff_eq] using hW_open.inter hB_open
  have hxV : x ∈ W \ B := by
    exact And.intro hxW hx_notB
  -- Apply `h_prop` to `V` to obtain a point of `interior A` in `V`.
  have h_nonempty : ((W \ B) ∩ interior (A : Set X)).Nonempty :=
    h_prop (W \ B) hV_open hxV
  rcases h_nonempty with ⟨y, hyV, hy_intA⟩
  have hyW    : y ∈ W := hyV.1
  have hy_notB : y ∉ B := hyV.2
  -- Show that `y ∈ interior (A \ B)`.
  have hy_int_diff : y ∈ interior (A \ B) := by
    -- The set `S = interior A \ B` is open and contained in `A \ B`,
    -- hence contained in `interior (A \ B)`.
    have hS_open : IsOpen (interior (A : Set X) \ B) := by
      have hB_open : IsOpen (Bᶜ) := hB.isOpen_compl
      simpa [Set.diff_eq] using isOpen_interior.inter hB_open
    have hS_subset :
        (interior (A : Set X) \ B : Set X) ⊆ interior (A \ B) :=
      interior_maximal
        (by
          intro z hz
          rcases hz with ⟨hz_intA, hz_notB⟩
          exact And.intro (interior_subset hz_intA) hz_notB)
        hS_open
    have : y ∈ interior (A : Set X) \ B := And.intro hy_intA hy_notB
    exact hS_subset this
  -- Provide the required witness in `W ∩ interior (A \ B)`.
  exact ⟨y, And.intro hyW hy_int_diff⟩

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  classical
  -- Either `A` is empty or it coincides with `univ`
  by_cases hAempty : (A : Set X) = ∅
  · -- The empty case is impossible since `x ∈ A`
    have : (x ∈ (∅ : Set X)) := by
      simpa [hAempty] using hx
    cases this
  · -- Hence `A = univ`
    have hAuniv : (A : Set X) = (Set.univ : Set X) := by
      ext z
      constructor
      · intro _; trivial
      · intro _
        have hz : z = x := Subsingleton.elim _ _
        simpa [hz] using hx
    -- The required membership is now trivial
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hAuniv, interior_univ, closure_univ] using this

theorem exists_dense_P1_subset {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), dense_univ, ?_⟩
  simpa using (P1_univ (X := X))

theorem P2_Union_closed {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (h : ∀ i, IsClosed (A i)) (hP : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  simpa using (P2_iUnion (X := X) (A := A) hP)

theorem P2_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hAc : IsClosed Aᶜ) : Topology.P2 A := by
  -- `A` is open since its complement is closed.
  have hA_open : IsOpen (A : Set X) := by
    simpa using hAc.isOpen_compl
  -- Apply the lemma giving `P2` for open sets.
  exact P2_of_open (A := A) hA_open

theorem exists_P3_between {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hA : Topology.P3 A) (hB : Topology.P3 B) : ∃ U, A ⊆ U ∧ U ⊆ B ∧ Topology.P3 U := by
  refine ⟨A ∪ interior B, ?_, ?_, ?_⟩
  · intro x hxA
    exact Or.inl hxA
  · intro x hxU
    cases hxU with
    | inl hxA => exact hAB hxA
    | inr hxIntB =>
        have hsubset : (interior B : Set X) ⊆ B := interior_subset
        exact hsubset hxIntB
  ·
    have hP3_intB : Topology.P3 (interior B) := by
      simpa using (P3_interior (X := X) (A := B))
    have hP3_union : Topology.P3 (A ∪ interior B) :=
      P3_union (X := X) (A := A) (B := interior B) hA hP3_intB
    simpa using hP3_union

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) : Topology.P1 (((A.prod B).prod C).prod D) := by
  -- First, obtain `P1` for `(A × B) × C`.
  have hABC : Topology.P1 ((A.prod B).prod C) :=
    P1_prod_three (X := W) (Y := X) (Z := Y) (A := A) (B := B) (C := C) hA hB hC
  -- Then combine this set with `D`.
  have hABCD : Topology.P1 (((A.prod B).prod C).prod D) :=
    P1_prod
      (X := (W × X) × Y)
      (Y := Z)
      (A := (A.prod B).prod C)
      (B := D)
      hABC
      hD
  simpa using hABCD

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A := by
  have hP2 : Topology.P2 (A : Set X) := P2_subsingleton (X := X) (A := A)
  exact P2_implies_P1 (A := A) hP2

theorem exists_dense_superset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : ∃ U : Set X, A ⊆ U ∧ IsOpen U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), ?_, ?_, ?_⟩
  · intro _ _; trivial
  · exact isOpen_univ
  · simpa using (P3_univ (X := X))

theorem P2_countable_iUnion {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (hA : ∀ n, Topology.P2 (A n)) : Topology.P2 (⋃ n, A n) := by
  simpa using (P2_iUnion (X := X) (A := A) hA)

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) : Topology.P3 (((A.prod B).prod C).prod D) := by
  -- First, obtain `P3` for `A × B`.
  have hAB : Topology.P3 (A.prod B) :=
    P3_prod (X := W) (Y := X) (A := A) (B := B) hA hB
  -- Then, obtain `P3` for `(A × B) × C`.
  have hABC : Topology.P3 ((A.prod B).prod C) :=
    P3_prod
      (X := W × X) (Y := Y)
      (A := (A.prod B)) (B := C) hAB hC
  -- Finally, combine this set with `D`.
  have hABCD : Topology.P3 (((A.prod B).prod C).prod D) :=
    P3_prod
      (X := (W × X) × Y) (Y := Z)
      (A := ((A.prod B).prod C)) (B := D) hABC hD
  simpa using hABCD

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (closure A ∪ closure B) := by
  -- First, upgrade the hypotheses to the closures.
  have hA_cl : Topology.P1 (closure A) := P1_closure (X := X) (A := A) hA
  have hB_cl : Topology.P1 (closure B) := P1_closure (X := X) (A := B) hB
  -- Then apply the union lemma.
  have h_union : Topology.P1 (closure A ∪ closure B) :=
    P1_union (A := closure A) (B := closure B) hA_cl hB_cl
  simpa using h_union

theorem exists_P3_dense_subset {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Dense A ∧ Topology.P3 A := by
  refine ⟨(Set.univ : Set X), dense_univ, ?_⟩
  simpa using (P3_univ (X := X))

theorem P3_union_sInter {X : Type*} [TopologicalSpace X] {A : Set (Set X)} (hA : ∀ B ∈ A, Topology.P3 B) : Topology.P3 (Set.sUnion A ∪ Set.sInter A) := by
  classical
  rcases (Set.eq_empty_or_nonempty (A : Set (Set X))) with hAempty | hAnonempty
  · -- Case `A = ∅`
    -- Then `⋃₀ A = ∅` and `⋂₀ A = univ`, so the union is `univ`,
    -- which satisfies `P3`.
    have : Topology.P3 (Set.univ : Set X) := P3_univ (X := X)
    simpa [hAempty] using this
  · -- Case `A` is non‐empty
    rcases hAnonempty with ⟨B₀, hB₀⟩
    -- `⋂₀ A ⊆ ⋃₀ A`
    have hsubset : (Set.sInter A : Set X) ⊆ Set.sUnion A := by
      intro x hx
      have hxB₀ : x ∈ B₀ := (Set.mem_sInter.1 hx) _ hB₀
      exact Set.mem_sUnion.2 ⟨B₀, hB₀, hxB₀⟩
    -- Hence the union is just `⋃₀ A`.
    have h_union_eq :
        (Set.sUnion A ∪ Set.sInter A : Set X) = Set.sUnion A :=
      Set.union_eq_self_of_subset_right hsubset
    -- Apply `P3` to `⋃₀ A`.
    have hP3 : Topology.P3 (Set.sUnion A) :=
      P3_sUnion (X := X) (𝒜 := A) hA
    simpa [h_union_eq] using hP3

theorem P2_iterate {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h0 : Topology.P2 (A 0)) (hstep : ∀ n, Topology.P2 (A n) → Topology.P2 (A (n+1))) : ∀ n, Topology.P2 (A n) := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      exact hstep n ih

theorem P1_eq_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hBA : B ⊆ closure (interior A)) : Topology.P1 A → Topology.P1 B := by
  intro _hPA
  dsimp [Topology.P1] at _hPA ⊢
  intro x hxB
  -- From `hBA` we have that `x` lies in `closure (interior A)`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hBA hxB
  -- Since `A ⊆ B`, we get `interior A ⊆ interior B`.
  have h_interior : (interior (A : Set X)) ⊆ interior B :=
    interior_mono hAB
  -- Taking closures yields the desired inclusion.
  have h_closure : closure (interior (A : Set X)) ⊆ closure (interior B) :=
    closure_mono h_interior
  -- Conclude that `x ∈ closure (interior B)`.
  exact h_closure hx_clA

theorem P1_prod_swap_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P1 (A.prod B) ↔ Topology.P1 (B.prod A)) := by
  constructor
  · intro h
    exact P1_prod_swap (X := X) (Y := Y) (A := A) (B := B) h
  · intro h
    simpa using
      (P1_prod_swap (X := Y) (Y := X) (A := B) (B := A) h)

theorem P1_of_dense_set {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : Topology.P1 (closure A) := by
  -- `A` is dense, hence its closure is the whole space.
  have hclosure : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using hA.closure_eq
  -- Rewrite and conclude using `P1_univ`.
  simpa [hclosure] using (P1_univ (X := X))

theorem P2_image_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (h_open : IsOpenMap f) {A : Set X} (hA : Topology.P2 A) : Topology.P2 (f '' A) := by
  -- Unfold the definition of `P2` in the hypothesis and in the goal.
  dsimp [Topology.P2] at hA ⊢
  -- Take a point in the image.
  intro y hy
  -- Write it as `f x` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Use the hypothesis on `A`.
  have hx : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  -- Define the auxiliary open set
  --   W = f '' interior (closure (interior A)).
  set W : Set Y := f '' interior (closure (interior (A : Set X))) with hWdef
  -- This set is open, as `f` is an open map.
  have hW_open : IsOpen W := by
    have : IsOpen (interior (closure (interior (A : Set X)))) :=
      isOpen_interior
    simpa [hWdef] using h_open _ this
  -- The point `f x` belongs to `W`.
  have hxW : f x ∈ W := by
    refine ⟨x, hx, rfl⟩
  -- We will show that `W ⊆ closure (interior (f '' A))`.
  have hW_sub_cl :
      W ⊆ closure (interior (f '' (A : Set X))) := by
    intro z hz
    -- Write `z = f x'` with `x' ∈ interior (closure (interior A))`.
    rcases (show ∃ x', x' ∈ interior (closure (interior (A : Set X))) ∧ f x' = z from by
        rcases hz with ⟨x', hx', rfl⟩
        exact ⟨x', hx', rfl⟩) with ⟨x', hx', rfl⟩
    -- From `hx'` we get `x' ∈ closure (interior A)`.
    have hx'cl : x' ∈ closure (interior (A : Set X)) :=
      interior_subset hx'
    -- We prove `f x' ∈ closure (interior (f '' A))`
    -- using the neighborhood characterization of the closure.
    have : f x' ∈ closure (interior (f '' (A : Set X))) := by
      -- Reformulate with `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro V hV_open hfxV
      -- Pull back the neighborhood `V` through `f`.
      have hU_open : IsOpen (f ⁻¹' V) := hV_open.preimage hf
      have hx'U : x' ∈ f ⁻¹' V := hfxV
      -- Since `x'` is in the closure of `interior A`, the intersection
      --   (f ⁻¹ V) ∩ interior A
      -- is non‐empty.
      have h_nonempty :
          ((f ⁻¹' V) ∩ interior (A : Set X)).Nonempty := by
        have h_cl := (mem_closure_iff).1 hx'cl
        exact h_cl _ hU_open hx'U
      rcases h_nonempty with ⟨w, hwU, hw_intA⟩
      -- The point `f w` is in `V` and also in the image of `interior A`.
      have hfwV : f w ∈ V := hwU
      -- `f w` lies in `f '' interior A`, which is open.
      have h_open_im : IsOpen (f '' interior (A : Set X)) :=
        h_open _ isOpen_interior
      -- Show that `f '' interior A ⊆ interior (f '' A)`.
      have h_im_sub_int :
          (f '' interior (A : Set X)) ⊆ interior (f '' (A : Set X)) :=
        interior_maximal
          (by
            intro t ht
            rcases ht with ⟨u, hu_intA, rfl⟩
            exact ⟨u, interior_subset hu_intA, rfl⟩)
          h_open_im
      -- Hence `f w ∈ interior (f '' A)`.
      have hfw_int : f w ∈ interior (f '' (A : Set X)) :=
        h_im_sub_int ⟨w, hw_intA, rfl⟩
      -- Provide the required witness in `V ∩ interior (f '' A)`.
      exact ⟨f w, hfwV, hfw_int⟩
    simpa using this
  -- Since `W` is open and contained in the closure, it is contained
  -- in the interior of that closure.
  have hW_sub_int :
      W ⊆ interior (closure (interior (f '' (A : Set X)))) :=
    interior_maximal hW_sub_cl hW_open
  -- Apply this inclusion to the point `f x`.
  exact hW_sub_int (by
    simpa [hWdef] using hxW)

theorem P3_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (closure (A ∪ Set.univ)) := by
  simpa [Set.union_univ, closure_univ] using (P3_univ (X := X))

theorem P3_iterate {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h0 : Topology.P3 (A 0)) (hstep : ∀ n, Topology.P3 (A n) → Topology.P3 (A (n+1))) : ∀ n, Topology.P3 (A n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => exact hstep n ih

theorem P3_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P3 (A.prod B)) ↔ Topology.P3 (B.prod A) := by
  constructor
  · intro h
    -- transport `P3` through the coordinate‐swap homeomorphism
    have h_image :
        Topology.P3
          ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) := by
      simpa using
        (P3_image_homeomorph
            (e := Homeomorph.prodComm (X := X) (Y := Y))
            (A := A.prod B)) h
    -- identify this image with `B × A`
    have h_eq :
        ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) =
          B.prod A := by
      ext p
      constructor
      · rintro ⟨⟨x, y⟩, hxy, rfl⟩
        rcases hxy with ⟨hxA, hyB⟩
        exact And.intro hyB hxA
      · intro hp
        rcases p with ⟨y, x⟩
        rcases hp with ⟨hyB, hxA⟩
        refine ⟨(x, y), ?_, rfl⟩
        exact And.intro hxA hyB
    simpa [h_eq] using h_image
  · intro h
    -- transport in the opposite direction
    have h_image :
        Topology.P3
          ((fun p : Y × X => Prod.swap p) '' (B.prod A) : Set (X × Y)) := by
      simpa using
        (P3_image_homeomorph
            (e := Homeomorph.prodComm (X := Y) (Y := X))
            (A := B.prod A)) h
    -- identify this image with `A × B`
    have h_eq :
        ((fun p : Y × X => Prod.swap p) '' (B.prod A) : Set (X × Y)) =
          A.prod B := by
      ext p
      constructor
      · rintro ⟨⟨y, x⟩, hxy, rfl⟩
        rcases hxy with ⟨hyB, hxA⟩
        exact And.intro hxA hyB
      · intro hp
        rcases p with ⟨x, y⟩
        rcases hp with ⟨hxA, hyB⟩
        refine ⟨(y, x), ?_, rfl⟩
        exact And.intro hyB hxA
    simpa [h_eq] using h_image

theorem P3_preimage_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (h_open : IsOpenMap f) {B : Set Y} (hB : Topology.P3 B) : Topology.P3 (f ⁻¹' B) := by
  -- Unpack the assumption `P3 B`.
  dsimp [Topology.P3] at hB
  -- Unfold the goal.
  dsimp [Topology.P3]
  intro x hx
  -- From `hx` we know `f x ∈ B`.
  have hfxB : f x ∈ (B : Set Y) := hx
  -- Hence `f x` belongs to the interior of `closure B`.
  have hfx_int : f x ∈ interior (closure (B : Set Y)) := hB hfxB
  -- Define the open set `S = f ⁻¹' interior (closure B)`.
  have hS_open :
      IsOpen (f ⁻¹' interior (closure (B : Set Y))) :=
    (isOpen_interior.preimage hf)
  have hxS : x ∈ f ⁻¹' interior (closure (B : Set Y)) := hfx_int
  -- We show that `S ⊆ closure (f ⁻¹' B)`.
  have hS_sub :
      (f ⁻¹' interior (closure (B : Set Y))) ⊆
        closure (f ⁻¹' (B : Set Y)) := by
    intro z hz
    -- First, note that `f z ∈ closure B`.
    have h_clB : f z ∈ closure (B : Set Y) := by
      have : interior (closure (B : Set Y)) ⊆ closure B := interior_subset
      exact this hz
    -- Prove that `z` is in the closure of `f ⁻¹' B`.
    have hz_cl : z ∈ closure (f ⁻¹' (B : Set Y)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro V hVopen hzV
      -- The image `f '' V` is open and contains `f z`.
      have h_fV_open : IsOpen (f '' V) := h_open _ hVopen
      have hfzV : f z ∈ f '' V := ⟨z, hzV, rfl⟩
      -- Hence it meets `B`.
      have h_nonempty :
          ((f '' V) ∩ (B : Set Y)).Nonempty :=
        (mem_closure_iff).1 h_clB _ h_fV_open hfzV
      rcases h_nonempty with ⟨y, ⟨⟨w, hwV, rfl⟩, hyB⟩⟩
      -- `w` is in `V ∩ f ⁻¹' B`.
      exact ⟨w, by
        refine ⟨hwV, ?_⟩
        simpa using hyB⟩
    exact hz_cl
  -- By maximality of the interior, we obtain the desired inclusion.
  have hS_sub_int :
      (f ⁻¹' interior (closure (B : Set Y))) ⊆
        interior (closure (f ⁻¹' (B : Set Y))) :=
    interior_maximal hS_sub hS_open
  -- Conclude for the original point `x`.
  exact hS_sub_int hxS

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P3 A → Topology.P3 (A.prod (Set.univ : Set Y)) := by
  intro hA
  have hUniv : Topology.P3 (Set.univ : Set Y) := P3_univ (X := Y)
  simpa using
    (P3_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem exists_P1_between {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hA : Topology.P1 A) (hB : Topology.P1 B) : ∃ U, A ⊆ U ∧ U ⊆ B ∧ Topology.P1 U := by
  refine ⟨A ∪ interior B, ?_, ?_, ?_⟩
  · intro x hxA
    exact Or.inl hxA
  · intro x hxU
    cases hxU with
    | inl hxA  => exact hAB hxA
    | inr hxIB => exact interior_subset hxIB
  ·
    have hIntB : Topology.P1 (interior B) := P1_interior (A := B)
    have hUnion : Topology.P1 (A ∪ interior B) :=
      P1_union (A := A) (B := interior B) hA hIntB
    simpa using hUnion

theorem P2_preimage_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (h_open : IsOpenMap f) {B : Set Y} (hB : Topology.P2 B) : Topology.P2 (f ⁻¹' B) := by
  -- Unfold `P2` in the hypothesis and in the goal.
  dsimp [Topology.P2] at hB ⊢
  -- Take a point of the preimage.
  intro x hx
  -- Reformulate this point on the image side.
  have hfxB : f x ∈ (B : Set Y) := hx
  -- Apply the hypothesis `hB`.
  have hfx_int :
      f x ∈ interior (closure (interior (B : Set Y))) := hB hfxB
  /-  Consider the open set
        S = f ⁻¹' interior (closure (interior B)). -/
  set S : Set X := f ⁻¹' interior (closure (interior (B : Set Y))) with hSdef
  have hS_open : IsOpen S := by
    have : IsOpen (interior (closure (interior (B : Set Y)))) :=
      isOpen_interior
    simpa [hSdef] using this.preimage hf
  -- `x` belongs to `S`.
  have hxS : x ∈ S := by
    simpa [hSdef] using hfx_int
  -- Main inclusion:  `S ⊆ closure (interior (f ⁻¹' B))`.
  have hS_sub :
      S ⊆ closure (interior (f ⁻¹' (B : Set Y))) := by
    intro z hzS
    -- First, note that `f z ∈ closure (interior B)`.
    have hz_closure : f z ∈ closure (interior (B : Set Y)) := by
      have : f z ∈ interior (closure (interior (B : Set Y))) := by
        simpa [hSdef] using hzS
      exact interior_subset this
    -- We prove that `z` is in the desired closure.
    have : z ∈ closure (interior (f ⁻¹' (B : Set Y))) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro V hVopen hzV
      -- The image `f '' V` is open and contains `f z`.
      have hVimage_open : IsOpen (f '' V) := h_open _ hVopen
      have hfzV : f z ∈ f '' V := ⟨z, hzV, rfl⟩
      -- Since `f z` is in the closure of `interior B`,
      -- the intersection `(f '' V) ∩ interior B` is non-empty.
      have h_nonempty :
          ((f '' V) ∩ interior (B : Set Y)).Nonempty := by
        have hh := (mem_closure_iff).1 hz_closure
        exact hh _ hVimage_open hfzV
      rcases h_nonempty with ⟨y, ⟨⟨w, hwV, rfl⟩, hy_intB⟩⟩
      -- `w ∈ V` and `f w ∈ interior B`.
      -- Show that `w ∈ interior (f ⁻¹' B)`.
      have hw_int_pre : w ∈ interior (f ⁻¹' (B : Set Y)) := by
        -- First, `w ∈ f ⁻¹' interior B`.
        have hw_in_pre : w ∈ f ⁻¹' interior (B : Set Y) := hy_intB
        -- This set is open and contained in `f ⁻¹' B`.
        have hT_open : IsOpen (f ⁻¹' interior (B : Set Y)) :=
          (isOpen_interior.preimage hf)
        have hT_subset :
            (f ⁻¹' interior (B : Set Y)) ⊆ f ⁻¹' (B : Set Y) := by
          intro u hu
          dsimp [Set.preimage] at hu ⊢
          -- `interior_subset` turns `f u ∈ interior B` into `f u ∈ B`.
          exact (interior_subset hu)
        -- Hence this set is contained in the interior of `f ⁻¹' B`.
        have hT_subset_int :
            (f ⁻¹' interior (B : Set Y)) ⊆
              interior (f ⁻¹' (B : Set Y)) :=
          interior_maximal hT_subset hT_open
        exact hT_subset_int hw_in_pre
      -- Provide the required witness in `V ∩ interior (f ⁻¹' B)`.
      exact ⟨w, hwV, hw_int_pre⟩
    exact this
  -- Since `S` is open and contained in the closure, it is contained in its interior.
  have hS_sub_int :
      S ⊆ interior (closure (interior (f ⁻¹' (B : Set Y)))) :=
    interior_maximal hS_sub hS_open
  -- Conclude for the original point `x`.
  exact hS_sub_int hxS

theorem P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P2 A ↔ Topology.P3 A := by
  -- `Dense (interior A)` already yields `P2 A`.
  have hP2_dense : Topology.P2 A :=
    P2_of_dense_interior (X := X) (A := A) h
  exact
    ⟨fun hP2 => P2_implies_P3 (X := X) (A := A) hP2,
     fun _hP3 => hP2_dense⟩

theorem P3_of_dense_iUnion {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (hA : ∀ n, Dense (A n)) : Topology.P3 (⋃ n, A n) := by
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3]
  intro x hx
  -- First, prove that the closure of the union is `univ`.
  have h_closure_univ :
      closure (⋃ n, (A n : Set X)) = (Set.univ : Set X) := by
    -- `A 0` is dense, hence its closure is `univ`.
    have hA0 : closure (A 0 : Set X) = (Set.univ : Set X) := by
      simpa using (hA 0).closure_eq
    -- `A 0 ⊆ ⋃ n, A n`.
    have hA0_subset : (A 0 : Set X) ⊆ ⋃ n, A n := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨0, hy⟩
    -- Therefore `closure (A 0) ⊆ closure (⋃ n, A n)`.
    have h_closure_subset :
        closure (A 0 : Set X) ⊆ closure (⋃ n, A n : Set X) :=
      closure_mono hA0_subset
    -- Rewrite the inclusion using `hA0`.
    have : (Set.univ : Set X) ⊆ closure (⋃ n, A n : Set X) := by
      simpa [hA0] using h_closure_subset
    -- Conclude with set equality.
    exact Set.Subset.antisymm (Set.subset_univ _) this
  -- Now `interior (closure …) = univ`, so the goal is immediate.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure_univ, interior_univ] using this

theorem P2_union_compl {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P2_univ (X := X))

theorem P1_closure_inter_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure A ∩ interior A) := by
  -- The intersection coincides with `interior A`, since `interior A ⊆ closure A`.
  have h_eq : (closure (A : Set X) ∩ interior A : Set X) = interior A := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      have h_cl : x ∈ closure (A : Set X) :=
        subset_closure (interior_subset hx)
      exact And.intro h_cl hx
  -- Hence the statement follows from `P1` for `interior A`.
  simpa [h_eq] using (P1_interior (X := X) (A := A))

theorem P1_iterate {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h0 : Topology.P1 (A 0)) (hstep : ∀ n, Topology.P1 (A n) → Topology.P1 (A (n + 1))) : ∀ n, Topology.P1 (A n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => exact hstep n ih

theorem P3_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : Topology.P3 B → Topology.P3 (((Set.univ : Set X).prod B)) := by
  intro hB
  have hUniv : Topology.P3 (Set.univ : Set X) := P3_univ (X := X)
  simpa using
    (P3_prod (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB)

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (A.prod (Set.univ : Set Y)) := by
  have hUniv : Topology.P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P2_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : Topology.P2 B) : Topology.P2 ((Set.univ : Set X).prod B) := by
  have hUniv : Topology.P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa using
    (P2_prod (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB)

theorem exists_closed_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ F : Set X, IsClosed F ∧ F ⊆ A ∧ Topology.P1 F := by
  refine ⟨(∅ : Set X), isClosed_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · simpa using (P1_empty (X := X))

theorem P1_preimage_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (h_open : IsOpenMap f) {B : Set Y} (hB : Topology.P1 B) : Topology.P1 (f ⁻¹' B) := by
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at hB ⊢
  -- Take a point of the preimage.
  intro x hx
  -- View this point in the image space.
  have hfxB : f x ∈ (B : Set Y) := hx
  -- Apply the hypothesis on `B`.
  have h_cl : f x ∈ closure (interior (B : Set Y)) := hB hfxB
  -- We will show that `x` is in the closure of `interior (f ⁻¹' B)`.
  apply (mem_closure_iff).2
  intro U hU_open hxU
  -- The image of `U` is an open neighbourhood of `f x`.
  have h_fU_open : IsOpen (f '' U) := h_open _ hU_open
  have hfx_in_fU : f x ∈ f '' U := ⟨x, hxU, rfl⟩
  -- Hence it meets `interior B`.
  have h_nonempty :
      ((f '' U) ∩ interior (B : Set Y)).Nonempty :=
    (mem_closure_iff).1 h_cl (f '' U) h_fU_open hfx_in_fU
  -- Pick a point in the intersection.
  rcases h_nonempty with ⟨y, ⟨⟨z, hzU, rfl⟩, hz_intB⟩⟩
  -- `z ∈ U` and `f z ∈ interior B`.
  -- Show that `z ∈ interior (f ⁻¹' B)`.
  have hz_int : z ∈ interior (f ⁻¹' (B : Set Y)) := by
    -- First, `z` belongs to the preimage of `interior B`.
    have hz_pre : z ∈ f ⁻¹' interior (B : Set Y) := hz_intB
    -- This preimage is open …
    have h_open_pre : IsOpen (f ⁻¹' interior (B : Set Y)) :=
      (isOpen_interior.preimage hf)
    -- … and contained in `f ⁻¹' B`.
    have h_sub_pre :
        (f ⁻¹' interior (B : Set Y) : Set X) ⊆ f ⁻¹' (B : Set Y) := by
      intro t ht
      dsimp [Set.preimage] at ht ⊢
      exact interior_subset ht
    -- Hence it is contained in the interior of `f ⁻¹' B`.
    have h_to_int :
        (f ⁻¹' interior (B : Set Y) : Set X) ⊆
          interior (f ⁻¹' (B : Set Y)) :=
      interior_maximal h_sub_pre h_open_pre
    exact h_to_int hz_pre
  -- Provide the required witness in `U ∩ interior (f ⁻¹' B)`.
  exact ⟨z, hzU, hz_int⟩

theorem exists_P1_closed_dense {X : Type*} [TopologicalSpace X] : ∃ F : Set X, IsClosed F ∧ Dense F ∧ Topology.P1 F := by
  refine ⟨(Set.univ : Set X), isClosed_univ, dense_univ, ?_⟩
  simpa using (P1_univ (X := X))

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P2 (A.prod B)) ↔ Topology.P2 (B.prod A) := by
  constructor
  · intro h
    -- transport `P2` through the coordinate‐swap homeomorphism
    have h_image :
        Topology.P2
          ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) := by
      simpa using
        (P2_image_homeomorph
            (e := Homeomorph.prodComm (X := X) (Y := Y))
            (A := A.prod B)
            h)
    -- identify this image with `B × A`
    have h_eq :
        ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) =
          B.prod A := by
      ext p
      constructor
      · rintro ⟨⟨x, y⟩, hxy, rfl⟩
        rcases hxy with ⟨hxA, hyB⟩
        exact And.intro hyB hxA
      · intro hp
        rcases p with ⟨y, x⟩
        rcases hp with ⟨hyB, hxA⟩
        refine ⟨(x, y), ?_, rfl⟩
        exact And.intro hxA hyB
    simpa [h_eq] using h_image
  · intro h
    -- transport `P2` in the opposite direction
    have h_image :
        Topology.P2
          ((fun p : Y × X => Prod.swap p) '' (B.prod A) : Set (X × Y)) := by
      simpa using
        (P2_image_homeomorph
            (e := Homeomorph.prodComm (X := Y) (Y := X))
            (A := B.prod A)
            h)
    -- identify this image with `A × B`
    have h_eq :
        ((fun p : Y × X => Prod.swap p) '' (B.prod A) : Set (X × Y)) =
          A.prod B := by
      ext p
      constructor
      · rintro ⟨⟨y, x⟩, hxy, rfl⟩
        rcases hxy with ⟨hyB, hxA⟩
        exact And.intro hxA hyB
      · intro hp
        rcases p with ⟨x, y⟩
        rcases hp with ⟨hxA, hyB⟩
        refine ⟨(y, x), ?_, rfl⟩
        exact And.intro hyB hxA
    simpa [h_eq] using h_image

theorem exists_P2_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ Topology.P2 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · simpa using (P2_empty (X := X))

theorem P1_closure_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 ((closure A).prod (closure B)) := by
  -- Upgrade the hypotheses to the closures.
  have hA_cl : Topology.P1 (closure (A : Set X)) :=
    P1_closure (X := X) (A := A) hA
  have hB_cl : Topology.P1 (closure (B : Set Y)) :=
    P1_closure (X := Y) (A := B) hB
  -- Apply the product lemma.
  simpa using
    (P1_prod (X := X) (Y := Y)
      (A := closure (A : Set X)) (B := closure (B : Set Y)) hA_cl hB_cl)

theorem P3_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) : Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using (Topology.P3_of_open (X := X) (A := A ∩ B) hOpen)

theorem P2_image_equiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (A : Set X) : Topology.P2 (e '' A) ↔ Topology.P2 A := by
  constructor
  · intro hImage
    -- Pull `P2` back through the inverse homeomorphism.
    have hPreimage : Topology.P2 (e.symm '' (e '' A)) :=
      P2_preimage_homeomorph (e := e) (B := e '' A) hImage
    -- Identify the pulled‐back set with `A`.
    have h_eq : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨z, hzA, rfl⟩
        have : z = x := by
          simpa [e.symm_apply_apply] using hxy
        simpa [this] using hzA
      · intro hxA
        refine ⟨e x, ?_, ?_⟩
        · exact ⟨x, hxA, rfl⟩
        · simpa using e.symm_apply_apply x
    simpa [h_eq] using hPreimage
  · intro hA
    exact P2_image_homeomorph (e := e) hA

theorem P3_prod_univ_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} (hA : Topology.P3 A) : Topology.P3 ((A.prod (Set.univ : Set Y)).prod (Set.univ : Set Z)) := by
  -- Obtain `P3` for `A × univ` on the second factor.
  have hAU : Topology.P3 (A.prod (Set.univ : Set Y)) :=
    (P3_prod_univ (X := X) (Y := Y) (A := A)) hA
  -- `univ` in `Z` satisfies `P3`.
  have hUnivZ : Topology.P3 (Set.univ : Set Z) := P3_univ (X := Z)
  -- Combine the two using the product lemma.
  simpa using
    (P3_prod
      (X := X × Y) (Y := Z)
      (A := (A.prod (Set.univ : Set Y)))
      (B := (Set.univ : Set Z))
      hAU hUnivZ)

theorem P2_bUnion_closed {X ι : Type*} [TopologicalSpace X] {s : Set ι} {A : ι → Set X} (hA : ∀ i ∈ s, IsClosed (A i)) (hP : ∀ i ∈ s, Topology.P2 (A i)) : Topology.P2 (⋃ i ∈ s, A i) := by
  dsimp [Topology.P2] at hP ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨his, hxAi⟩
  have hP2i : Topology.P2 (A i) := hP i his
  have hx' : x ∈ interior (closure (interior (A i))) := hP2i hxAi
  have hsubset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ i ∈ s, A i))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    have : y ∈ ⋃ j ∈ s, A j := by
      apply Set.mem_iUnion.2
      exact ⟨i, Set.mem_iUnion.2 ⟨his, hy⟩⟩
    exact this
  exact hsubset hx'

theorem P3_image_open_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Embedding f) (h_open : IsOpenMap f) {A : Set X} (hA : Topology.P3 A) : Topology.P3 (f '' A) := by
  -- Unfold the definition of `P3` in the hypothesis and in the goal.
  dsimp [Topology.P3] at hA ⊢
  -- Take a point of `f '' A`.
  intro y hy
  -- Write it as `f x` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Use the hypothesis on `A`.
  have hx_int : x ∈ interior (closure (A : Set X)) := hA hxA
  -- Consider the open set `W = f '' interior (closure A)`.
  have hW_open :
      IsOpen (f '' interior (closure (A : Set X))) :=
    h_open _ isOpen_interior
  -- Our point belongs to `W`.
  have hxW :
      (f : X → Y) x ∈ f '' interior (closure (A : Set X)) :=
    ⟨x, hx_int, rfl⟩
  -- We now show `W ⊆ closure (f '' A)`.
  have hW_sub :
      (f '' interior (closure (A : Set X))) ⊆
        closure (f '' (A : Set X)) := by
    intro z hz
    rcases hz with ⟨x', hx'int, rfl⟩
    -- First, `x' ∈ closure A`.
    have hx'_cl : x' ∈ closure (A : Set X) := interior_subset hx'int
    -- We prove that `f x'` is in the desired closure.
    have : f x' ∈ closure (f '' (A : Set X)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro V hVopen hfxV
      -- Pull the neighbourhood back through `f`.
      have hU_open : IsOpen (f ⁻¹' V) := hVopen.preimage hf.continuous
      have hx'U : x' ∈ f ⁻¹' V := hfxV
      -- Since `x'` is in the closure of `A`, `f ⁻¹' V` meets `A`.
      have h_nonempty :
          ((f ⁻¹' V) ∩ (A : Set X)).Nonempty :=
        (mem_closure_iff).1 hx'_cl _ hU_open hx'U
      rcases h_nonempty with ⟨w, ⟨hwU, hwA⟩⟩
      -- The point `f w` is in `V ∩ f '' A`.
      have hfw_in : f w ∈ V ∩ f '' (A : Set X) := by
        refine And.intro ?_ ?_
        · exact hwU
        · exact ⟨w, hwA, rfl⟩
      -- Provide the required witness.
      exact ⟨f w, hfw_in⟩
    exact this
  -- By maximality of the interior we obtain the desired inclusion.
  have hW_sub_int :
      (f '' interior (closure (A : Set X))) ⊆
        interior (closure (f '' (A : Set X))) :=
    interior_maximal hW_sub hW_open
  -- Conclude for our point.
  exact hW_sub_int hxW

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : Topology.P1 B) : Topology.P1 ((Set.univ : Set X).prod B) := by
  have hUniv : Topology.P1 (Set.univ : Set X) := P1_univ (X := X)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB)

theorem exists_P1_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ Topology.P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · simpa using (P1_empty (X := X))

theorem P2_Union_finite {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {A : ι → Set X} (hA : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  simpa using P2_iUnion (X := X) (A := A) hA

theorem P2_of_perfect {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h_dense : Dense A) : Topology.P2 A := by
  -- `A` is the whole space since it is both closed and dense.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    have h1 : closure (A : Set X) = A := hA.closure_eq
    have h2 : closure (A : Set X) = (Set.univ : Set X) := h_dense.closure_eq
    simpa [h1] using h2
  -- Unfold `P2` and conclude.
  dsimp [Topology.P2]
  intro x hx
  simpa [hA_univ, interior_univ, closure_univ] using (Set.mem_univ x)