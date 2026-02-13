

theorem eq_empty_of_P1_and_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h2 : interior A = ∅) : A = ∅ := by
  ext x
  constructor
  · intro hxA
    have hx_closure : x ∈ closure (interior A) := h1 hxA
    simpa [h2, closure_empty] using hx_closure
  · intro hxEmpty
    cases hxEmpty

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : P3 A := by
  intro x hx
  simpa [hA, interior_univ] using (Set.mem_univ x)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_closure : x ∈ closure (interior A) := hA hxA
      -- `interior A ⊆ interior (A ∪ B)`
      have hsubset_int : interior A ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      -- take closures of the previous inclusion
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      exact hsubset hx_closure
  | inr hxB =>
      -- `x` comes from `B`
      have hx_closure : x ∈ closure (interior B) := hB hxB
      -- `interior B ⊆ interior (A ∪ B)`
      have hsubset_int : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      -- take closures of the previous inclusion
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      exact hsubset hx_closure

theorem exists_open_neighborhood_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A) := by
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hA hx
  refine ⟨interior (closure (interior A)), isOpen_interior, hx_int, ?_⟩
  exact interior_subset

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2 x hx
  exact interior_subset (hP2 hx)

theorem P1_and_not_P3_implies_not_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ∧ ¬ P3 A → ¬ P2 A := by
  rintro ⟨hP1, hnotP3⟩ hP2
  have hP3 : P3 A := P1_and_P2_implies_P3 ⟨hP1, hP2⟩
  exact hnotP3 hP3

theorem open_iff_P1_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : (P1 A ↔ P2 A) := by
  constructor
  · intro _; exact P2_of_open hA
  · exact P1_of_P2