

theorem P1_iff_closure_inter_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply subset_antisymm
    · -- `closure (interior A) ⊆ closure A`
      exact closure_mono interior_subset
    · -- `closure A ⊆ closure (interior A)`
      have h : (A : Set X) ⊆ closure (interior A) := hP1
      have h' : closure (A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono h
      simpa [closure_closure] using h'
  · intro h_eq
    -- Need to show `A ⊆ closure (interior A)`
    intro x hx
    have : x ∈ closure (A : Set X) := subset_closure hx
    simpa [h_eq] using this

theorem exists_open_subset_P3 {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ U ⊆ A ∧ P3 U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  simpa using (interior_maximal subset_closure isOpen_interior)