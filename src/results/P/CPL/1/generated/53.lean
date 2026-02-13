

theorem P2_of_closure_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure (interior A))) : P2 A := by
  intro x hx
  exact h (subset_closure hx)

theorem exists_P3_within_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : ∃ B : Set X, B ⊆ closure A ∧ P3 B := by
  refine ⟨interior (closure A), ?_, ?_⟩
  ·
    exact interior_subset
  ·
    exact P3_of_isOpen (A := interior (closure A)) isOpen_interior