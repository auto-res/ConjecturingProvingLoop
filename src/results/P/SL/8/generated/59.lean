

theorem interior_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure A) := by
  have h : A ⊆ closure A := subset_closure
  exact interior_mono h