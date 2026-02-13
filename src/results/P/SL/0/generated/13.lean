

theorem interior_subset_interior_closure_inter {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior A : Set X) ⊆ interior (closure (interior A)) := by
  have h : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  simpa using interior_mono h