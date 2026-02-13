

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  have h : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  simpa [interior_interior] using (interior_mono h)