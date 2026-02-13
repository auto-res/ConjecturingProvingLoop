

theorem interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure (interior A)) := by
  -- First, note the basic inclusion `interior A ⊆ closure (interior A)`.
  have h :
      interior (interior A) ⊆ interior (closure (interior A)) := by
    apply interior_mono
    exact (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  -- Rewrite `interior (interior A)` as `interior A` to obtain the goal.
  simpa [interior_interior] using h