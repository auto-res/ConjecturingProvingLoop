

theorem closure_inter_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure (A ∩ interior B) ⊆ B := by
  -- `interior B` is contained in `B`.
  have h_subset : A ∩ interior B ⊆ B := by
    intro x hx
    exact (interior_subset : interior B ⊆ B) hx.2
  -- Taking closures preserves inclusions.
  have h_closure : closure (A ∩ interior B) ⊆ closure B :=
    closure_mono h_subset
  -- Since `B` is closed, `closure B = B`.
  simpa [hB.closure_eq] using h_closure