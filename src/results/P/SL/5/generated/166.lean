

theorem closure_interior_subset_of_subset_closed
    {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hAC : (A : Set X) ⊆ C) (hC_closed : IsClosed (C : Set X)) :
    closure (interior (A : Set X)) ⊆ C := by
  -- First, note `interior A ⊆ A ⊆ C`.
  have h₁ : (interior (A : Set X) : Set X) ⊆ C :=
    interior_subset.trans hAC
  -- Taking closures preserves inclusions; rewrite using `closure C = C`
  -- because `C` is closed.
  simpa [hC_closed.closure_eq] using closure_mono h₁