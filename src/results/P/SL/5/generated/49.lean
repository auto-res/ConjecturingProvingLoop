

theorem closure_interior_closure_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    closure (interior (closure (A : Set X))) ⊆ A := by
  -- Since `A` is closed, its closure is itself.
  have h_closure_eq : closure (A : Set X) = A := hA.closure_eq
  -- First, `interior (closure A)` is contained in `closure A`, hence in `A`.
  have h_subset : (interior (closure (A : Set X)) : Set X) ⊆ A := by
    have h' : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    simpa [h_closure_eq] using h'
  -- Taking closures preserves inclusions; rewrite via `closure A = A`.
  simpa [h_closure_eq] using closure_mono h_subset