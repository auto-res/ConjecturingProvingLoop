

theorem frontier_frontier_subset_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    frontier (frontier (A : Set X)) ⊆ A := by
  intro x hx
  -- Step 1: `frontier A ⊆ A` because `A` is closed.
  have h_sub : frontier A ⊆ A :=
    frontier_subset_of_closed (A := A) hA
  -- Step 2: Taking closures preserves inclusions, and `closure A = A`.
  have h_closure : closure (frontier A) ⊆ A := by
    have h := closure_mono h_sub
    simpa [hA.closure_eq] using h
  -- Step 3: `x` lies in `closure (frontier A)` by definition of the frontier,
  -- hence in `A` by `h_closure`.
  exact h_closure hx.1