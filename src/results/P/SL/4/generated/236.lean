

theorem frontier_subset_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    frontier A ⊆ A := by
  intro x hx
  -- From `hx` we have `x ∈ closure A`.
  have hx_closure : x ∈ closure A := hx.1
  -- For a closed set, its closure is itself.
  simpa [hA.closure_eq] using hx_closure