

theorem Topology.boundary_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (A : Set X) \ interior A ⊆ A := by
  intro x hx
  -- `x` lies in the closure of `A`, but `A` is closed, hence
  -- `closure A = A`.  This places `x` inside `A`.
  simpa [hA.closure_eq] using hx.1