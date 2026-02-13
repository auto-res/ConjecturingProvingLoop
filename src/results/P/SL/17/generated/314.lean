

theorem Topology.frontier_eq_univ_diff_interior_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (hDense : Dense A) :
    frontier A = (Set.univ : Set X) \ interior A := by
  -- Since `A` is dense, its closure is the whole space.
  have hClosure : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Rewrite `frontier A` using its definition and the closure equality.
  simpa [frontier, hClosure]