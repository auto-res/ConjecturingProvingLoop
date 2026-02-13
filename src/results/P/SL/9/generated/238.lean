

theorem Topology.frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : frontier (A : Set X) ⊆ A := by
  intro x hx
  -- `hx` provides `x ∈ closure A`.
  have hx_cl : x ∈ closure (A : Set X) := hx.1
  -- Since `A` is closed, we have `closure A = A`.
  have h_cl_eq : closure (A : Set X) = A := hA.closure_eq
  -- The desired result follows by rewriting.
  simpa [h_cl_eq] using hx_cl