

theorem Topology.closed_dense_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) :
    A = (Set.univ : Set X) := by
  -- Since `A` is closed, its closure is itself.
  have h₁ : closure A = A := hClosed.closure_eq
  -- Since `A` is dense, its closure is the whole space.
  have h₂ : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Combining the two equalities yields the desired result.
  simpa [h₁] using h₂