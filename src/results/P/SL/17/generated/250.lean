

theorem Topology.dense_iff_eq_univ_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Dense A ↔ A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    -- In a discrete space every set is closed, so its closure is itself.
    have hClosed : IsClosed A := isClosed_discrete _
    have hClosureSelf : closure A = A := hClosed.closure_eq
    -- Density gives `closure A = univ`; rewrite to obtain the desired equality.
    have hClosureUniv : closure A = (Set.univ : Set X) := hDense.closure_eq
    simpa [hClosureSelf] using hClosureUniv
  · intro hEq
    -- If `A = univ`, it is trivially dense.
    simpa [hEq] using (dense_univ : Dense (Set.univ : Set X))