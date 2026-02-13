

theorem Topology.P3_closure_interior_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure (interior A)) := by
  intro hDense
  -- Since `interior A` is dense, its (double) closure is the whole space.
  have hEq : closure (closure (interior A)) = (Set.univ : Set X) := by
    simpa [closure_closure] using hDense.closure_eq
  -- Apply the existing lemma to conclude the `P3` property.
  exact Topology.P3_of_closure_eq_univ (A := closure (interior A)) hEq