

theorem Topology.dense_closure_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure A) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    simpa [closure_closure] using hDense.closure_eq
  · intro hEq
    dsimp [Dense]
    simpa [closure_closure, hEq]