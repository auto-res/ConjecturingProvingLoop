

theorem Topology.dense_interior_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro h
    simpa using h.closure_eq
  · intro h
    exact (dense_iff_closure_eq).2 h