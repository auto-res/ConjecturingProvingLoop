

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro h
    exact Topology.closure_eq_closure_interior_of_P1 h
  · intro hEq
    dsimp [Topology.P1]
    have hsubset : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq] using hsubset