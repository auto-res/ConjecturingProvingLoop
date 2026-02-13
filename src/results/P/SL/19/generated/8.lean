

theorem Topology.P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  · intro hEq
    exact Topology.P1_of_closure_eq_closure_interior (A := A) hEq