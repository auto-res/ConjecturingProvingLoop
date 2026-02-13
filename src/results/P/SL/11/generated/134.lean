

theorem P2_iff_closure_eq_closure_interior_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    Topology.P2 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP2
    exact Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  · intro hEq
    exact Topology.P2_of_P3_and_closure_eq_closure_interior (A := A) hP3 hEq