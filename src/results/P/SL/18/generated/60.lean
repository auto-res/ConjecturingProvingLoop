

theorem closure_eq_closure_interior_of_open {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure A = closure (interior A) := by
  have hP2 : Topology.P2 A := Topology.P2_of_open hA
  exact Topology.closure_eq_closure_interior_of_P2 hP2