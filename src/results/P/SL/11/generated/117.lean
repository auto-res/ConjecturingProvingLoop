

theorem closure_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) :
    closure A = closure (interior (closure A)) := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) h
  simpa using Topology.closure_eq_closure_interior_closure_of_P3 (A := A) hP3