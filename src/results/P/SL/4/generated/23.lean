

theorem closed_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) (hP1 : Topology.P1 A) :
    A = closure (interior A) := by
  have h : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [hA.closure_eq] using h