

theorem Topology.closure_interior_eq_of_P2_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hClosed : IsClosed A) :
    closure (interior A) = A := by
  have h_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hP2
  have h_cl : closure A = A := hClosed.closure_eq
  simpa [h_cl] using h_eq.symm