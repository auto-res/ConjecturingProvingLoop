

theorem Topology.interior_closure_interior_eq_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    interior (closure (interior A)) = interior (closure A) := by
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  simpa [h_eq]