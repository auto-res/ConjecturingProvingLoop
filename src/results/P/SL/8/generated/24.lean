

theorem interior_closure_interior_eq_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    interior (closure (interior A)) = interior (closure A) := by
  have h : closure (interior A) = closure A :=
    Topology.closure_interior_eq_of_isOpen (X := X) (A := A) hA
  simpa [h]