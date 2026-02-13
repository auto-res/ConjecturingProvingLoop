

theorem interior_closure_interior_eq_interior_of_closed_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosedInt : IsClosed (interior (A : Set X))) :
    interior (closure (interior (A : Set X))) = interior (A : Set X) := by
  have h : closure (interior (A : Set X)) = interior (A : Set X) :=
    hClosedInt.closure_eq
  simpa [h, interior_interior]