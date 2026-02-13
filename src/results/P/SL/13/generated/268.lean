

theorem Topology.boundary_empty_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen (A : Set X)) (hA_closed : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior A = (∅ : Set X) := by
  have h_int : interior (A : Set X) = A := hA_open.interior_eq
  have h_cl : closure (A : Set X) = A := hA_closed.closure_eq
  simpa [h_int, h_cl, Set.diff_self]