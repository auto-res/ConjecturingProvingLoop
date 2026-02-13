

theorem Topology.closureInterior_eq_self_of_isClopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_open : IsOpen (A : Set X)) (hA_closed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  have h_int : interior (A : Set X) = A := hA_open.interior_eq
  have h_cl : closure (A : Set X) = A := hA_closed.closure_eq
  simpa [h_int, h_cl]