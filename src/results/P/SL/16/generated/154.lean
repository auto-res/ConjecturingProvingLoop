

theorem Topology.closure_interior_eq_univ_of_dense_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X))
    (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = (Set.univ : Set X) := by
  -- From `P1`, we know `closure (interior A) = closure A`.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  -- Combine this with the density hypothesis `closure A = univ`.
  simpa [h_dense] using h_eq