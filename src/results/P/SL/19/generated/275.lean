

theorem Topology.closure_eq_univ_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (Set.univ : Set X) ↔ interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro h
    exact
      Topology.interior_closure_eq_univ_of_closure_eq_univ
        (X := X) (A := A) h
  · intro h
    exact
      Topology.closure_eq_univ_of_interior_closure_eq_univ
        (X := X) (A := A) h