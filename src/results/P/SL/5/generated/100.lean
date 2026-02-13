

theorem closure_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = closure (A : Set X) := by
  simpa using
    ((Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1).symm