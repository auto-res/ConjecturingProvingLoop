

theorem Topology.interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure A)) :
    interior (closure A) = closure A := by
  simpa using h.interior_eq