

theorem Topology.interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure A) → interior (closure A) = closure A := by
  intro hOpen
  simpa using hOpen.interior_eq