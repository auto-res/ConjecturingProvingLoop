

theorem Topology.isOpen_closure_iff_interior_closure_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure (A : Set X)) = closure A := by
  constructor
  · intro h_open
    exact
      Topology.interior_closure_eq_closure_of_isOpen_closure
        (X := X) (A := A) h_open
  · intro h_eq
    have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [h_eq] using this