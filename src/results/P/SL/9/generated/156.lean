

theorem Topology.isOpen_closure_iff_interiorClosure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure (A : Set X)) = closure A := by
  constructor
  · intro h_open
    simpa using h_open.interior_eq
  · intro h_eq
    simpa [h_eq] using (isOpen_interior : IsOpen (interior (closure A)))