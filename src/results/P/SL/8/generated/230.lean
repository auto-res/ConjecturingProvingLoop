

theorem isOpen_closure_iff_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure A) ↔ interior (closure A) = closure A := by
  constructor
  · intro h_open
    simpa using h_open.interior_eq
  · intro h_eq
    have h_open_int : IsOpen (interior (closure A)) := isOpen_interior
    simpa [h_eq] using h_open_int