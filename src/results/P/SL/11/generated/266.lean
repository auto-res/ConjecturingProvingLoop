

theorem isOpen_closure_iff_interior_closure_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure A) = closure A := by
  constructor
  · intro hOpen
    exact hOpen.interior_eq
  · intro hEq
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    simpa [hEq] using hOpen