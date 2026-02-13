

theorem open_closure_interior_iff_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior (A : Set X))) ↔
      interior (closure (interior A)) = closure (interior A) := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have hOpenInt : IsOpen (interior (closure (interior (A : Set X)))) := isOpen_interior
    simpa [hEq] using hOpenInt