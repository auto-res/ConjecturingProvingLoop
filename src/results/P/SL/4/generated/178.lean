

theorem isOpen_iff_interior_closure_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    IsOpen A ↔ interior (closure A) = A := by
  have hCl : closure A = A := hA.closure_eq
  constructor
  · intro hOpen
    calc
      interior (closure A) = interior A := by
        simpa [hCl]
      _ = A := by
        simpa [hOpen.interior_eq]
  · intro hEq
    -- From the given equality and `hCl`, deduce `interior A = A`.
    have hIntA : interior A = A := by
      simpa [hCl] using hEq
    -- `interior A` is open; rewrite using `hIntA`.
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hIntA] using hOpenInt