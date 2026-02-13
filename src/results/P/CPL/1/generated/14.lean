

theorem interior_eq_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : P3 A) : interior A = A := by
  -- First, deduce `interior (closure A) = A`.
  have h_int_closure : interior (closure A) = A := by
    have h_eq := closure_eq_of_P3_closed (A := A) hA h
    simpa [hA.closure_eq] using h_eq.symm
  -- Now obtain the desired equality.
  have : interior A = A := by
    calc
      interior A = interior (closure A) := by
        simpa [hA.closure_eq]
      _ = A := by
        simpa using h_int_closure
  exact this