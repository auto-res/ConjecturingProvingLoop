

theorem isClosed_iff_closure_interior_eq_of_open {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    IsClosed A ↔ closure (interior A) = A := by
  have hInt : interior A = A := hA.interior_eq
  constructor
  · intro hClosed
    calc
      closure (interior A)
          = closure A := by
            simpa [hInt]
      _ = A := hClosed.closure_eq
  · intro hEq
    -- From the given equality and `hInt`, deduce `closure A = A`.
    have hCl : closure A = A := by
      simpa [hInt] using hEq
    -- `closure A` is always closed; rewrite using `hCl`.
    have hClosedClosure : IsClosed (closure A) := isClosed_closure
    simpa [hCl] using hClosedClosure