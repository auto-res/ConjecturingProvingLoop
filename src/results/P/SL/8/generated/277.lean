

theorem closureInterior_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    closure (interior (closure A)) = closure A := by
  -- Since `closure A` is open, its interior is itself.
  have h_int : interior (closure A) = closure A := h_open.interior_eq
  -- Taking closures and simplifying yields the desired equality.
  calc
    closure (interior (closure A))
        = closure (closure A) := by
            simpa [h_int]
    _ = closure A := by
            simpa [closure_closure]