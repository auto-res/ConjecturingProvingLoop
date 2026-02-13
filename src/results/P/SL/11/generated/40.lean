

theorem closure_interior_eq_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : closure (interior A) = closure A := by
  simpa [hA.interior_eq]