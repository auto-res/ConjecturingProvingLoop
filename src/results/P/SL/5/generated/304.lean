

theorem interior_eq_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    interior (A : Set X) = A := by
  simpa using hA.interior_eq