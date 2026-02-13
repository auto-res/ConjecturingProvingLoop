

theorem nonempty_iff_nonempty_interior_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  have hEq : interior (A : Set X) = A := hA.interior_eq
  constructor
  · intro hNon
    simpa [hEq] using hNon
  · intro hInt
    simpa [hEq] using hInt