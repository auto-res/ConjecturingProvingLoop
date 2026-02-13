

theorem interior_compl_eq_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    interior (Aᶜ) = Aᶜ := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  simpa using hOpen.interior_eq