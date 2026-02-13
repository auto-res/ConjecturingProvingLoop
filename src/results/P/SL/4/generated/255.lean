

theorem interior_inter_closure_of_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ closure B) = A ∩ interior (closure B) := by
  simpa using
    (interior_inter_of_isOpen_left (X := X) (A := A) (B := closure B) hA)