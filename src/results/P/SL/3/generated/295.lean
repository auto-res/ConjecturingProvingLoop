

theorem interior_inter_interiors_eq_inter_interiors
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (interior (A : Set X) ∩ interior B) =
      interior (A : Set X) ∩ interior B := by
  have hOpenA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hOpenB : IsOpen (interior (B : Set X)) := isOpen_interior
  simpa using
    (interior_inter_eq_of_isOpen
        (A := interior (A : Set X)) (B := interior (B : Set X))
        hOpenA hOpenB)