

theorem interior_inter_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((interior (A : Set X) ∩ interior (B : Set X)) : Set X) =
      interior (A : Set X) ∩ interior (B : Set X) := by
  have hOpenA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hOpenB : IsOpen (interior (B : Set X)) := isOpen_interior
  simpa using
    interior_inter_eq_self_of_open
      (X := X)
      (A := interior (A : Set X))
      (B := interior (B : Set X))
      hOpenA
      hOpenB