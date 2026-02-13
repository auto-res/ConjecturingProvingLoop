

theorem closure_interior_eq_self_of_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  have hClos : closure (A : Set X) = A := hClosed.closure_eq
  calc
    closure (interior (A : Set X)) = closure (A : Set X) := by
      simpa [hInt]
    _ = A := by
      simpa [hClos]