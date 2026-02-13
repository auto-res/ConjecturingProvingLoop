

theorem interior_closure_eq_self_of_isOpen_and_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  calc
    interior (closure (A : Set X)) = interior (A : Set X) := by
      simpa [hClosed.closure_eq]
    _ = A := by
      simpa [hOpen.interior_eq]