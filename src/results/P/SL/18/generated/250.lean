

theorem interior_closure_eq_self_of_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  calc
    interior (closure (A : Set X))
        = interior (A : Set X) :=
          (interior_closure_eq_interior_of_closed (A := A) hClosed)
    _ = A := hOpen.interior_eq