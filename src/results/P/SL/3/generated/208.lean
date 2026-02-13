

theorem interior_closure_interior_eq_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (closure (interior (A : Set X))) = interior (closure (A : Set X)) := by
  have h := closure_interior_eq_closure_of_isOpen (A := A) hA
  simpa [h]