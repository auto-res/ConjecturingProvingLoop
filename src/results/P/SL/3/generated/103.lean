

theorem isOpen_of_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = A → IsOpen (A : Set X) := by
  intro hA
  have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa [hA] using this