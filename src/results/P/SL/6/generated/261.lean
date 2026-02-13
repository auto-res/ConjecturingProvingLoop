

theorem isOpen_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsOpen (interior (closure (A : Set X))) := by
  simpa using
    (isOpen_interior : IsOpen (interior (closure (A : Set X))))