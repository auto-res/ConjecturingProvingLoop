

theorem isOpen_interior_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    IsOpen (interior (closure (interior A))) := by
  simpa using
    (isOpen_interior :
      IsOpen (interior (closure (interior A))))