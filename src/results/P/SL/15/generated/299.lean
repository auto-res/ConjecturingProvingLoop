

theorem interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior A : Set X) = interior A := by
  simpa using (isOpen_interior (A := A)).interior_eq