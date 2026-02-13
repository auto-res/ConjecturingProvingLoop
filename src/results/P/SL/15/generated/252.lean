

theorem closure_interior_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  -- The interior of an open set is itself.
  have h : interior (interior A) = interior A := by
    simpa using (isOpen_interior (A := A)).interior_eq
  simpa [h]