

theorem boundary_eq_empty_of_isClopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
  have hClosure : closure (A : Set X) = A := hClosed.closure_eq
  have hInterior : interior (A : Set X) = A := hOpen.interior_eq
  simpa [hClosure, hInterior, Set.diff_self]