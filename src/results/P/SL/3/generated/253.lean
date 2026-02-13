

theorem isClopen_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = interior (A : Set X) →
      (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  intro hEq
  -- The boundary of `A` is empty, since `closure A = interior A`.
  have hBoundary :
      closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
    simpa [hEq, Set.diff_self]
  -- Apply the characterisation of clopen sets via empty boundary.
  exact (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary