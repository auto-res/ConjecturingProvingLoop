

theorem isOpen_of_isClosed_and_boundary_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X))
    (hBoundary : closure (A : Set X) \ interior (A : Set X) = (∅ : Set X)) :
    IsOpen (A : Set X) := by
  have hClopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  exact hClopen.1