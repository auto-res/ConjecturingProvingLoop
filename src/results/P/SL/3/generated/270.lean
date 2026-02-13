

theorem P1_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) →
      Topology.P1 A := by
  intro hBoundary
  -- An empty boundary implies that `A` is both open and closed.
  have hClopen :
      IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  -- Any open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A) hClopen.1