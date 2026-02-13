

theorem P2_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) →
      Topology.P2 (A : Set X) := by
  intro hBoundary
  -- An empty boundary implies that `A` is both open and closed.
  have hClopen :
      IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  -- Every open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A) hClopen.1