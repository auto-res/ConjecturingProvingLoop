

theorem P3_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) →
      Topology.P3 A := by
  intro hBoundary
  -- From the empty boundary we infer that `A` is both open and closed.
  have hClopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  -- Every open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A) hClopen.1