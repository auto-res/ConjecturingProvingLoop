

theorem Topology.P2_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_boundary : closure (A : Set X) \ interior A = (∅ : Set X)) :
    Topology.P2 (X := X) A := by
  -- From the vanishing boundary we obtain that `A` is both open and closed.
  have h_clopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (Topology.boundary_empty_iff_isClopen (X := X) (A := A)).1 h_boundary
  -- Any open set satisfies `P2`.
  exact isOpen_implies_P2 (X := X) (A := A) h_clopen.1