

theorem Topology.boundary_empty_implies_all_P {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_boundary : closure (A : Set X) \ interior A = (∅ : Set X)) :
    Topology.P1 (X:=X) A ∧ Topology.P2 (X:=X) A ∧ Topology.P3 (X:=X) A := by
  -- From the empty boundary, we learn that `A` is both open and closed.
  have h_clopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (Topology.boundary_empty_iff_isClopen (X := X) (A := A)).1 h_boundary
  -- Any open set satisfies all three properties `P1`, `P2`, and `P3`.
  simpa using
    Topology.isOpen_implies_all_P (X := X) (A := A) h_clopen.1