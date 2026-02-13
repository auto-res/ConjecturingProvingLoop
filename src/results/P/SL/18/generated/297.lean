

theorem P1_of_closed_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hInt : interior (A : Set X) = A) :
    Topology.P1 (A : Set X) := by
  -- Since `A = interior A`, the set `A` is open.
  have hOpen : IsOpen (A : Set X) := by
    simpa [hInt] using (isOpen_interior : IsOpen (interior (A : Set X)))
  -- Apply the existing lemma for open sets.
  exact Topology.P1_of_open (A := A) hOpen