

theorem P123_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) (hClosed : IsClosed A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- Since `A` is open, all three properties follow immediately from
  -- `Topology.P123_of_open`.
  simpa using Topology.P123_of_open (A := A) hOpen