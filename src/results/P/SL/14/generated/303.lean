

theorem Topology.P1_closure_iff_P1_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (closure A) ↔ Topology.P1 A := by
  -- Since `A` is closed, its closure equals itself.
  have h_eq : (closure A : Set X) = A := hA_closed.closure_eq
  -- Rewriting with this equality shows that the two `P1` statements coincide.
  simpa [h_eq] using
    (Iff.rfl : Topology.P1 (closure A) ↔ Topology.P1 (closure A))