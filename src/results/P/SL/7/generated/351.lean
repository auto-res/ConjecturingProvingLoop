

theorem Topology.P3_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 (Aᶜ) := by
  -- We already have a result giving all three properties for the complement of a closed set.
  -- Extract the `P3` component from that result.
  have h := (Topology.P1_P2_P3_compl_of_closed (A := A) hA)
  exact h.2.2