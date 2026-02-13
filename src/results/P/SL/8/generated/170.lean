

theorem closed_P2_imp_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    IsOpen A ∧ IsClosed A := by
  -- From `hP2` and the fact that `A` is closed, we know that `A` is open.
  have h_open : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2
  -- Combine the obtained openness with the given closedness.
  exact And.intro h_open hA_closed