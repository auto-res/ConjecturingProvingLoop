

theorem Topology.P2_of_isClosed_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    Topology.P2 (X := X) A := by
  -- Obtain the triple property for sets that are both closed and open.
  have h := Topology.P1_P2_P3_of_isClosed_isOpen (X := X) (A := A) h_closed h_open
  -- Extract the `P2` component from the conjunction.
  exact h.2.1