

theorem clopen_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- We can obtain all three properties directly from the fact that `A` is open.
  exact Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen