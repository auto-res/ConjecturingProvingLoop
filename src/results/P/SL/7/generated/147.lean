

theorem Topology.interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) : (interior A).Nonempty := by
  -- `P2` implies `P1`.
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  -- Use the existing result for `P1`.
  exact Topology.interior_nonempty_of_P1 (A := A) hP1 hA