

theorem P123_of_P1_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- Obtain `P2` and `P3` from the given assumptions.
  have hP2 : Topology.P2 A := Topology.P2_of_P1_and_open_closure (A := A) hP1 hOpenCl
  have hP3 : Topology.P3 A := Topology.P3_of_P1_and_open_closure (A := A) hP1 hOpenCl
  exact ⟨hP1, hP2, hP3⟩