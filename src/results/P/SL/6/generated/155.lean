

theorem P3_inter_of_P3_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hP3A : Topology.P3 (A : Set X)) (hP3B : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- `A` and `B` are open because they are closed and satisfy `P3`.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.open_of_P3_closed (A := A) hA_closed) hP3A
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.open_of_P3_closed (A := B) hB_closed) hP3B
  -- The intersection of open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Open sets satisfy `P3`.
  exact Topology.open_satisfies_P3 (A := A ∩ B) hOpenInter