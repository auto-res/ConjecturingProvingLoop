

theorem P2_inter_of_P2_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hP2A : Topology.P2 (A : Set X)) (hP2B : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- From closedness and `P2`, infer that both `A` and `B` are open.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P2_iff_open_of_closed (A := A) hA_closed).1 hP2A
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P2_iff_open_of_closed (A := B) hB_closed).1 hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Open sets satisfy `P2`.
  exact Topology.open_satisfies_P2 (A := A ∩ B) hOpenInter