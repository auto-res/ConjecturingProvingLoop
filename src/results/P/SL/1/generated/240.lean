

theorem Topology.P2_inter_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (closure A) → Topology.P2 (closure B) → Topology.P2 (closure A ∩ closure B) := by
  intro hA hB
  have hA_closed : IsClosed (closure A) := isClosed_closure
  have hB_closed : IsClosed (closure B) := isClosed_closure
  exact
    Topology.P2_inter
      (A := closure A) (B := closure B)
      hA_closed hB_closed
      hA hB