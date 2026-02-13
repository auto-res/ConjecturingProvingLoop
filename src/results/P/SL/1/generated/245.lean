

theorem Topology.P3_inter_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (closure A) → Topology.P3 (closure B) → Topology.P3 (closure A ∩ closure B) := by
  intro hA hB
  have hA_closed : IsClosed (closure A) := isClosed_closure
  have hB_closed : IsClosed (closure B) := isClosed_closure
  exact
    Topology.P3_inter
      (A := closure A) (B := closure B)
      hA_closed hB_closed
      hA hB