

theorem P1_P2_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  simpa using
    (Topology.isOpen_imp_P1_P2_P3 (A := (∅ : Set X)) isOpen_empty)