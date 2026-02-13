

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  simpa using (Topology.empty_has_all_Ps (X := X)).2.1