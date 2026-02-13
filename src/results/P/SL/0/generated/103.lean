

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  exact (Topology.empty_has_all_Ps (X := X)).2.2