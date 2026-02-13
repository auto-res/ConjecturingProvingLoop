

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  simpa using (Topology.empty_has_all_Ps (X := X)).1