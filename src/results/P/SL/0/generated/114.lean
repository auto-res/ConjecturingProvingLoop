

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  simpa using ((Topology.univ_has_all_Ps (X := X)).1)