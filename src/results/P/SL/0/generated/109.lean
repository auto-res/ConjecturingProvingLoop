

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  simpa using ((Topology.univ_has_all_Ps (X := X)).2.1)