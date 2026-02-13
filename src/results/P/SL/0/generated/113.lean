

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  simpa using ((Topology.univ_has_all_Ps (X := X)).2.2)