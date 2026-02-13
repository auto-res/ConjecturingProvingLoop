

theorem P2_closure_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3
  simpa using ((P3_closure_iff_P2_closure (A := A)).1 hP3)