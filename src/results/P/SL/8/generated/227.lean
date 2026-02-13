

theorem P3_closure_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P2 (closure A) := by
  intro hP3
  exact (Topology.P3_closure_iff_P2_closure (X := X) (A := A)).1 hP3