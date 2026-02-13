

theorem P3_closure_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P2 (closure A) := by
  intro hP3
  exact ((Topology.P2_iff_P3_closure (A := A)).mpr hP3)