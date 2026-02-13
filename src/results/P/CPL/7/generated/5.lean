

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P3 A := by
  exact P3_of_P2 (P2_of_dense_interior h)

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P1 A := P1_of_P2 (P2_of_dense_interior h)

theorem P1_and_P2_implies_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P2 A → closure (interior A) = closure A := by
  intro hP1 hP2
  exact (P1_iff_closure_interior_eq_closure).1 hP1