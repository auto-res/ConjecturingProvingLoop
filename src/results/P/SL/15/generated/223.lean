

theorem P1_and_dense_implies_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense A → Dense (interior A) := by
  intro hP1 hDenseA
  have hEquiv := (Topology.P1_dense_iff_denseInterior (X := X) (A := A)) hP1
  exact hEquiv.mp hDenseA