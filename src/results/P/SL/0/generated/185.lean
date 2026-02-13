

theorem P3_implies_P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (interior (A : Set X)) := by
  intro _
  simpa using (Topology.interior_has_P1 (X := X) (A := A))