

theorem P2_implies_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P2 (interior A) := by
  intro _
  simpa using (Topology.interior_has_P2 (X := X) (A := A))