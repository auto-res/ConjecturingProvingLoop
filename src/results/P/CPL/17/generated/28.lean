

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P2 A → Topology.P2 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP2A
  have hP2_univ : Topology.P2 (Set.univ : Set Y) := P2_univ (X := Y)
  simpa using (P2_prod (A := A) (B := (Set.univ : Set Y)) hP2A hP2_univ)