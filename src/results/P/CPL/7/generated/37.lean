

theorem P2_prod_univ {X : Type*} [TopologicalSpace X] {A : Set X} {Y : Type*} [TopologicalSpace Y] (h : Topology.P2 A) : Topology.P2 (A ×ˢ (Set.univ : Set Y)) := by
  have hUniv : Topology.P2 (Set.univ : Set Y) := P2_univ
  simpa using (P2_prod (A := A) (B := (Set.univ : Set Y)) h hUniv)