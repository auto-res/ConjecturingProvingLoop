

theorem Topology.P1_union_interior_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (A ∪ interior A) := by
  intro hP1A
  have hP1Int : Topology.P1 (interior A) := P1_interior (A := A)
  exact Topology.P1_union (A := A) (B := interior A) hP1A hP1Int