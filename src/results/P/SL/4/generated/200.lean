

theorem P2_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 (A ∪ interior B) := by
  intro hP2A
  have hP2IntB : Topology.P2 (interior B) :=
    Topology.P2_interior (X := X) (A := B)
  have h := Topology.P2_union (A := A) (B := interior B) hP2A hP2IntB
  simpa using h