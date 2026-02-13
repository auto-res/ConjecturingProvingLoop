

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (closure (A ∪ B)) := by
  intro hA hB
  have h_union : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  have h_closure : Topology.P1 (closure (A ∪ B)) :=
    Topology.P1_implies_P1_closure (X := X) (A := A ∪ B) h_union
  simpa using h_closure