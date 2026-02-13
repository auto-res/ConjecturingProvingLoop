

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (A : Set X) → Topology.P1 (B : Set X) →
      Topology.P1 (closure (A ∪ B : Set X)) := by
  intro hA hB
  have hUnion : Topology.P1 (A ∪ B : Set X) :=
    Topology.P1_union (A := A) (B := B) hA hB
  exact Topology.P1_closure (A := A ∪ B) hUnion