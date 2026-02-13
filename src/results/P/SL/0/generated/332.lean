

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 D →
      Topology.P2 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  have hAB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  have hABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := A ∪ B) (B := C) hAB hC
  have hABCD : Topology.P2 (((A ∪ B) ∪ C) ∪ D) :=
    Topology.P2_union (X := X) (A := (A ∪ B) ∪ C) (B := D) hABC hD
  simpa [Set.union_assoc] using hABCD