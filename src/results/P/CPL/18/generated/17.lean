

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∪ B ∪ C) := by
  have hAB : Topology.P2 (A ∪ B) := P2_union (X := X) (A := A) (B := B) hA hB
  simpa [Set.union_assoc] using
    (P2_union (X := X) (A := A ∪ B) (B := C) hAB hC)

theorem exists_P2_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, U ⊆ A ∧ Topology.P2 U := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  simpa using (P2_empty (X := X))