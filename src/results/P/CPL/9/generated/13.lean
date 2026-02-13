

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) (hD : Topology.P2 (A := D)) : Topology.P2 (A := A ∪ B ∪ C ∪ D) := by
  -- First, combine `A`, `B`, and `C`
  have hABC : P2 (A ∪ B ∪ C) :=
    P2_union_three (A := A) (B := B) (C := C) hA hB hC
  -- Then add `D`
  simpa [Set.union_assoc] using
    union_P2 (A := A ∪ B ∪ C) (B := D) hABC hD