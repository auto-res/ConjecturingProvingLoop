

theorem Topology.P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First, unite the three sets `A`, `B`, and `C`.
  have hABC : Topology.P2 (X := X) (A ∪ B ∪ C) :=
    Topology.P2_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Next, union the resulting set with `D`.
  have hABCD : Topology.P2 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P2_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Rewrite the unions to match the desired normal form.
  simpa [Set.union_assoc, Set.union_left_comm, Set.union_right_comm] using hABCD