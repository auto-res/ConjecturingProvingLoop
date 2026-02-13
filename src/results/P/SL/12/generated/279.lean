

theorem Topology.P1_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First, combine `A`, `B`, and `C`.
  have hABC : Topology.P1 (X := X) (A ∪ B ∪ C) :=
    Topology.P1_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Then, union the result with `D`.
  have hABCD : Topology.P1 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P1_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Reassociate the unions to match the desired form.
  simpa [Set.union_assoc] using hABCD