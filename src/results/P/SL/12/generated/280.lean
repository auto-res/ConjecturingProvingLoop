

theorem Topology.P3_union_four {X : Type*} [TopologicalSpace X]
    {A B C D : Set X}
    (hA : Topology.P3 (X := X) A)
    (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C)
    (hD : Topology.P3 (X := X) D) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First union `A` and `B`.
  have hAB : Topology.P3 (X := X) (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Then add `C`.
  have hABC : Topology.P3 (X := X) (A ∪ B ∪ C) := by
    -- `(A ∪ B ∪ C)` is definitionally `(A ∪ B) ∪ C`.
    have : Topology.P3 (X := X) ((A ∪ B) ∪ C) :=
      Topology.P3_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
    simpa [Set.union_assoc] using this
  -- Finally, add `D`.
  have hABCD : Topology.P3 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P3_union (X := X) (A := (A ∪ B ∪ C)) (B := D) hABC hD
  -- Rewrite to the desired union ordering.
  simpa [Set.union_assoc] using hABCD