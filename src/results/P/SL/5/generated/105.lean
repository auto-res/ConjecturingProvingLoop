

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P2 (X := X) A)
    (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) :
    Topology.P2 (X := X) (A ∪ B ∪ C) := by
  -- First, combine the properties for `A` and `B`.
  have hAB : Topology.P2 (X := X) (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Then, combine the result with `C`.
  have hABC : Topology.P2 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Re-associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABC