

theorem Topology.P3_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) :
    Topology.P3 (A ∪ B ∪ C) := by
  -- First, obtain `P3` for `A ∪ B`.
  have hAB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P3 ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Rewrite to the desired (left-associative) form.
  simpa [Set.union_assoc] using hABC