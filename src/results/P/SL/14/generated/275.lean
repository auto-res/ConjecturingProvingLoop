

theorem Topology.dense_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Dense (A : Set X)) (hB : Dense (B : Set X)) (hC : Dense (C : Set X)) :
    Dense (A ∪ B ∪ C : Set X) := by
  -- First, the union `A ∪ B` is dense.
  have hAB : Dense (A ∪ B : Set X) :=
    Topology.dense_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Dense ((A ∪ B) ∪ C : Set X) :=
    Topology.dense_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Rewrite to the desired (left‐associative) form.
  simpa [Set.union_assoc] using hABC