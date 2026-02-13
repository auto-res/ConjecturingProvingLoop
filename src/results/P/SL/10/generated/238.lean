

theorem Topology.closure_union_closure_left_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ B) = closure (A ∪ B) := by
  calc
    closure (closure A ∪ B)
        = closure (B ∪ closure A) := by
          simpa [Set.union_comm]
    _ = closure (B ∪ A) := by
          simpa using
            Topology.closure_union_closure_right_eq_closure_union
              (X := X) (A := B) (B := A)
    _ = closure (A ∪ B) := by
          simpa [Set.union_comm]