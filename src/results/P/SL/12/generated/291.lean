

theorem Topology.closure_union_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    closure (A ∪ B ∪ C : Set X) = closure A ∪ closure B ∪ closure C := by
  simpa [Set.union_assoc] using
    calc
      closure (A ∪ B ∪ C : Set X)
          = closure (A ∪ B) ∪ closure C := by
              simpa [Set.union_assoc] using closure_union (A ∪ B) C
      _ = (closure A ∪ closure B) ∪ closure C := by
              simpa using
                congrArg (fun s : Set X => s ∪ closure C) (closure_union A B)