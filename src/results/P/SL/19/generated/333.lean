

theorem Topology.closure_diff_union_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ (A ∪ frontier A) = (∅ : Set X) := by
  have hUnion : (A : Set X) ∪ frontier A = closure A :=
    (Topology.closure_eq_self_union_frontier (A := A)).symm
  calc
    closure A \ (A ∪ frontier A)
        = closure A \ closure A := by
          simpa [hUnion]
    _ = (∅ : Set X) := by
          simp