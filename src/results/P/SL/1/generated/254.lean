

theorem Topology.dense_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Dense A) (hB : Dense B) : Dense (A ∪ B) := by
  -- Compute the closure of the union using `closure_union`.
  have hclosure : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    calc
      closure (A ∪ B : Set X)
          = closure A ∪ closure B := by
            simpa [closure_union]
      _ = (Set.univ : Set X) := by
            simp [hA.closure_eq, hB.closure_eq]
  -- Translate the closure equality back into a density statement.
  exact (dense_iff_closure_eq).2 hclosure