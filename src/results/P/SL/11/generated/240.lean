

theorem interior_closure_empty_iff_empty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    interior (closure A) = (∅ : Set X) ↔ A = ∅ := by
  constructor
  · intro hInt
    -- `P3` gives `A ⊆ interior (closure A)`.
    have hSub : (A : Set X) ⊆ interior (closure A) := hP3
    -- Combining with `hInt`, we obtain `A ⊆ ∅`.
    have hSubEmpty : (A : Set X) ⊆ (∅ : Set X) := by
      simpa [hInt] using hSub
    -- Hence `A = ∅`.
    exact Set.Subset.antisymm hSubEmpty (Set.empty_subset _)
  · intro hA
    -- If `A = ∅`, then its closure is `∅`, and so is the interior.
    simpa [hA, closure_empty, interior_empty]