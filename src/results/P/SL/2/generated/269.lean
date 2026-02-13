

theorem Topology.dense_subset_closed_eq_univ {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hDense : Dense (A : Set X)) (hClosed : IsClosed (B : Set X))
    (hSub : (A : Set X) ⊆ B) : (B : Set X) = (Set.univ : Set X) := by
  -- From density of `A` we have `closure A = univ`.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Since `A ⊆ B` and `B` is closed, `closure A ⊆ B`.
  have hClosureASubB : closure (A : Set X) ⊆ B := by
    have : closure (A : Set X) ⊆ closure (B : Set X) := closure_mono hSub
    simpa [hClosed.closure_eq] using this
  -- Hence `univ ⊆ B`.
  have hUnivSubB : (Set.univ : Set X) ⊆ B := by
    simpa [hClosureA] using hClosureASubB
  -- Combine the inclusions to obtain the equality.
  exact Set.Subset.antisymm (by
    intro x _
    simp) hUnivSubB