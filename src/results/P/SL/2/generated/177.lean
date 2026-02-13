

theorem Topology.interior_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = (Set.univ : Set X) ↔ (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- Since `interior A ⊆ A`, the equality `interior A = univ` forces `univ ⊆ A`.
    have hSub : (Set.univ : Set X) ⊆ (A : Set X) := by
      intro x hx
      have : (x : X) ∈ interior (A : Set X) := by
        simpa [hInt] using hx
      exact interior_subset this
    -- The reverse inclusion `A ⊆ univ` is always true.
    have hSub' : (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x hx
      simp
    exact subset_antisymm hSub' hSub
  · intro hA
    simpa [hA, interior_univ] using rfl