

theorem P1_and_interior_eq_empty_implies_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (A : Set X) = ∅ → A = (∅ : Set X) := by
  intro hP1 hIntEmpty
  dsimp [Topology.P1] at hP1
  -- From `P1`, we know `A ⊆ closure (interior A)`.
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    have : (A : Set X) ⊆ closure (interior (A : Set X)) := hP1
    simpa [hIntEmpty, closure_empty] using this
  exact Set.Subset.antisymm hSub (Set.empty_subset _)