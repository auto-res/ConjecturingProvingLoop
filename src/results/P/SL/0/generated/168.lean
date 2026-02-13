

theorem P3_and_interior_closure_eq_empty_implies_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → interior (closure (A : Set X)) = ∅ → A = (∅ : Set X) := by
  intro hP3 hIntEmpty
  dsimp [Topology.P3] at hP3
  -- `P3` gives `A ⊆ interior (closure A)`, which is empty by hypothesis.
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    have : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    simpa [hIntEmpty] using this
  -- Conclude that `A = ∅`.
  exact Set.Subset.antisymm hSub (Set.empty_subset _)