

theorem P2_and_interior_eq_empty_implies_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → interior (A : Set X) = ∅ → A = (∅ : Set X) := by
  intro hP2 hIntEmpty
  dsimp [Topology.P2] at hP2
  -- Compute the target set: `interior (closure (interior A)) = ∅`.
  have hTarget : interior (closure (interior (A : Set X))) = (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty, interior_empty]
  -- `P2` implies `A ⊆ interior (closure (interior A))`, hence `A ⊆ ∅`.
  have hSubset : (A : Set X) ⊆ (∅ : Set X) := by
    have h : (A : Set X) ⊆ interior (closure (interior (A : Set X))) := hP2
    simpa [hTarget] using h
  -- Conclude that `A = ∅`.
  exact Set.Subset.antisymm hSubset (Set.empty_subset _)