

theorem P2_and_interior_closure_eq_empty_implies_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (A : Set X)) = ∅ → A = (∅ : Set X) := by
  intro hP2 hIntEmpty
  -- From `P2` we have the inclusion `A ⊆ interior (closure A)`.
  have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) :=
    (Topology.P2_implies_subset_interior_closure (X := X) (A := A)) hP2
  -- But `interior (closure A)` is empty by hypothesis, hence so is `A`.
  have hSubEmpty : (A : Set X) ⊆ (∅ : Set X) := by
    simpa [hIntEmpty] using hSub
  exact Set.Subset.antisymm hSubEmpty (Set.empty_subset _)