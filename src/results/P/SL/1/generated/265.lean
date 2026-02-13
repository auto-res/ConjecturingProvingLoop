

theorem Topology.closure_inter_subset_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure B := by
  -- `A ∩ B` is contained in `B`.
  have hsubset : (A ∩ B : Set X) ⊆ B := by
    intro x hx
    exact hx.2
  -- Taking closures preserves this inclusion.
  exact closure_mono hsubset