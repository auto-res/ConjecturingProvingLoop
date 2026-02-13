

theorem Topology.interior_inter_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior (A ∪ B) := by
  -- `interior` is monotone with respect to set inclusion.
  refine interior_mono ?_
  intro x hx
  exact Or.inl hx.1