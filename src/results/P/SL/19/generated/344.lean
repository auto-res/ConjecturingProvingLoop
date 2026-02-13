

theorem Topology.frontier_subset_closure_union_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure A ∪ closure (Aᶜ) := by
  intro x hx
  have h₁ : x ∈ closure A :=
    (Topology.frontier_subset_closure (A := A)) hx
  exact Or.inl h₁