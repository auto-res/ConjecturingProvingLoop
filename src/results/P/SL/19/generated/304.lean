

theorem Topology.frontier_subset_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure A ∩ closure (Aᶜ) := by
  intro x hx
  have h₁ : x ∈ closure A :=
    (Topology.frontier_subset_closure (A := A)) hx
  have h₂ : x ∈ closure (Aᶜ) :=
    (Topology.frontier_subset_closure_compl (A := A)) hx
  exact And.intro h₁ h₂