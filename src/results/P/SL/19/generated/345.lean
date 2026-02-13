

theorem Topology.frontier_eq_frontier_inter_closure_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) = frontier A ∩ closure (Aᶜ) := by
  ext x
  constructor
  · intro hx
    have h₁ : x ∈ closure (Aᶜ) :=
      (Topology.frontier_subset_closure_compl (A := A)) hx
    exact And.intro hx h₁
  · intro hx
    exact hx.1