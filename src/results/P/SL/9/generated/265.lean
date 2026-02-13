

theorem Topology.frontier_subset_closureCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (Aᶜ) := by
  intro x hx
  -- Re-express `frontier A` as `closure A ∩ closure Aᶜ`.
  have h_inter : x ∈ closure (A : Set X) ∩ closure (Aᶜ) := by
    have h_eq := Topology.frontier_eq_inter_closure_closureCompl (A := A)
    simpa [h_eq] using hx
  -- Extract the membership in `closure Aᶜ`.
  exact h_inter.2