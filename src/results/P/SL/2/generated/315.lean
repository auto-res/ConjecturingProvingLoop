

theorem Topology.closure_frontier_subset_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier (A : Set X)) ⊆
      closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  intro x hx
  -- `frontier A ⊆ closure A`
  have h₁ :
      (frontier (A : Set X) : Set X) ⊆ closure (A : Set X) :=
    Topology.frontier_subset_closure (A := A)
  -- Taking closures preserves inclusions.
  have h₁' :
      closure (frontier (A : Set X)) ⊆ closure (closure (A : Set X)) :=
    closure_mono h₁
  -- Simplify the right‐hand side.
  have hx₁ : x ∈ closure (A : Set X) := by
    have : x ∈ closure (closure (A : Set X)) := h₁' hx
    simpa [closure_closure] using this
  -- `frontier A ⊆ closure Aᶜ`
  have h₂ :
      (frontier (A : Set X) : Set X) ⊆ closure (Aᶜ : Set X) :=
    Topology.frontier_subset_closure_compl (A := A)
  -- Again, take closures.
  have h₂' :
      closure (frontier (A : Set X)) ⊆ closure (closure (Aᶜ : Set X)) :=
    closure_mono h₂
  have hx₂ : x ∈ closure (Aᶜ : Set X) := by
    have : x ∈ closure (closure (Aᶜ : Set X)) := h₂' hx
    simpa [closure_closure] using this
  exact And.intro hx₁ hx₂