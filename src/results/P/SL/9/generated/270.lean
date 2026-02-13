

theorem Topology.frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    frontier (A : Set X) ⊆ closure B := by
  intro x hx
  -- From `hx` we obtain `x ∈ closure A`.
  have hx_clA : x ∈ closure (A : Set X) := hx.1
  -- Monotonicity of `closure` gives `closure A ⊆ closure B`.
  have h_closure_mono : closure (A : Set X) ⊆ closure B := closure_mono hAB
  -- Hence `x ∈ closure B`.
  exact h_closure_mono hx_clA