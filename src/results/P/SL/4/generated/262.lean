

theorem frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    frontier (A : Set X) ⊆ closure B := by
  intro x hx
  -- `hx` gives `x ∈ closure A`
  have hx_closureA : x ∈ closure A := hx.1
  -- Monotonicity of `closure` upgrades the inclusion
  have h_mono : closure A ⊆ closure B := closure_mono hAB
  exact h_mono hx_closureA