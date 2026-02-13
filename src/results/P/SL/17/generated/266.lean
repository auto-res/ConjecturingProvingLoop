

theorem Topology.interior_subset_closure_interior_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior A ⊆ closure (interior B) := by
  intro x hx
  -- Step 1: use monotonicity of `interior` under `hAB`
  have hx_intB : x ∈ interior B := (interior_mono hAB) hx
  -- Step 2: every set is contained in the closure of itself
  exact (subset_closure : interior B ⊆ closure (interior B)) hx_intB