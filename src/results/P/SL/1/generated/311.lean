

theorem Topology.closure_inter_interior_subset_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B : Set X) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior A ∩ interior B` is contained in each individual interior.
  have hA : (interior A ∩ interior B : Set X) ⊆ interior A := by
    intro y hy; exact hy.1
  have hB : (interior A ∩ interior B : Set X) ⊆ interior B := by
    intro y hy; exact hy.2
  -- Apply monotonicity of `closure` to obtain the desired memberships.
  have hxA : x ∈ closure (interior A) := (closure_mono hA) hx
  have hxB : x ∈ closure (interior B) := (closure_mono hB) hx
  exact And.intro hxA hxB