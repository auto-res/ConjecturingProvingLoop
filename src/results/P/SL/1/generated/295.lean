

theorem Topology.closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure (interior B) := by
  intro x hx
  -- `A ∩ interior B` is contained in `A`.
  have hA : (A ∩ interior B : Set X) ⊆ A := by
    intro y hy; exact hy.1
  -- `A ∩ interior B` is also contained in `interior B`.
  have hB : (A ∩ interior B : Set X) ⊆ interior B := by
    intro y hy; exact hy.2
  -- Taking closures preserves inclusions.
  have hxA : x ∈ closure A := (closure_mono hA) hx
  have hxB : x ∈ closure (interior B) := (closure_mono hB) hx
  exact And.intro hxA hxB