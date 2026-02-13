

theorem Topology.closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior (B : Set X)) ⊆
      closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- `A ∩ interior B ⊆ A`
  have hSubA : (A ∩ interior (B : Set X) : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  -- `A ∩ interior B ⊆ B` (because `interior B ⊆ B`)
  have hSubB : (A ∩ interior (B : Set X) : Set X) ⊆ B := by
    intro y hy
    exact (interior_subset : interior (B : Set X) ⊆ B) hy.2
  -- Taking closures preserves inclusions.
  have hxA : x ∈ closure (A : Set X) := (closure_mono hSubA) hx
  have hxB : x ∈ closure (B : Set X) := (closure_mono hSubB) hx
  exact And.intro hxA hxB