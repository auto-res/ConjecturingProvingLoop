

theorem Topology.interior_closure_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure A ∩ closure B ⊆ closure A`
  have hsubA : closure A ∩ closure B ⊆ closure A := by
    intro y hy
    exact hy.1
  -- `closure A ∩ closure B ⊆ closure B`
  have hsubB : closure A ∩ closure B ⊆ closure B := by
    intro y hy
    exact hy.2
  -- Use monotonicity of `interior` to upgrade the membership.
  have hxA : x ∈ interior (closure A) := (interior_mono hsubA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono hsubB) hx
  exact And.intro hxA hxB