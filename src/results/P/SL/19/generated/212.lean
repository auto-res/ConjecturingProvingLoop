

theorem Topology.frontier_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- From `hx` we know `x ∈ closure (A ∩ B)`.
  have hxClos : x ∈ closure (A ∩ B) := hx.1
  -- Deduce `x ∈ closure A` since `A ∩ B ⊆ A`.
  have hxA : x ∈ closure A := by
    have hSub : (A ∩ B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hxClos
  -- Deduce `x ∈ closure B` since `A ∩ B ⊆ B`.
  have hxB : x ∈ closure B := by
    have hSub : (A ∩ B : Set X) ⊆ B := fun y hy => hy.2
    exact (closure_mono hSub) hxClos
  exact And.intro hxA hxB