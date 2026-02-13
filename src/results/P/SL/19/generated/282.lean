

theorem Topology.closure_inter_closure_subset_inter_closure₁
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- First, show `x ∈ closure A`.
  have hxA : x ∈ closure A := by
    have hSub : (A ∩ closure B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hx
  -- Next, show `x ∈ closure B`.
  have hxB : x ∈ closure B := by
    have hSub : (A ∩ closure B : Set X) ⊆ closure B := fun y hy => hy.2
    -- This gives `x ∈ closure (closure B)`, which simplifies to `closure B`.
    have : x ∈ closure (closure B) := (closure_mono hSub) hx
    simpa [closure_closure] using this
  exact And.intro hxA hxB