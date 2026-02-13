

theorem Topology.closure_inter_closure_subset_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- First show `x ∈ closure A`.
  have hxClosA : x ∈ closure A := by
    have hSub : (A ∩ closure B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hx
  -- Then show `x ∈ closure B`.
  have hxClosB : x ∈ closure B := by
    have hSub : (A ∩ closure B : Set X) ⊆ closure B := fun y hy => hy.2
    have hx' : x ∈ closure (closure B) := (closure_mono hSub) hx
    simpa [closure_closure] using hx'
  exact And.intro hxClosA hxClosB