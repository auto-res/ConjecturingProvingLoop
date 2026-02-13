

theorem Topology.interior_closure_inter_subset_inter_interior_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    -- `closure A ∩ closure B` is included in `closure A`
    have hSub : (closure A ∩ closure B : Set X) ⊆ closure A := by
      intro y hy; exact hy.1
    exact (interior_mono hSub) hx
  have hxB : x ∈ interior (closure B) := by
    -- `closure A ∩ closure B` is included in `closure B`
    have hSub : (closure A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact (interior_mono hSub) hx
  exact And.intro hxA hxB