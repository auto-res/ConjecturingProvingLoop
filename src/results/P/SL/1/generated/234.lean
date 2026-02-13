

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `A ∩ B` is contained in `A`, hence its closure is contained in `closure A`.
  have hA : (A ∩ B : Set X) ⊆ A := by
    intro y hy; exact hy.1
  have hxA : x ∈ closure A := (closure_mono hA) hx
  -- Similarly for `B`.
  have hB : (A ∩ B : Set X) ⊆ B := by
    intro y hy; exact hy.2
  have hxB : x ∈ closure B := (closure_mono hB) hx
  exact And.intro hxA hxB