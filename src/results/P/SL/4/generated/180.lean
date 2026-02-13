

theorem interior_inter_closure_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `A ∩ closure B` is contained in `closure A`
  have hSubA : (A ∩ closure B : Set X) ⊆ closure A := by
    intro y hy
    exact subset_closure hy.1
  -- `A ∩ closure B` is also contained in `closure B`
  have hSubB : (A ∩ closure B : Set X) ⊆ closure B := by
    intro y hy
    exact hy.2
  -- Taking interiors preserves these inclusions
  have hxA : x ∈ interior (closure A) := (interior_mono hSubA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono hSubB) hx
  exact And.intro hxA hxB