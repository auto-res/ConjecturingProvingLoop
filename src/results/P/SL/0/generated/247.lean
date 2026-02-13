

theorem closure_inter_interior_subset_inter_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A : Set X) ∩ interior (B : Set X)) ⊆
      closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- From `A ∩ interior B ⊆ A`, deduce membership in `closure A`.
  have hSubA :
      ((A : Set X) ∩ interior (B : Set X)) ⊆ (A : Set X) := by
    intro y hy; exact hy.1
  have hxA : x ∈ closure (A : Set X) := (closure_mono hSubA) hx
  -- From `A ∩ interior B ⊆ B`, deduce membership in `closure B`.
  have hSubB :
      ((A : Set X) ∩ interior (B : Set X)) ⊆ (B : Set X) := by
    intro y hy; exact
      (interior_subset : interior (B : Set X) ⊆ (B : Set X)) hy.2
  have hxB : x ∈ closure (B : Set X) := (closure_mono hSubB) hx
  exact And.intro hxA hxB