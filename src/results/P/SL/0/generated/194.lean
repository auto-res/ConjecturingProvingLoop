

theorem interior_inter_closures_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((closure (A : Set X)) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- `closure A ∩ closure B` is contained in each of the closures separately.
  have hSubA :
      (closure (A : Set X) ∩ closure (B : Set X)) ⊆ closure (A : Set X) := by
    intro y hy; exact hy.1
  have hSubB :
      (closure (A : Set X) ∩ closure (B : Set X)) ⊆ closure (B : Set X) := by
    intro y hy; exact hy.2
  -- Apply monotonicity of `interior` to both inclusions.
  have hxA : x ∈ interior (closure (A : Set X)) := (interior_mono hSubA) hx
  have hxB : x ∈ interior (closure (B : Set X)) := (interior_mono hSubB) hx
  exact And.intro hxA hxB