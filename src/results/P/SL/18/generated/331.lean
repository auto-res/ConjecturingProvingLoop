

theorem interior_closure_inter_closure_left_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ closure (B : Set X) : Set X)) ⊆
      interior (closure (A : Set X)) := by
  -- `closure` is monotone with respect to set inclusion.
  have h :
      closure (A ∩ closure (B : Set X) : Set X) ⊆ closure (A : Set X) := by
    apply closure_mono
    intro x hx
    exact hx.1
  -- Taking interiors preserves inclusions.
  exact interior_mono h