

theorem interior_closure_inter_left_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ closure (B : Set X)) : Set X)) ⊆
      interior (closure (B : Set X)) := by
  -- `A ∩ closure B` is contained in `closure B`.
  have hSub : (A ∩ closure (B : Set X) : Set X) ⊆ closure (B : Set X) := by
    intro x hx
    exact hx.2
  -- Apply `closure_mono` followed by `interior_mono`.
  simpa [closure_closure] using
    (interior_mono (closure_mono hSub))