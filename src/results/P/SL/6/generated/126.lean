

theorem closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (A : Set X)))) =
      closure (interior A) := by
  apply Set.Subset.antisymm
  · -- `⊆` direction
    have h₁ :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior A) := by
      -- `interior s ⊆ s` with `s = closure (interior A)`
      simpa using (interior_subset :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior (A : Set X)))
    simpa [closure_closure] using (closure_mono h₁)
  · -- `⊇` direction
    have h₂ : interior A ⊆ interior (closure (interior A)) := by
      have hSub : (interior A : Set X) ⊆ closure (interior A) :=
        subset_closure
      have h := interior_mono hSub
      simpa [interior_interior] using h
    simpa using (closure_mono h₂)