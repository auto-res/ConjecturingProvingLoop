

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  -- `interior A` is contained in `closure (interior A)`
  have h_sub : interior A ⊆ closure (interior A) := by
    intro y hy
    exact subset_closure hy
  -- Taking interiors preserves the inclusion
  have h_mono : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h_sub
  -- Rewrite `interior (interior A)` and apply the inclusion to `x`
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  exact h_mono hx'