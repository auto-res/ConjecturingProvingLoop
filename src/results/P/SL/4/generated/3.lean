

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  intro x hx
  -- `interior A` is contained in its closure
  have h_sub : interior A ⊆ closure (interior A) := by
    intro y hy
    exact subset_closure hy
  -- Taking interiors preserves the inclusion
  have h_inclusion : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h_sub
  -- Rewrite `interior (interior A)` and apply the inclusion to `x`
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  have hx'' : x ∈ interior (closure (interior A)) := h_inclusion hx'
  simpa using hx''