

theorem Topology.P1_closure_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = closure (interior A)) :
    Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  intro x hx
  -- Rewrite `x ∈ closure A` using the given equality.
  have hx' : x ∈ closure (interior A) := by
    simpa [h] using hx
  -- Show that this closure is contained in `closure (interior (closure A))`.
  have hsubset : closure (interior A) ⊆ closure (interior (closure A)) := by
    have hinner : interior A ⊆ interior (closure A) := by
      apply interior_mono
      exact (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono hinner
  exact hsubset hx'