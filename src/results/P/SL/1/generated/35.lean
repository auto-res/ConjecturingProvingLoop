

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- We show `closure (interior A)` is contained in `closure (interior (closure (interior A)))`.
  have hsubset : closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    -- First, monotonicity of `interior` gives the needed inclusion of interiors.
    have hInner : interior (interior A) ⊆ interior (closure (interior A)) := by
      apply interior_mono
      exact (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    -- Taking closures preserves inclusion.
    have hclosure : closure (interior (interior A)) ⊆
        closure (interior (closure (interior A))) := closure_mono hInner
    simpa [interior_interior] using hclosure
  exact hsubset hx