

theorem Topology.P1_iff_closure_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `P1`, we have `A ⊆ closure (interior A)`.
    -- Taking closures preserves inclusions and yields the desired result.
    have h : (A : Set X) ⊆ closure (interior A) := hP1
    simpa [closure_closure] using closure_mono h
  · intro hClosure
    -- To prove `P1`, start with any `x ∈ A`.
    dsimp [Topology.P1] at *
    intro x hxA
    -- Since `A ⊆ closure A`, we first place `x` in `closure A`,
    -- then use the assumed inclusion.
    have hx_closure : x ∈ closure A := Set.subset_closure hxA
    exact hClosure hx_closure