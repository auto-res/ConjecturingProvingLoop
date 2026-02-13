

theorem Topology.P1_iff_closure_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)` we get the desired inclusion by taking closures.
    have h : (A : Set X) ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using this
  · intro hSub
    -- Use the assumed inclusion and the fact that `x ∈ A` implies `x ∈ closure A`.
    dsimp [Topology.P1] at *
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    exact hSub hx_closure