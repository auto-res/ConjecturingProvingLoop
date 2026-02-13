

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)` we obtain the desired inclusion
    -- between the closures.
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using this
  · intro h
    -- Unfold the definition of `P1`.
    dsimp [Topology.P1]
    intro x hxA
    -- First send `x` into `closure A`, then use the hypothesis `h`.
    have hx_cl : (x : X) ∈ closure A := subset_closure hxA
    exact h hx_cl