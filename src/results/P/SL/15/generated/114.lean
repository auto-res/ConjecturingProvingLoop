

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)` we deduce the desired inclusion of closures.
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using h
  · intro hSubset
    -- Use `closure` monotonicity together with `A ⊆ closure A`.
    dsimp [Topology.P1]
    intro x hx
    have hx_cl : x ∈ closure A := subset_closure hx
    exact hSubset hx_cl