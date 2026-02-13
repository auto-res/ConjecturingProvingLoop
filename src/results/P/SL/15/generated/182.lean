

theorem P1_subset_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior (closure A)) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  intro x hxA
  -- From `P1`, the point `x` lies in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Since `A ⊆ closure A`, we have `interior A ⊆ interior (closure A)`.
  have h_int_subset : interior A ⊆ interior (closure A) := by
    have : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono this
  -- Taking closures preserves inclusion.
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_cl