

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2] at *
  intro x hxA
  -- From `P3` we know that `x ∈ interior (closure A)`.
  have hx_int_clA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- `P1` yields `closure A ⊆ closure (interior A)`.
  have h_closure_subset :
      closure (A : Set X) ⊆ closure (interior A) :=
    Topology.P1_closure_subset (X := X) (A := A) hP1
  -- Monotonicity of `interior` then gives the required inclusion.
  have h_int_subset :
      interior (closure (A : Set X)) ⊆ interior (closure (interior A)) :=
    interior_mono h_closure_subset
  exact h_int_subset hx_int_clA