

theorem P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (closure (A : Set X))) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- Every point of `A` lies in `closure A`.
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
  -- Apply the `P2` hypothesis for `closure A`.
  have hx_int :
      x ∈ interior (closure (interior (closure (A : Set X)))) :=
    h hx_closure
  -- Use monotonicity of `interior` to pass to `interior (closure A)`.
  have h_subset :
      interior (closure (interior (closure (A : Set X))))
        ⊆ interior (closure (A : Set X)) := by
    have h_closure :
        closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
      Topology.closure_interior_closure_subset_closure (X := X) (A := A)
    exact interior_mono h_closure
  exact h_subset hx_int