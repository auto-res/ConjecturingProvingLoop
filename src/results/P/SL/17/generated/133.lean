

theorem Topology.closure_interior_closure_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    closure (interior (closure A)) = closure A := by
  apply Set.Subset.antisymm
  ·
    exact Topology.closure_interior_closure_subset_closure (A := A)
  ·
    -- From `P1 A` we have `closure (interior A) = closure A`.
    have h_eq : closure (interior A) = closure A :=
      Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
    -- Use monotonicity of `closure ∘ interior` under the inclusion `A ⊆ closure A`.
    have h_inc : closure (interior A) ⊆ closure (interior (closure A)) :=
      Topology.closure_interior_mono
        (A := A) (B := closure A) (subset_closure : A ⊆ closure A)
    -- Rewrite using `h_eq` to get the desired inclusion.
    simpa [h_eq] using h_inc