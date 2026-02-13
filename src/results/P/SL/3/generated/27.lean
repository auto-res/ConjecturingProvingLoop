

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  -- Using the equality of closures granted by `P1`
  have hEq := closure_eq_closure_interior_of_P1 (A := A) hA
  have hx_intA : (x : X) ∈ closure (interior (A : Set X)) := by
    simpa [hEq] using hx
  -- Monotonicity of closure with respect to set inclusion
  have h_subset :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
    apply closure_mono
    exact interior_subset_interior_closure (A := A)
  exact h_subset hx_intA