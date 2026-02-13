

theorem interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      interior (closure (A : Set X)) ⊆ closure (interior (A : Set X)) := by
  intro hP1
  intro x hx
  -- `P1` gives equality of the two closures.
  have hEq := closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Rewrite `hx` using this equality.
  have hx' : (x : X) ∈ interior (closure (interior (A : Set X))) := by
    simpa [hEq] using hx
  -- Use the fact that `interior S ⊆ S`.
  exact (interior_subset (s := closure (interior (A : Set X)))) hx'