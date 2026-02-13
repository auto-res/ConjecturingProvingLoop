

theorem boundary_subset_closure_complement {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ interior (A : Set X) ⊆
      closure ((Aᶜ) : Set X) := by
  intro x hx
  -- Identify the boundary with the intersection of the two closures.
  have hEq := boundary_eq_closure_inter_closure_compl (A := A)
  -- Reinterpret `hx` via this equality.
  have hx' :
      (x : X) ∈ closure (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
    simpa [hEq] using hx
  exact hx'.2