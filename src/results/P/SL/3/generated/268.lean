

theorem boundary_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) →
      closure (A : Set X) \ interior (A : Set X) =
        (interior (A : Set X))ᶜ := by
  intro hDense
  classical
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxNotInt
    have hxCl : (x : X) ∈ closure (A : Set X) := by
      simpa [hDense] using (Set.mem_univ (x : X))
    exact And.intro hxCl hxNotInt