

theorem interior_closure_nonempty_of_nonempty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxIntA⟩
  have hxIntClos : x ∈ interior (closure (A : Set X)) :=
    (interior_subset_interior_closure (A := A)) hxIntA
  exact ⟨x, hxIntClos⟩