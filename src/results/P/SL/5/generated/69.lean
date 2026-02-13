

theorem interior_closure_nonempty_of_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (interior (A : Set X)).Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  rcases h with ⟨x, hx⟩
  have hx' : x ∈ interior (closure (A : Set X)) :=
    (interior_subset_interior_closure (X := X) (A := A)) hx
  exact ⟨x, hx'⟩