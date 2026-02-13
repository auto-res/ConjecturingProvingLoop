

theorem closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ interior (A : Set X) = closure (A : Set X) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hCl => exact hCl
    | inr hInt =>
        have hsubset : (interior (A : Set X) : Set X) ⊆ closure (A : Set X) :=
          interior_subset_closure (X := X) (A := A)
        exact hsubset hInt
  · intro hx
    exact Or.inl hx