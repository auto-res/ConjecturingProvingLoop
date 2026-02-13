

theorem closure_interior_union_interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∪ interior (closure A) ⊆
      closure (interior (closure A)) := by
  intro x hx
  cases hx with
  | inl hx₁ =>
      -- `closure (interior A)` is contained in `closure (interior (closure A))`
      have h :=
        closure_interior_subset_closure_interior_closure
          (X := X) (A := A) hx₁
      exact h
  | inr hx₂ =>
      -- `interior (closure A)` is evidently contained in its own closure
      have h_sub :
          interior (closure A) ⊆ closure (interior (closure A)) := by
        intro y hy
        exact subset_closure hy
      exact h_sub hx₂