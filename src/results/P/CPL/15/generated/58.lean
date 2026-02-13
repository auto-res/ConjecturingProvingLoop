

theorem P1_iterated_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (closure (interior A))) := by
  simpa [closure_closure] using (P1_closure_interior (A := A))

theorem P1_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (A ∪ interior A) := by
  -- Since `interior A ⊆ A`, the union is just `A`.
  have hEq : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA     => exact hA
      | inr hIntA  => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  -- Rewrite with this equality and apply the hypothesis `hA`.
  simpa [hEq] using hA