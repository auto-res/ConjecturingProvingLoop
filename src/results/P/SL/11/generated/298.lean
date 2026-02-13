

theorem closure_union_closure_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ closure B : Set X) = closure (A ∪ B) := by
  have h₁ :
      closure (closure A ∪ closure B : Set X) = closure (A ∪ closure B) := by
    simpa using
      (closure_union_closure_left (A := A) (B := closure B))
  have h₂ : closure (A ∪ closure B : Set X) = closure (A ∪ B) :=
    closure_union_closure_right (A := A) (B := B)
  simpa using (h₁.trans h₂)