

theorem interior_closure_union_eq_union_closure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    interior (closure ((A ∪ B) : Set X)) =
      interior (closure (A : Set X) ∪ closure (B : Set X)) := by
  have h := closure_union_eq_union_closure (A := A) (B := B)
  simpa using congrArg interior h