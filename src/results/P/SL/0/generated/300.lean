

theorem closure_union_interiors_subset_union_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior (B : Set X)) ⊆
      closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) := by
  -- Step 1: Establish the inclusion before taking closures.
  have hSub :
      ((interior (A : Set X)) ∪ interior (B : Set X) : Set X) ⊆
        closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) := by
    intro x hx
    cases hx with
    | inl hxA => exact Or.inl (subset_closure hxA)
    | inr hxB => exact Or.inr (subset_closure hxB)
  -- Step 2: Apply `closure_mono`.
  have hIncl : closure (interior (A : Set X) ∪ interior (B : Set X)) ⊆
      closure (closure (interior (A : Set X)) ∪ closure (interior (B : Set X))) :=
    closure_mono hSub
  -- Step 3: The right‐hand side is already closed, so its closure is itself.
  have hClosedA : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have hClosedB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  have hClosed :
      IsClosed (closure (interior (A : Set X)) ∪ closure (interior (B : Set X))) :=
    hClosedA.union hClosedB
  simpa [hClosed.closure_eq] using hIncl