

theorem Topology.closure_interior_union_three_eq_closure_union_interiors
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ∪ closure (interior C) =
      closure (interior A ∪ interior B ∪ interior C) := by
  -- First, regroup the unions for convenient rewriting.
  calc
    closure (interior A) ∪ closure (interior B) ∪ closure (interior C)
        = closure (interior A) ∪ (closure (interior B) ∪ closure (interior C)) := by
          simp [Set.union_assoc]
    _ = closure (interior A) ∪ closure (interior B ∪ interior C) := by
          -- Use the two‐set equality on the last two terms.
          simpa using
            congrArg (fun s : Set X ↦ closure (interior A) ∪ s)
              (closure_union (interior (B : Set X)) (interior C))
    _ = closure (interior A ∪ (interior B ∪ interior C)) := by
          -- Apply the two‐set equality again.
          simpa using
            (closure_union (interior (A : Set X)) (interior B ∪ interior C)).symm
    _ = closure (interior A ∪ interior B ∪ interior C) := by
          simpa [Set.union_assoc]