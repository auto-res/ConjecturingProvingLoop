

theorem interior_closure_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ closure B := by
  -- First, upgrade the inclusion through `closure` and `interior`.
  have h₁ :
      interior (closure (A : Set X)) ⊆ interior (closure B) :=
    interior_closure_mono (A := A) (B := B) hAB
  -- Second, use that the interior of any set is contained in the set itself.
  exact h₁.trans (interior_subset : interior (closure B) ⊆ closure B)