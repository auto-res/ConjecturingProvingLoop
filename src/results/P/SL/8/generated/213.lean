

theorem interior_diff_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B) ⊆ closure A \ B := by
  intro x hx
  -- From `hx : x ∈ interior (A \ B)` we deduce `x ∈ A \ B`.
  have h_mem : x ∈ A \ B := interior_subset hx
  -- Using the existing lemma, we know `x ∈ closure A`.
  have h_cl : x ∈ closure A :=
    interior_diff_subset_closure_left (X := X) (A := A) (B := B) hx
  -- Assemble the membership in the required difference set.
  exact And.intro h_cl h_mem.2