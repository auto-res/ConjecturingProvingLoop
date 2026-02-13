

theorem interior_diff_subset_closure_diff_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ closure A \ closure B := by
  intro x hx
  -- `x` lies in `closure A` by an existing lemma.
  have hxClA : x ∈ closure A :=
    interior_diff_subset_closure_left (X := X) (A := A) (B := B) hx
  -- `x` is not in `closure B`, using another established lemma.
  have hxNotClB : x ∉ closure B := by
    have h := (interior_diff_subset (X := X) (A := A) (B := B)) hx
    exact h.2
  exact And.intro hxClA hxNotClB