

theorem closure_interior_inter_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ closure (interior (closure A)) =
      closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    -- `closure (interior A)` is contained in `closure (interior (closure A))`
    have hx' :
        x ∈ closure (interior (closure A)) :=
      (closure_interior_subset_closure_interior_closure
        (X := X) (A := A)) hx
    exact And.intro hx hx'