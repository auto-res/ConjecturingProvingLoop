

theorem closure_interior_union_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∪ interior (closure (A : Set X)) ⊆
      closure (A : Set X) := by
  intro x hx
  cases hx with
  | inl h_closure_int =>
      have h_subset :
          closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
        closure_interior_subset_closure (A := A)
      exact h_subset h_closure_int
  | inr h_interior_cl =>
      have h : (x : X) ∈ closure (A : Set X) :=
        (interior_subset (s := closure (A : Set X))) h_interior_cl
      exact h