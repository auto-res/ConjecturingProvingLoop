

theorem Topology.closure_interior_diff_closure_eq_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ closure A = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClInt, hxNotCl⟩
    have hxCl : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (X := X) (A := A)) hxClInt
    exact (hxNotCl hxCl).elim
  · intro hx
    cases hx