

theorem closure_diff_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B : Set X) ∩ interior B = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxCl, hxInt⟩
    have h : x ∈ closure A \ interior B :=
      (closure_diff_subset (A := A) (B := B)) hxCl
    exact (h.2 hxInt).elim
  · intro hx
    cases hx