

theorem subset_of_closure_subset_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : closure (A : Set X) ⊆ interior (B : Set X)) :
    (A : Set X) ⊆ B := by
  intro x hxA
  have hxCl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have hxInt : (x : X) ∈ interior (B : Set X) := h hxCl
  exact interior_subset hxInt