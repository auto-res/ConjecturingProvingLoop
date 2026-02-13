

theorem interior_inter_closure_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((closure (A : Set X)) ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) :=
    (interior_mono
      (Set.inter_subset_left :
        ((closure (A : Set X)) ∩ closure B) ⊆ closure A)) hx
  have hxB : x ∈ interior (closure B) :=
    (interior_mono
      (Set.inter_subset_right :
        ((closure (A : Set X)) ∩ closure B) ⊆ closure B)) hx
  exact ⟨hxA, hxB⟩