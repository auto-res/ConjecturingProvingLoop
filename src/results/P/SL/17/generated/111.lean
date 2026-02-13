

theorem Topology.interior_closure_inter_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    have h_subset : closure (A ∩ B) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
    have h_int : interior (closure (A ∩ B)) ⊆ interior (closure A) :=
      interior_mono h_subset
    exact h_int hx
  have hxB : x ∈ interior (closure B) := by
    have h_subset : closure (A ∩ B) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
    have h_int : interior (closure (A ∩ B)) ⊆ interior (closure B) :=
      interior_mono h_subset
    exact h_int hx
  exact And.intro hxA hxB