

theorem closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior ((A ∩ B) : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hA_sub : interior (A ∩ B : Set X) ⊆ interior A := by
    apply interior_mono
    exact Set.inter_subset_left
  have hB_sub : interior (A ∩ B : Set X) ⊆ interior B := by
    apply interior_mono
    exact Set.inter_subset_right
  have hxA : (x : X) ∈ closure (interior A) := (closure_mono hA_sub) hx
  have hxB : (x : X) ∈ closure (interior B) := (closure_mono hB_sub) hx
  exact And.intro hxA hxB