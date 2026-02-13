

theorem interior_closure_inter_subset_inter_interior_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure (A ∩ B)` is contained in each of `closure A` and `closure B`
  have hA : closure (A ∩ B) ⊆ closure A := closure_mono Set.inter_subset_left
  have hB : closure (A ∩ B) ⊆ closure B := closure_mono Set.inter_subset_right
  -- Taking interiors preserves these inclusions
  have hA_int : interior (closure (A ∩ B)) ⊆ interior (closure A) := interior_mono hA
  have hB_int : interior (closure (A ∩ B)) ⊆ interior (closure B) := interior_mono hB
  -- Apply the inclusions to the given point `x`
  have hxA : x ∈ interior (closure A) := hA_int hx
  have hxB : x ∈ interior (closure B) := hB_int hx
  exact And.intro hxA hxB