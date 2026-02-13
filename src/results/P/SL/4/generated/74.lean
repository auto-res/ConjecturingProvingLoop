

theorem interior_closure_interior_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`.
  have hA : interior (A ∩ B) ⊆ interior A :=
    interior_mono Set.inter_subset_left
  have hB : interior (A ∩ B) ⊆ interior B :=
    interior_mono Set.inter_subset_right
  -- Taking closures preserves these inclusions.
  have hA_closure : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono hA
  have hB_closure : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono hB
  -- Taking interiors again preserves the inclusions.
  have hA_int :
      interior (closure (interior (A ∩ B))) ⊆ interior (closure (interior A)) :=
    interior_mono hA_closure
  have hB_int :
      interior (closure (interior (A ∩ B))) ⊆ interior (closure (interior B)) :=
    interior_mono hB_closure
  -- Apply the inclusions to the given point `x`.
  exact And.intro (hA_int hx) (hB_int hx)