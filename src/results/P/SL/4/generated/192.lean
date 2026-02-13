

theorem interior_closure_inter_interior_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure (interior B)) := by
  intro x hx
  -- `closure (A ∩ interior B)` is contained in `closure A`
  have hA : closure (A ∩ interior B) ⊆ closure A :=
    closure_mono Set.inter_subset_left
  -- `closure (A ∩ interior B)` is also contained in `closure (interior B)`
  have hB : closure (A ∩ interior B) ⊆ closure (interior B) := by
    have hSub : (A ∩ interior B : Set X) ⊆ interior B := by
      intro y hy
      exact hy.2
    exact closure_mono hSub
  -- Taking interiors preserves these inclusions
  have hxA : x ∈ interior (closure A) := (interior_mono hA) hx
  have hxB : x ∈ interior (closure (interior B)) := (interior_mono hB) hx
  exact And.intro hxA hxB