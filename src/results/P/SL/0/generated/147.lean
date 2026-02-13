

theorem closure_interior_inter_subset_intersection {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior ((A ∩ B) : Set X)) ⊆
      closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) := by
  intro x hx
  -- `A ∩ B` is contained in `A`, hence so is its interior.
  have hSubA : interior ((A ∩ B) : Set X) ⊆ interior (A : Set X) := by
    have hAB_A : (A ∩ B : Set X) ⊆ (A : Set X) := by
      intro y hy
      exact hy.1
    exact interior_mono hAB_A
  -- Symmetrically for `B`.
  have hSubB : interior ((A ∩ B) : Set X) ⊆ interior (B : Set X) := by
    have hAB_B : (A ∩ B : Set X) ⊆ (B : Set X) := by
      intro y hy
      exact hy.2
    exact interior_mono hAB_B
  -- Transfer the inclusions to closures and assemble the result.
  have hxA : x ∈ closure (interior (A : Set X)) :=
    (closure_mono hSubA) hx
  have hxB : x ∈ closure (interior (B : Set X)) :=
    (closure_mono hSubB) hx
  exact And.intro hxA hxB