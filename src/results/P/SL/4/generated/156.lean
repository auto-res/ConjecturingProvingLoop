

theorem interior_closure_interclosure_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure A ∩ closure B` is contained in each of its factors.
  have hSubA : closure A ∩ closure B ⊆ closure A := by
    intro y hy
    exact hy.1
  have hSubB : closure A ∩ closure B ⊆ closure B := by
    intro y hy
    exact hy.2
  -- Taking interiors preserves these inclusions.
  have hIntA : interior (closure A ∩ closure B) ⊆ interior (closure A) :=
    interior_mono hSubA
  have hIntB : interior (closure A ∩ closure B) ⊆ interior (closure B) :=
    interior_mono hSubB
  -- Apply the inclusions to the given point `x`.
  exact And.intro (hIntA hx) (hIntB hx)