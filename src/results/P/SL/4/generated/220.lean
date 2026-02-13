

theorem interior_closure_interInterior_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A ∩ interior B)) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- `interior A ∩ interior B` is contained in `interior A`
  have hSubA : (interior A ∩ interior B : Set X) ⊆ interior A := by
    intro y hy
    exact hy.1
  -- and also contained in `interior B`
  have hSubB : (interior A ∩ interior B : Set X) ⊆ interior B := by
    intro y hy
    exact hy.2
  -- Taking closures preserves these inclusions
  have hClA :
      closure (interior A ∩ interior B) ⊆ closure (interior A) :=
    closure_mono hSubA
  have hClB :
      closure (interior A ∩ interior B) ⊆ closure (interior B) :=
    closure_mono hSubB
  -- Taking interiors again preserves the inclusions
  have hIntA :
      interior (closure (interior A ∩ interior B)) ⊆
        interior (closure (interior A)) :=
    interior_mono hClA
  have hIntB :
      interior (closure (interior A ∩ interior B)) ⊆
        interior (closure (interior B)) :=
    interior_mono hClB
  -- Apply the inclusions to the given point `x`
  exact And.intro (hIntA hx) (hIntB hx)