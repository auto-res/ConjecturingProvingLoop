

theorem Topology.closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hSubA : interior (A ∩ B) ⊆ interior A := interior_mono (by
    intro z hz; exact hz.1)
  have hxA : x ∈ closure (interior A) := (closure_mono hSubA) hx
  have hSubB : interior (A ∩ B) ⊆ interior B := interior_mono (by
    intro z hz; exact hz.2)
  have hxB : x ∈ closure (interior B) := (closure_mono hSubB) hx
  exact And.intro hxA hxB