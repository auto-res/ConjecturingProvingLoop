

theorem Topology.interior_closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have hA : x ∈ interior (closure (interior A)) := by
    have hSubA :
        interior (closure (interior (A ∩ B))) ⊆
          interior (closure (interior A)) := by
      have hInterA : (A ∩ B : Set X) ⊆ A := by
        intro z hz
        exact hz.1
      exact
        Topology.interior_closure_interior_mono
          (X := X) (A := A ∩ B) (B := A) hInterA
    exact hSubA hx
  have hB : x ∈ interior (closure (interior B)) := by
    have hSubB :
        interior (closure (interior (A ∩ B))) ⊆
          interior (closure (interior B)) := by
      have hInterB : (A ∩ B : Set X) ⊆ B := by
        intro z hz
        exact hz.2
      exact
        Topology.interior_closure_interior_mono
          (X := X) (A := A ∩ B) (B := B) hInterB
    exact hSubB hx
  exact And.intro hA hB