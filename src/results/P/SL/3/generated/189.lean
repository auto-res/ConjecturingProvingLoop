

theorem interior_closure_inter_closures_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  have hA : (x : X) ∈ interior (closure (A : Set X)) := by
    have hSubset :
        closure (A : Set X) ∩ closure (B : Set X) ⊆ closure (A : Set X) := by
      intro y hy; exact hy.1
    exact (interior_mono hSubset) hx
  have hB : (x : X) ∈ interior (closure (B : Set X)) := by
    have hSubset :
        closure (A : Set X) ∩ closure (B : Set X) ⊆ closure (B : Set X) := by
      intro y hy; exact hy.2
    exact (interior_mono hSubset) hx
  exact And.intro hA hB