

theorem Topology.interior_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : x ∈ interior (closure A) := by
    have hsubsetA : (A ∩ B : Set X) ⊆ A := by
      intro z hz; exact hz.1
    have hClosureSubA : closure (A ∩ B) ⊆ closure A := closure_mono hsubsetA
    exact (interior_mono hClosureSubA) hx
  have hB : x ∈ interior (closure B) := by
    have hsubsetB : (A ∩ B : Set X) ⊆ B := by
      intro z hz; exact hz.2
    have hClosureSubB : closure (A ∩ B) ⊆ closure B := closure_mono hsubsetB
    exact (interior_mono hClosureSubB) hx
  exact And.intro hA hB