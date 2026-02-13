

theorem interior_iInter_closure_subset {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (⋂ i, closure (A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  have hxAll : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    have hsubset : (⋂ j, closure (A j) : Set X) ⊆ closure (A i) :=
      Set.iInter_subset (fun j => closure (A j)) i
    exact (interior_mono hsubset) hx
  exact Set.mem_iInter.2 hxAll