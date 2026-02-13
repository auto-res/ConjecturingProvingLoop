

theorem closure_inter_interior_subset_closure_interiors {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ interior (B : Set X)) : Set X) ⊆
      closure (A : Set X) ∩ closure (interior (B : Set X)) := by
  intro x hx
  have hA : ((A : Set X) ∩ interior (B : Set X)) ⊆ A := by
    intro y hy
    exact hy.1
  have hxA : (x : X) ∈ closure (A : Set X) := (closure_mono hA) hx
  have hB : ((A : Set X) ∩ interior (B : Set X)) ⊆ interior (B : Set X) := by
    intro y hy
    exact hy.2
  have hxB : (x : X) ∈ closure (interior (B : Set X)) := (closure_mono hB) hx
  exact And.intro hxA hxB