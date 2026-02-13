

theorem closure_interior_inter_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
  have hA : interior (A ∩ B : Set X) ⊆ interior A := by
    have : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    exact interior_mono this
  have hB : interior (A ∩ B : Set X) ⊆ interior B := by
    have : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact interior_mono this
  -- Taking closures preserves these inclusions
  have hA' : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono hA
  have hB' : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono hB
  exact ⟨hA' hx, hB' hx⟩