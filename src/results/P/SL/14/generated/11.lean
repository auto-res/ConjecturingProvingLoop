

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at *
  -- `A` is contained in `closure (interior (A ∪ B))`
  have hA' : (A : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hA_to_closure : (A : Set X) ⊆ closure (interior A) := hA
    have h_closure_mono : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
      have h_int_mono : interior A ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro x hx
          exact Or.inl hx)
      exact closure_mono h_int_mono
    exact Set.Subset.trans hA_to_closure h_closure_mono
  -- `B` is contained in `closure (interior (A ∪ B))`
  have hB' : (B : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hB_to_closure : (B : Set X) ⊆ closure (interior B) := hB
    have h_closure_mono : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
      have h_int_mono : interior B ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro x hx
          exact Or.inr hx)
      exact closure_mono h_int_mono
    exact Set.Subset.trans hB_to_closure h_closure_mono
  -- Hence `A ∪ B` is contained in `closure (interior (A ∪ B))`
  exact Set.union_subset hA' hB'