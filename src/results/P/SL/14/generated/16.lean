

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  -- First, upgrade the target set for `A`.
  have hA' : (A : Set X) ⊆ interior (closure (interior (A ∪ B))) := by
    -- `A` is already inside `interior (closure (interior A))`.
    have hA_to : (A : Set X) ⊆ interior (closure (interior A)) := hA
    -- `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`.
    have h_incl : interior (closure (interior A))
        ⊆ interior (closure (interior (A ∪ B))) := by
      -- Monotonicity of `closure` and `interior`.
      have h_closure_mono :
          closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have h_int_mono : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have h_subset : (A : Set X) ⊆ (A ∪ B) := by
            intro x hx
            exact Or.inl hx
          exact interior_mono h_subset
        exact closure_mono h_int_mono
      exact interior_mono h_closure_mono
    exact Set.Subset.trans hA_to h_incl
  -- Next, upgrade the target set for `B`.
  have hB' : (B : Set X) ⊆ interior (closure (interior (A ∪ B))) := by
    have hB_to : (B : Set X) ⊆ interior (closure (interior B)) := hB
    have h_incl : interior (closure (interior B))
        ⊆ interior (closure (interior (A ∪ B))) := by
      have h_closure_mono :
          closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h_int_mono : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have h_subset : (B : Set X) ⊆ (A ∪ B) := by
            intro x hx
            exact Or.inr hx
          exact interior_mono h_subset
        exact closure_mono h_int_mono
      exact interior_mono h_closure_mono
    exact Set.Subset.trans hB_to h_incl
  -- Finally, combine the two inclusions.
  exact Set.union_subset hA' hB'